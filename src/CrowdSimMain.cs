using KeyEventArgs = System.Windows.Forms.KeyEventArgs;
using Keys = System.Windows.Forms.Keys;
using System;
using System.Collections.Generic;
using System.Drawing;
using System.Globalization;
using System.IO;
using System.Net;
using System.Runtime.InteropServices;
using System.Text;
using System.Threading;
using System.Web.Script.Serialization;
using GTA;
using GTA.Math;
using GTA.UI;
using GTA.Native;

namespace CrowdSim
{
    public class CrowdSimMain : Script
    {
        #region Constants & Configuration

        // Stage 4 Population Limits & Fair Sharing (Unlocked via XtremeTool Runtime Limit Adjuster)
        private const int MaxGroupPopulation = 5000;
        private const int MaxTotalPopulation = 10000;
        private const int DefaultGroupSize = 50;
        private const int GlobalSpawnBudgetPerTick = 6; // Fair sharing: max 2 peds created per tick across all groups

        private const string PollUrl = "http://127.0.0.1:8088/api/game/poll";
        private const string AckUrl = "http://127.0.0.1:8088/api/game/ack";
        private const string LogDirectory = @"C:\Users\Teja-Clove\GTA_crowd\logs";
        private const string LogFilePath = @"C:\Users\Teja-Clove\GTA_crowd\logs\crowdsim.log";

        #endregion

        #region State & Concurrency Fields

        private static readonly object _lock = new object();
        private readonly Queue<CommandItem> _inboundQueue = new Queue<CommandItem>();
        private readonly Queue<string> _outboundQueue = new Queue<string>();

        private readonly List<CrowdPedRecord> _crowdRegistry = new List<CrowdPedRecord>();
        private readonly Dictionary<string, CrowdGroup> _groups = new Dictionary<string, CrowdGroup>(StringComparer.OrdinalIgnoreCase);

        private readonly Random _rng = new Random();
        private bool _noclipEnabled = false;
        private bool _godModeEnabled = true;
        private bool _neverWantedEnabled = true;
        private bool _propBuilderEnabled = false;
        private int _previewPropHandle = 0;
        private string _previewPropModel = "";
        private int _builderCategoryIdx = 0;
        private int _builderItemIdx = 0;
        private float _builderHeading = 0.0f;
        private float _builderPitch = 0.0f;
        private float _builderRoll = 0.0f;
        private float _builderManualZOffset = 0.0f;
        private float _builderRotStep = 15.0f;
        private float _builderGridSnap = 0.0f; // 0 = off, 0.25, 0.5, 1.0
        private bool _builderCloneSideAxis = false;
        private int _selectedPropHandle = 0;
        private int _aimedPropHandle = 0;
        private int _lastPlacedPropHandle = 0;
        private Vector3 _builderPreviewPos = Vector3.Zero;

        private readonly List<int> _stationPropHandles = new List<int>();
        private readonly List<int> _propUndoStack = new List<int>();
        public class CustomPropData
        {
            public int Handle;
            public string Model;
            public float X;
            public float Y;
            public float Z;
            public float Heading;
            public float Pitch;
            public float Roll;
            public string Zone;
            public float Width;
            public float Length;
            public float Height;
        }
        private readonly Dictionary<int, CustomPropData> _customProps = new Dictionary<int, CustomPropData>();
        private readonly Thread _networkThread;
        private volatile bool _isRunning = true;
        private bool _isInitialized = false;
        private DateTime _lastTickHeartbeat = DateTime.MinValue;
        private long _groupCounter = 0;
        private int _spawningRoundRobinIndex = 0;

        // Thread-safe cached player telemetry
        private Vector3 _cachedPlayerPos = Vector3.Zero;
        private float _cachedPlayerHeading = 0f;
        private int _cachedPlayerHandle = -1;
        private bool _cachedPlayerValid = false;
        private DateTime _lastPlayerUpdateUtc = DateTime.MinValue;

        // Stage 4 Experiment State & Config
        private class ExperimentConfig
        {
            public string State { get; set; } // "STOPPED", "RUNNING", "PAUSED"
            public string Name { get; set; }
            public string AreaType { get; set; } // "RECTANGLE", "CIRCLE"
            public float CenterX { get; set; }
            public float CenterY { get; set; }
            public float CenterZ { get; set; }
            public float Width { get; set; }
            public float Height { get; set; }
            public float Radius { get; set; }
            public bool VehicleCleanup { get; set; }
            public bool DespawnCheckpointEnabled { get; set; }
            public Vector3? DespawnCheckpoint { get; set; }
            public float DespawnRadius { get; set; }
            public bool ContinuousStream { get; set; }
            public int ExitedCount { get; set; }
            public float GridResolution { get; set; }
            public bool AllowOutsideRouting { get; set; }
        }

        private ExperimentConfig _experiment = new ExperimentConfig
        {
            State = "STOPPED",
            Name = "Experiment_1",
            AreaType = "RECTANGLE",
            CenterX = 0f,
            CenterY = 0f,
            CenterZ = 0f,
            Width = 150f,
            Height = 150f,
            Radius = 80f,
            VehicleCleanup = false,
            GridResolution = 10f,
            AllowOutsideRouting = false
        };

        private class HeatmapCell
        {
            public int Col { get; set; }
            public int Row { get; set; }
            public float X { get; set; }
            public float Y { get; set; }
            public int Count { get; set; }
            public Dictionary<string, int> GroupCounts { get; set; }
        }

        private readonly List<HeatmapCell> _currentHeatmapCells = new List<HeatmapCell>();
        private DateTime _lastHeatmapUpdate = DateTime.MinValue;

        #endregion

        #region Script Initialization & Lifecycle

        public CrowdSimMain()
        {
            Tick += OnTick;
            KeyDown += OnKeyDown;
            Aborted += OnAborted;

            Log("Script constructor called, starting background communication worker (Stage 4)...");

            _networkThread = new Thread(NetworkWorkerLoop);
            _networkThread.IsBackground = true;
            _networkThread.Name = "CrowdSimNetworkWorker";
            _networkThread.Start();
        }

        private void OnAborted(object sender, EventArgs e)
        {
            _isRunning = false;
            SetNoclip(false);
            DeletePreviewProp();

            try
            {
                // Release streaming models and clean up groups
                foreach (CrowdGroup grp in _groups.Values)
                {
                    ReleaseGroupModels(grp);
                    grp.PendingCount = 0;
                    grp.Status = "CANCELLED";
                }

                // Delete all CrowdSim-managed pedestrians on script unload
                int deleted = 0;
                lock (_lock)
                {
                    for (int i = 0; i < _crowdRegistry.Count; i++)
                    {
                        try
                        {
                            Ped p = Entity.FromHandle(_crowdRegistry[i].Handle) as Ped;
                            if (p != null && p.Exists())
                            {
                                p.Delete();
                                deleted++;
                            }
                        }
                        catch { }
                    }
                    _crowdRegistry.Clear();
                    _groups.Clear();
                    _currentHeatmapCells.Clear();
                }

                Log(string.Format("SUCCESS: [CrowdSim] Script unloaded. Cleaned up {0} entities.", deleted));
            }
            catch (Exception ex)
            {
                Log(string.Format("ERROR: Exception during OnAborted cleanup: {0}", ex.Message));
            }
        }

        #endregion

        #region Game Thread OnTick

        private void OnTick(object sender, EventArgs e)
        {
            try
            {
                // 0. Continuously update cached player position, God Mode, Never Wanted & Fly Mode on game thread
                try
                {
                    Player curPlayer = Game.Player;
                    if (curPlayer != null && curPlayer.Character != null && curPlayer.Character.Exists())
                    {
                        Ped playerPed = curPlayer.Character;
                        Vector3 curPos = playerPed.Position;
                        float curHead = playerPed.Heading;
                        int curHandle = playerPed.Handle;
                        lock (_lock)
                        {
                            _cachedPlayerPos = curPos;
                            _cachedPlayerHeading = curHead;
                            _cachedPlayerHandle = curHandle;
                            _cachedPlayerValid = true;
                            _lastPlayerUpdateUtc = DateTime.UtcNow;
                        }

                        // God Mode Enforcement (Immune to bullets, fire, explosions, collision, falls, ragdoll, dismount)
                        if (_godModeEnabled)
                        {
                            Function.Call(Hash.SET_ENTITY_INVINCIBLE, playerPed.Handle, true);
                            Function.Call(Hash.SET_PLAYER_INVINCIBLE, curPlayer.Handle, true);
                            Function.Call(Hash.SET_ENTITY_CAN_BE_DAMAGED, playerPed.Handle, false);
                            Function.Call(Hash.SET_ENTITY_PROOFS, playerPed.Handle, true, true, true, true, true, true, true, true);
                            Function.Call(Hash.SET_PED_CAN_RAGDOLL, playerPed.Handle, false);
                            Function.Call(Hash.SET_PED_CAN_RAGDOLL_FROM_PLAYER_IMPACT, playerPed.Handle, false);
                            Function.Call(Hash.SET_PED_CAN_BE_KNOCKED_OFF_BIKE, playerPed.Handle, 1);
                            Function.Call(Hash.SET_PED_CAN_BE_SHOT_IN_VEHICLE, playerPed.Handle, false);

                            if (playerPed.Health < playerPed.MaxHealth)
                            {
                                playerPed.Health = playerPed.MaxHealth;
                            }
                            if (curPlayer.Character.Armor < 100)
                            {
                                curPlayer.Character.Armor = 100;
                            }

                            if (playerPed.IsInVehicle() && playerPed.CurrentVehicle != null && playerPed.CurrentVehicle.Exists())
                            {
                                Vehicle veh = playerPed.CurrentVehicle;
                                Function.Call(Hash.SET_ENTITY_INVINCIBLE, veh.Handle, true);
                                Function.Call(Hash.SET_ENTITY_CAN_BE_DAMAGED, veh.Handle, false);
                                Function.Call(Hash.SET_VEHICLE_CAN_BE_VISIBLY_DAMAGED, veh.Handle, false);
                                Function.Call(Hash.SET_VEHICLE_TYRES_CAN_BURST, veh.Handle, false);
                                Function.Call(Hash.SET_VEHICLE_WHEELS_CAN_BREAK, veh.Handle, false);
                                if (veh.Health < veh.MaxHealth) veh.Health = veh.MaxHealth;
                                if (veh.EngineHealth < 1000f) veh.EngineHealth = 1000f;
                            }
                        }

                        // Never Wanted / Police Response Suppression
                        if (_neverWantedEnabled)
                        {
                            if (curPlayer.WantedLevel > 0)
                            {
                                curPlayer.WantedLevel = 0;
                            }
                            Function.Call(Hash.CLEAR_PLAYER_WANTED_LEVEL, curPlayer.Handle);
                            Function.Call(Hash.SET_MAX_WANTED_LEVEL, 0);
                            Function.Call(Hash.SET_POLICE_IGNORE_PLAYER, curPlayer.Handle, true);
                            Function.Call(Hash.SET_DISPATCH_COPS_FOR_PLAYER, curPlayer.Handle, false);
                            Function.Call(Hash.SET_CREATE_RANDOM_COPS, false);
                            Function.Call(Hash.SET_CREATE_RANDOM_COPS_NOT_ON_SCENARIOS, false);
                            Function.Call(Hash.SET_CREATE_RANDOM_COPS_ON_SCENARIOS, false);

                            for (int d = 1; d <= 15; d++)
                            {
                                Function.Call(Hash.ENABLE_DISPATCH_SERVICE, d, false);
                            }
                        }

                        // Fly Mode / Freecam Movement
                        if (_noclipEnabled)
                        {
                            HandleNoclip(playerPed);
                        }

                        // In-Game 3D Mod-Menu Prop Builder (F9)
                        if (_propBuilderEnabled)
                        {
                            TickPropBuilder();
                        }
                    }
                }
                catch { }
                // 1. Rate-limited OnTick Heartbeat (every 2 seconds) and Registry Pruning
                if ((DateTime.UtcNow - _lastTickHeartbeat).TotalSeconds >= 2.0)
                {
                    _lastTickHeartbeat = DateTime.UtcNow;

                    // Prune dead or despawned peds from global registry
                    lock (_lock)
                    {
                        for (int i = _crowdRegistry.Count - 1; i >= 0; i--)
                        {
                            Ped p = Entity.FromHandle(_crowdRegistry[i].Handle) as Ped;
                            if (p == null || !p.Exists() || p.IsDead)
                            {
                                int prunedHandle = _crowdRegistry[i].Handle;
                                string prunedGrpId = _crowdRegistry[i].GroupId;
                                _crowdRegistry.RemoveAt(i);
                                Log(string.Format("WARN: Managed entity {0} in group '{1}' disappeared or died (Exists: {2}, Dead: {3}). Pruned from registry.",
                                    prunedHandle, prunedGrpId, p != null && p.Exists(), p != null && p.IsDead));
                            }
                        }
                    }

                    // Prune dead handles from group member lists
                    foreach (CrowdGroup grp in _groups.Values)
                    {
                        for (int i = grp.MemberHandles.Count - 1; i >= 0; i--)
                        {
                            Ped p = Entity.FromHandle(grp.MemberHandles[i]) as Ped;
                            if (p == null || !p.Exists() || p.IsDead)
                            {
                                grp.MemberHandles.RemoveAt(i);
                            }
                        }

                        // Re-elect leader if leader died or was pruned
                        if (grp.Behavior == "FOLLOW_LEADER" && grp.LeaderHandle != 0)
                        {
                            Ped leader = Entity.FromHandle(grp.LeaderHandle) as Ped;
                            if (leader == null || !leader.Exists() || leader.IsDead)
                            {
                                ElectNewLeader(grp);
                            }
                        }

                        // Mark active group COMPLETED only if it reached target AND all members departed
                        if (grp.Status == "ACTIVE" && grp.PendingCount == 0 && grp.MemberHandles.Count == 0 && grp.SpawnedCount >= grp.TargetCount && grp.TargetCount > 0)
                        {
                            grp.Status = "COMPLETED";
                            Log(string.Format("INFO: Group {0} ('{1}') marked COMPLETED (all {2} members departed).", grp.GroupId, grp.Name, grp.SpawnedCount));
                        }
                    }

                    int inCount = 0;
                    int outCount = 0;
                    lock (_lock)
                    {
                        inCount = _inboundQueue.Count;
                        outCount = _outboundQueue.Count;
                    }

                    int activeGroups = 0;
                    int spawningGroups = 0;
                    foreach (CrowdGroup grp in _groups.Values)
                    {
                        if (grp.Status == "ACTIVE") activeGroups++;
                        else if (grp.Status == "SPAWNING") spawningGroups++;
                    }

                    Log(string.Format("DIAG: Heartbeat (Initialized: {0}, InQueue: {1}, OutQueue: {2}, ManagedPeds: {3}, ActiveGroups: {4}, SpawningGroups: {5}, ExpState: {6})",
                        _isInitialized, inCount, outCount, _crowdRegistry.Count, activeGroups, spawningGroups, _experiment.State));

                    foreach (CrowdGroup gSummary in _groups.Values)
                    {
                        Log(string.Format("GROUP_SUMMARY: [{0} / '{1}'] Status: {2}, Alive: {3}, Target: {4}, Spawned: {5}, Pending: {6}, Failed: {7}, Rate: {8}/s",
                            gSummary.GroupId, gSummary.Name, gSummary.Status, gSummary.MemberHandles.Count, gSummary.TargetCount, gSummary.SpawnedCount, gSummary.PendingCount, gSummary.FailedCount, gSummary.SpawnRate));
                    }
                }

                // 2. Baseline Initialization (runs once when player character exists)
                if (!_isInitialized)
                {
                    Player player = Game.Player;
                    if (player != null && player.Character != null && player.Character.Exists())
                    {
                        _isInitialized = true;
                        Vector3 playerPos = player.Character.Position;
                        _experiment.CenterX = (float)Math.Round(playerPos.X, 2);
                        _experiment.CenterY = (float)Math.Round(playerPos.Y, 2);
                        _experiment.CenterZ = (float)Math.Round(playerPos.Z, 2);

                        // Automatically purge any leftover airport jetbridges/stairs from previous session reloads
                        PurgeAirportPropsInWorld();

                        Notification.PostTicker("~g~[CrowdSim]~s~ Concrete Station Studio Loaded (F9)", true, true);
                        GTA.UI.Screen.ShowSubtitle("~b~[CrowdSim]~s~ Concrete Station Builder Ready (Press ~y~F9~s~)", 3500);
                        Log(string.Format("SUCCESS: [CrowdSim] Script loaded successfully! Player handle: {0}, Pos: ({1}, {2}, {3})",
                            player.Character.Handle, _experiment.CenterX, _experiment.CenterY, _experiment.CenterZ));
                    }
                    return;
                }

                // 3. Process Inbound Command (one command per frame to avoid frame drop)
                CommandItem command = null;
                lock (_lock)
                {
                    if (_inboundQueue.Count > 0)
                    {
                        command = _inboundQueue.Dequeue();
                    }
                }

                if (command != null)
                {
                    Log(string.Format("DIAG: OnTick dequeued command: {0} (ReqID: {1})", command.Command, command.RequestId));
                    ProcessGameCommand(command);
                }

                // ALWAYS completely suppress ambient civilian pedestrians and vehicle traffic
                // so 100% of engine entity slots belong exclusively to CrowdSim pedestrians!
                Function.Call(Hash.SET_PED_DENSITY_MULTIPLIER_THIS_FRAME, 0.0f);
                Function.Call(Hash.SET_SCENARIO_PED_DENSITY_MULTIPLIER_THIS_FRAME, 0.0f, 0.0f);
                Function.Call(Hash.SET_VEHICLE_DENSITY_MULTIPLIER_THIS_FRAME, 0.0f);
                Function.Call(Hash.SET_RANDOM_VEHICLE_DENSITY_MULTIPLIER_THIS_FRAME, 0.0f);
                Function.Call(Hash.SET_PARKED_VEHICLE_DENSITY_MULTIPLIER_THIS_FRAME, 0.0f);
                Function.Call(Hash.SET_GARBAGE_TRUCKS, false);
                Function.Call(Hash.SET_RANDOM_BOATS, false);

                if ((DateTime.UtcNow - _lastAmbientSweep).TotalSeconds >= 1.0)
                {
                    _lastAmbientSweep = DateTime.UtcNow;
                    SweepAmbientEntities();
                }

                // 4. Global Fair Round-Robin Spawner (max 2 peds created per tick across all groups)
                if (_experiment.State != "PAUSED")
                {
                    TickSpawningGroups();
                }

                // 5. Group Behavior & Route Controllers (throttled internally per group)
                TickGroupBehaviors();

                // 6. Stage 4 Heatmap Grid Aggregation (every 500ms)
                UpdateHeatmapGrid();
            }
            catch (Exception ex)
            {
                Log(string.Format("ERROR: Unhandled exception in OnTick: {0}", ex.ToString()));
            }
        }

        #endregion

        #region Stage 4 Experiment Boundary & Vehicle Cleanup

        private bool IsInsideExperimentArea(Vector3 pt)
        {
            if (_experiment == null) return true;
            if (_experiment.AreaType == "CIRCLE")
            {
                float dx = pt.X - _experiment.CenterX;
                float dy = pt.Y - _experiment.CenterY;
                return (dx * dx + dy * dy) <= (_experiment.Radius * _experiment.Radius);
            }
            else // RECTANGLE
            {
                float halfW = _experiment.Width / 2.0f;
                float halfH = _experiment.Height / 2.0f;
                return Math.Abs(pt.X - _experiment.CenterX) <= halfW && Math.Abs(pt.Y - _experiment.CenterY) <= halfH;
            }
        }

        private int PerformSafeVehicleCleanup(float? customCenterX = null, float? customCenterY = null, float? customRadius = null)
        {
            int cleaned = 0;
            try
            {
                Ped playerPed = (Game.Player != null) ? Game.Player.Character : null;
                Vehicle playerVeh = (playerPed != null && playerPed.Exists() && playerPed.IsInVehicle()) ? playerPed.CurrentVehicle : null;
                int playerVehHandle = (playerVeh != null && playerVeh.Exists()) ? playerVeh.Handle : 0;

                Vehicle[] allVehs = World.GetAllVehicles();
                if (allVehs == null) return 0;

                foreach (Vehicle veh in allVehs)
                {
                    if (veh == null || !veh.Exists()) continue;
                    if (playerVehHandle != 0 && veh.Handle == playerVehHandle) continue;
                    if (veh.IsPersistent) continue; // Skip mission/scripted protected vehicles

                    // Exclude vehicles occupied by player (as driver or passenger)
                    if (!veh.IsSeatFree(VehicleSeat.Driver) && veh.Driver != null && veh.Driver.Exists() && veh.Driver.IsPlayer) continue;
                    if (playerPed != null && playerPed.Exists() && playerPed.IsInVehicle())
                    {
                        Vehicle curV = playerPed.CurrentVehicle;
                        if (curV != null && curV.Handle == veh.Handle) continue;
                    }

                    Vector3 pos = veh.Position;
                    bool shouldClean = false;
                    if (customCenterX.HasValue && customCenterY.HasValue && customRadius.HasValue)
                    {
                        float dx = pos.X - customCenterX.Value;
                        float dy = pos.Y - customCenterY.Value;
                        if ((dx * dx + dy * dy) <= (customRadius.Value * customRadius.Value))
                        {
                            shouldClean = true;
                        }
                    }
                    else
                    {
                        shouldClean = IsInsideExperimentArea(pos);
                    }

                    if (shouldClean)
                    {
                        veh.Delete();
                        cleaned++;
                    }
                }

                Log(string.Format("INFO: Safe vehicle cleanup completed. Removed {0} ambient vehicles (Center: {1},{2}, Radius: {3}).",
                    cleaned,
                    customCenterX.HasValue ? customCenterX.Value.ToString("F1", CultureInfo.InvariantCulture) : "Area",
                    customCenterY.HasValue ? customCenterY.Value.ToString("F1", CultureInfo.InvariantCulture) : "Area",
                    customRadius.HasValue ? customRadius.Value.ToString("F1", CultureInfo.InvariantCulture) : "Area"));
            }
            catch (Exception ex)
            {
                Log(string.Format("WARN: Exception during ambient vehicle cleanup: {0}", ex.Message));
            }
            return cleaned;
        }

        private void UpdateHeatmapGrid()
        {
            if ((DateTime.UtcNow - _lastHeatmapUpdate).TotalMilliseconds < 500) return;
            _lastHeatmapUpdate = DateTime.UtcNow;

            float res = Math.Max(5.0f, Math.Min(50.0f, _experiment.GridResolution));
            Dictionary<string, HeatmapCell> cellMap = new Dictionary<string, HeatmapCell>();

            lock (_lock)
            {
                for (int i = 0; i < _crowdRegistry.Count; i++)
                {
                    CrowdPedRecord rec = _crowdRegistry[i];
                    Ped p = Entity.FromHandle(rec.Handle) as Ped;
                    if (p != null && p.Exists() && !p.IsDead)
                    {
                        Vector3 pos = p.Position;
                        if (IsInsideExperimentArea(pos))
                        {
                            int col = (int)Math.Floor(pos.X / res);
                            int row = (int)Math.Floor(pos.Y / res);
                            string key = col + "_" + row;

                            HeatmapCell cell;
                            if (!cellMap.TryGetValue(key, out cell))
                            {
                                cell = new HeatmapCell
                                {
                                    Col = col,
                                    Row = row,
                                    X = (float)Math.Round((col + 0.5f) * res, 2),
                                    Y = (float)Math.Round((row + 0.5f) * res, 2),
                                    Count = 0,
                                    GroupCounts = new Dictionary<string, int>(StringComparer.OrdinalIgnoreCase)
                                };
                                cellMap[key] = cell;
                            }

                            cell.Count++;
                            string grpId = rec.GroupId ?? "default";
                            if (!cell.GroupCounts.ContainsKey(grpId))
                                cell.GroupCounts[grpId] = 0;
                            cell.GroupCounts[grpId]++;
                        }
                    }
                }

                _currentHeatmapCells.Clear();
                _currentHeatmapCells.AddRange(cellMap.Values);
            }
        }

        #endregion

        #region Command Processing

        private void ProcessGameCommand(CommandItem cmd)
        {
            try
            {
                switch (cmd.Command.ToUpperInvariant())
                {
                    case "PING_GAME":
                        ProcessPingCommand(cmd);
                        break;

                    case "SPAWN_PED":
                        ProcessSpawnPedCommand(cmd);
                        break;

                    case "CLEAR_PEDS":
                        ProcessClearPedsCommand(cmd);
                        break;

                    case "CREATE_GROUP":
                        ProcessCreateGroupCommand(cmd);
                        break;

                    case "GET_GROUPS":
                        ProcessGetGroupsCommand(cmd);
                        break;

                    case "GET_GROUP_STATUS":
                        ProcessGetGroupStatusCommand(cmd);
                        break;

                    case "REMOVE_GROUP":
                        ProcessRemoveGroupCommand(cmd);
                        break;

                    case "CLEAR_ALL_GROUPS":
                        ProcessClearAllGroupsCommand(cmd);
                        break;

                    case "UPDATE_GROUP":
                        ProcessUpdateGroupCommand(cmd);
                        break;

                    case "START_GROUP":
                        ProcessStartGroupCommand(cmd);
                        break;

                    case "PAUSE_GROUP":
                        ProcessPauseGroupCommand(cmd);
                        break;

                    case "SET_GROUP_LEADER":
                        ProcessSetGroupLeaderCommand(cmd);
                        break;

                    case "SET_EXPERIMENT":
                        ProcessSetExperimentCommand(cmd);
                        break;

                    case "START_EXPERIMENT":
                        ProcessStartExperimentCommand(cmd);
                        break;

                    case "PAUSE_EXPERIMENT":
                        ProcessPauseExperimentCommand(cmd);
                        break;

                    case "RESUME_EXPERIMENT":
                        ProcessResumeExperimentCommand(cmd);
                        break;

                    case "STOP_EXPERIMENT":
                        ProcessStopExperimentCommand(cmd);
                        break;

                    case "RESET_EXPERIMENT":
                        ProcessResetExperimentCommand(cmd);
                        break;

                    case "CLEANUP_VEHICLES":
                        ProcessCleanupVehiclesCommand(cmd);
                        break;

                    case "TELEPORT_PLAYER":
                        ProcessTeleportPlayerCommand(cmd);
                        break;

                    case "TOGGLE_NOCLIP":
                        bool enableNoclip = !_noclipEnabled;
                        Dictionary<string, object> nDict = cmd.Payload as Dictionary<string, object>;
                        if (nDict != null && nDict.ContainsKey("enabled"))
                        {
                            bool.TryParse(Convert.ToString(nDict["enabled"]), out enableNoclip);
                        }
                        SetNoclip(enableNoclip);
                        Dictionary<string, object> nAck = new Dictionary<string, object>();
                        nAck["request_id"] = cmd.RequestId;
                        nAck["command"] = cmd.Command;
                        nAck["status"] = "ACK";
                        nAck["noclip_enabled"] = _noclipEnabled;
                        EnqueueAck(nAck);
                        break;

                    case "TOGGLE_PROP_BUILDER":
                        bool enableBuilder = !_propBuilderEnabled;
                        Dictionary<string, object> pbDict = cmd.Payload as Dictionary<string, object>;
                        if (pbDict != null && pbDict.ContainsKey("enabled"))
                        {
                            bool.TryParse(Convert.ToString(pbDict["enabled"]), out enableBuilder);
                        }
                        SetPropBuilderMode(enableBuilder);
                        Dictionary<string, object> pbAck = new Dictionary<string, object>();
                        pbAck["request_id"] = cmd.RequestId;
                        pbAck["command"] = cmd.Command;
                        pbAck["status"] = "ACK";
                        pbAck["prop_builder_enabled"] = _propBuilderEnabled;
                        pbAck["noclip_enabled"] = _noclipEnabled;
                        EnqueueAck(pbAck);
                        break;

                    case "SAVE_STATION_LAYOUT_DIRECT":
                        {
                            Dictionary<string, object> svDict = cmd.Payload as Dictionary<string, object>;
                            string layoutName = "Custom_Station_Entity";
                            if (svDict != null && svDict.ContainsKey("name"))
                            {
                                string rawName = Convert.ToString(svDict["name"]).Trim();
                                if (!string.IsNullOrEmpty(rawName)) layoutName = rawName;
                            }
                            int savedCount = SaveStationLayoutDirect(layoutName);
                            Dictionary<string, object> svAck = new Dictionary<string, object>();
                            svAck["request_id"] = cmd.RequestId;
                            svAck["command"] = cmd.Command;
                            svAck["status"] = "ACK";
                            svAck["saved_name"] = layoutName;
                            svAck["count"] = savedCount;
                            svAck["props"] = GetSerializedCustomPropsList();
                            EnqueueAck(svAck);
                            break;
                        }

                    case "CLONE_PROP":
                        {
                            Dictionary<string, object> clpDict = cmd.Payload as Dictionary<string, object>;
                            int srcId = _selectedPropHandle != 0 ? _selectedPropHandle : _lastPlacedPropHandle;
                            bool sideAxis = _builderCloneSideAxis;
                            float sign = 1.0f;
                            if (clpDict != null)
                            {
                                if (clpDict.ContainsKey("id")) int.TryParse(Convert.ToString(clpDict["id"]), out srcId);
                                if (clpDict.ContainsKey("side_axis")) bool.TryParse(Convert.ToString(clpDict["side_axis"]), out sideAxis);
                                if (clpDict.ContainsKey("direction")) float.TryParse(Convert.ToString(clpDict["direction"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out sign);
                            }
                            CustomPropData cloned = ClonePropById(srcId, sideAxis, sign);
                            Dictionary<string, object> clpAck = new Dictionary<string, object>();
                            clpAck["request_id"] = cmd.RequestId;
                            clpAck["command"] = cmd.Command;
                            if (cloned != null)
                            {
                                clpAck["status"] = "ACK";
                                clpAck["prop"] = SerializeCustomProp(cloned);
                            }
                            else
                            {
                                clpAck["status"] = "ERROR";
                                clpAck["message"] = "Could not clone prop ID " + srcId;
                            }
                            EnqueueAck(clpAck);
                            break;
                        }

                    case "BUILD_CUSTOM_STATION":
                        float sbx = -1340.0f, sby = -3040.0f, sbz = 13.95f;
                        Dictionary<string, object> bDict = cmd.Payload as Dictionary<string, object>;
                        if (bDict != null)
                        {
                            if (bDict.ContainsKey("x")) float.TryParse(Convert.ToString(bDict["x"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out sbx);
                            if (bDict.ContainsKey("y")) float.TryParse(Convert.ToString(bDict["y"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out sby);
                            if (bDict.ContainsKey("z")) float.TryParse(Convert.ToString(bDict["z"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out sbz);
                        }
                        int propsBuilt = BuildCustomStation(sbx, sby, sbz);
                        Dictionary<string, object> bAck = new Dictionary<string, object>();
                        bAck["request_id"] = cmd.RequestId;
                        bAck["command"] = cmd.Command;
                        bAck["status"] = "ACK";
                        bAck["props_built"] = propsBuilt;
                        bAck["station_center"] = new Dictionary<string, object> { { "x", sbx }, { "y", sby }, { "z", sbz } };
                        EnqueueAck(bAck);
                        break;

                    case "CLEAR_CUSTOM_STATION":
                    case "CLEAR_ALL_PROPS":
                        ClearStationProps();
                        Dictionary<string, object> cAck = new Dictionary<string, object>();
                        cAck["request_id"] = cmd.RequestId;
                        cAck["command"] = cmd.Command;
                        cAck["status"] = "ACK";
                        EnqueueAck(cAck);
                        break;

                    case "SPAWN_PROP":
                        {
                            Dictionary<string, object> sDict = cmd.Payload as Dictionary<string, object>;
                            string pModel = "prop_portacabin01";
                            string pZone = "Custom";
                            float px = 0f, py = 0f, pz = 0f, pHeading = 0f, pPitch = 0f, pRoll = 0f;
                            bool hasCoords = false;
                            bool snapSurface = false;
                            if (sDict != null)
                            {
                                if (sDict.ContainsKey("model")) pModel = Convert.ToString(sDict["model"]);
                                if (sDict.ContainsKey("zone")) pZone = Convert.ToString(sDict["zone"]);
                                if (sDict.ContainsKey("x") && sDict.ContainsKey("y") && sDict.ContainsKey("z"))
                                {
                                    float.TryParse(Convert.ToString(sDict["x"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out px);
                                    float.TryParse(Convert.ToString(sDict["y"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out py);
                                    float.TryParse(Convert.ToString(sDict["z"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out pz);
                                    hasCoords = true;
                                }
                                if (sDict.ContainsKey("heading"))
                                {
                                    float.TryParse(Convert.ToString(sDict["heading"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out pHeading);
                                }
                                if (sDict.ContainsKey("pitch"))
                                {
                                    float.TryParse(Convert.ToString(sDict["pitch"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out pPitch);
                                }
                                if (sDict.ContainsKey("roll"))
                                {
                                    float.TryParse(Convert.ToString(sDict["roll"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out pRoll);
                                }
                                if (sDict.ContainsKey("snap_surface"))
                                {
                                    bool.TryParse(Convert.ToString(sDict["snap_surface"]), out snapSurface);
                                }
                            }

                            if (!hasCoords)
                            {
                                Ped ply = Game.Player != null ? Game.Player.Character : null;
                                if (ply != null && ply.Exists())
                                {
                                    Vector3 fwd = ply.ForwardVector;
                                    Vector3 spawnPos = ply.Position + fwd * 4.0f;
                                    px = spawnPos.X;
                                    py = spawnPos.Y;
                                    pz = spawnPos.Z;
                                    pHeading = ply.Heading;
                                    snapSurface = true;
                                }
                            }

                            if (snapSurface)
                            {
                                float sZ;
                                if (TryGetPreciseSurfaceZ(px, py, pz + 3.0f, out sZ)) pz = sZ;
                            }

                            Dictionary<string, object> pAck = new Dictionary<string, object>();
                            pAck["request_id"] = cmd.RequestId;
                            pAck["command"] = cmd.Command;

                            if (pModel.StartsWith("prefab_", StringComparison.OrdinalIgnoreCase))
                            {
                                int builtCount = SpawnConcretePrefab(pModel, new Vector3(px, py, pz), pHeading, pZone);
                                if (builtCount > 0 && _lastPlacedPropHandle != 0 && _customProps.ContainsKey(_lastPlacedPropHandle))
                                {
                                    pAck["status"] = "ACK";
                                    pAck["spawned_count"] = builtCount;
                                    pAck["prop"] = SerializeCustomProp(_customProps[_lastPlacedPropHandle]);
                                    GTA.UI.Screen.ShowSubtitle(string.Format("~g~Built Concrete Prefab {0} ({1} blocks)~s~", pModel, builtCount), 2500);
                                }
                                else
                                {
                                    pAck["status"] = "ERROR";
                                    pAck["message"] = "Failed to spawn concrete prefab: " + pModel;
                                }
                                EnqueueAck(pAck);
                                break;
                            }

                            Model m = new Model(pModel);
                            if (!m.IsValid)
                            {
                                pAck["status"] = "ERROR";
                                pAck["message"] = "Invalid model name: " + pModel;
                            }
                            else
                            {
                                m.Request(1500);
                                if (!m.IsLoaded)
                                {
                                    pAck["status"] = "ERROR";
                                    pAck["message"] = "Model failed to load: " + pModel;
                                }
                                else
                                {
                                    Prop p = CreateConfiguredStationProp(m, pModel, new Vector3(px, py, pz), new Vector3(pPitch, pRoll, pHeading), pZone);
                                    if (p != null && p.Exists())
                                    {
                                        CustomPropData cpd = _customProps[p.Handle];
                                        _lastPlacedPropHandle = p.Handle;
                                        _selectedPropHandle = p.Handle;
                                        pAck["status"] = "ACK";
                                        pAck["prop"] = SerializeCustomProp(cpd);
                                        GTA.UI.Screen.ShowSubtitle("~g~Spawned: " + pModel + " [ID: " + p.Handle + "]~s~", 2000);
                                    }
                                    else
                                    {
                                        pAck["status"] = "ERROR";
                                        pAck["message"] = "World.CreateProp returned null";
                                    }
                                }
                            }
                            EnqueueAck(pAck);
                            break;
                        }

                    case "UPDATE_PROP":
                        {
                            Dictionary<string, object> uDict = cmd.Payload as Dictionary<string, object>;
                            int propId = 0;
                            float ux = 0f, uy = 0f, uz = 0f, uHead = 0f, uPitch = 0f, uRoll = 0f;
                            bool hasPos = false;
                            bool hasPitchRoll = false;
                            bool snap = false;
                            if (uDict != null)
                            {
                                if (uDict.ContainsKey("id")) int.TryParse(Convert.ToString(uDict["id"]), out propId);
                                if (uDict.ContainsKey("x")) { float.TryParse(Convert.ToString(uDict["x"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out ux); hasPos = true; }
                                if (uDict.ContainsKey("y")) { float.TryParse(Convert.ToString(uDict["y"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out uy); hasPos = true; }
                                if (uDict.ContainsKey("z")) { float.TryParse(Convert.ToString(uDict["z"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out uz); hasPos = true; }
                                if (uDict.ContainsKey("heading")) { float.TryParse(Convert.ToString(uDict["heading"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out uHead); }
                                if (uDict.ContainsKey("pitch")) { float.TryParse(Convert.ToString(uDict["pitch"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out uPitch); hasPitchRoll = true; }
                                if (uDict.ContainsKey("roll")) { float.TryParse(Convert.ToString(uDict["roll"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out uRoll); hasPitchRoll = true; }
                                if (uDict.ContainsKey("snap_surface")) { bool.TryParse(Convert.ToString(uDict["snap_surface"]), out snap); }
                            }

                            Dictionary<string, object> uAck = new Dictionary<string, object>();
                            uAck["request_id"] = cmd.RequestId;
                            uAck["command"] = cmd.Command;

                            Entity ent = Entity.FromHandle(propId);
                            if (ent != null && ent.Exists())
                            {
                                if (snap)
                                {
                                    float sZ;
                                    if (TryGetPreciseSurfaceZ(ux, uy, uz + 3.0f, out sZ)) uz = sZ;
                                }
                                if (hasPos)
                                {
                                    Function.Call(Hash.SET_ENTITY_COORDS_NO_OFFSET, ent.Handle, ux, uy, uz, false, false, false);
                                }
                                if (hasPitchRoll)
                                {
                                    ent.Rotation = new Vector3(uPitch, uRoll, uHead);
                                }
                                else
                                {
                                    ent.Heading = uHead;
                                }
                                ent.IsPositionFrozen = true;

                                CustomPropData updatedCpd = null;
                                lock (_lock)
                                {
                                    if (!_customProps.ContainsKey(propId))
                                    {
                                        float pw, pl, ph;
                                        GetModelSize(ent.Model, out pw, out pl, out ph);
                                        _customProps[propId] = new CustomPropData
                                        {
                                            Handle = propId,
                                            Model = ResolvePropModelName(ent.Model.Hash),
                                            X = ent.Position.X,
                                            Y = ent.Position.Y,
                                            Z = ent.Position.Z,
                                            Heading = ent.Heading,
                                            Pitch = ent.Rotation.X,
                                            Roll = ent.Rotation.Y,
                                            Zone = "Menyoo",
                                            Width = pw,
                                            Length = pl,
                                            Height = ph
                                        };
                                    }
                                    if (_customProps.ContainsKey(propId))
                                    {
                                        _customProps[propId].X = ux;
                                        _customProps[propId].Y = uy;
                                        _customProps[propId].Z = uz;
                                        _customProps[propId].Heading = uHead;
                                        if (hasPitchRoll)
                                        {
                                            _customProps[propId].Pitch = uPitch;
                                            _customProps[propId].Roll = uRoll;
                                        }
                                        updatedCpd = _customProps[propId];
                                    }
                                }
                                _selectedPropHandle = propId;
                                uAck["status"] = "ACK";
                                uAck["prop"] = updatedCpd != null ? SerializeCustomProp(updatedCpd) : new Dictionary<string, object> {
                                    { "id", propId },
                                    { "x", ux },
                                    { "y", uy },
                                    { "z", uz },
                                    { "heading", uHead }
                                };
                            }
                            else
                            {
                                uAck["status"] = "ERROR";
                                uAck["message"] = "Prop with ID " + propId + " not found";
                            }
                            EnqueueAck(uAck);
                            break;
                        }

                    case "DELETE_PROP":
                        {
                            Dictionary<string, object> dDict = cmd.Payload as Dictionary<string, object>;
                            int delId = 0;
                            if (dDict != null && dDict.ContainsKey("id")) int.TryParse(Convert.ToString(dDict["id"]), out delId);

                            Dictionary<string, object> dAck = new Dictionary<string, object>();
                            dAck["request_id"] = cmd.RequestId;
                            dAck["command"] = cmd.Command;

                            string delModel = "Prop";
                            lock (_lock)
                            {
                                if (_customProps.ContainsKey(delId)) delModel = _customProps[delId].Model;
                            }
                            ForceDeletePropEntity(delId);
                            dAck["status"] = "ACK";
                            dAck["deleted_id"] = delId;
                            dAck["deleted_model"] = delModel;
                            dAck["props"] = GetSerializedCustomPropsList();
                            GTA.UI.Screen.ShowSubtitle("~r~Deleted " + delModel + " [ID: " + delId + "]~s~", 1800);
                            EnqueueAck(dAck);
                            break;
                        }

                    case "UNDO_PROP":
                        {
                            Dictionary<string, object> unAck = new Dictionary<string, object>();
                            unAck["request_id"] = cmd.RequestId;
                            unAck["command"] = cmd.Command;

                            int undoneId;
                            string undoneModel;
                            if (UndoLastProp(out undoneId, out undoneModel))
                            {
                                unAck["status"] = "ACK";
                                unAck["deleted_id"] = undoneId;
                                unAck["deleted_model"] = undoneModel;
                                unAck["props"] = GetSerializedCustomPropsList();
                            }
                            else
                            {
                                unAck["status"] = "ERROR";
                                unAck["message"] = "No placed props left to undo.";
                                unAck["props"] = GetSerializedCustomPropsList();
                            }
                            EnqueueAck(unAck);
                            break;
                        }

                    case "DELETE_NEAREST_PROP":
                        {
                            Dictionary<string, object> dnDict = cmd.Payload as Dictionary<string, object>;
                            float maxRad = 60.0f;
                            if (dnDict != null && dnDict.ContainsKey("radius"))
                            {
                                float.TryParse(Convert.ToString(dnDict["radius"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out maxRad);
                            }

                            Dictionary<string, object> dnAck = new Dictionary<string, object>();
                            dnAck["request_id"] = cmd.RequestId;
                            dnAck["command"] = cmd.Command;

                            int nearId;
                            string nearModel;
                            float nearDist;
                            if (DeleteNearestProp(maxRad, out nearId, out nearModel, out nearDist))
                            {
                                dnAck["status"] = "ACK";
                                dnAck["deleted_id"] = nearId;
                                dnAck["deleted_model"] = nearModel;
                                dnAck["distance"] = Math.Round(nearDist, 2);
                                dnAck["props"] = GetSerializedCustomPropsList();
                            }
                            else
                            {
                                dnAck["status"] = "ERROR";
                                dnAck["message"] = "No prop found within " + maxRad.ToString("F0") + "m of player.";
                                dnAck["props"] = GetSerializedCustomPropsList();
                            }
                            EnqueueAck(dnAck);
                            break;
                        }

                    case "GET_ALL_PROPS":
                        {
                            SyncWorldPropsWithManager();
                            Dictionary<string, object> aAck = new Dictionary<string, object>();
                            aAck["request_id"] = cmd.RequestId;
                            aAck["command"] = cmd.Command;
                            aAck["status"] = "ACK";
                            aAck["prop_builder_enabled"] = _propBuilderEnabled;
                            aAck["selected_prop_id"] = _selectedPropHandle;
                            aAck["props"] = GetSerializedCustomPropsList();
                            EnqueueAck(aAck);
                            break;
                        }

                    case "BATCH_SPAWN_PROPS":
                        {
                            Dictionary<string, object> batDict = cmd.Payload as Dictionary<string, object>;
                            bool clearFirst = true;
                            bool spawnAtPlayer = false;
                            float offsetDist = 10.0f;
                            var rawProps = batDict != null && batDict.ContainsKey("props") ? batDict["props"] as System.Collections.ArrayList : null;
                            if (batDict != null && batDict.ContainsKey("clear_first"))
                            {
                                bool.TryParse(Convert.ToString(batDict["clear_first"]), out clearFirst);
                            }
                            if (batDict != null && batDict.ContainsKey("spawn_at_player"))
                            {
                                bool.TryParse(Convert.ToString(batDict["spawn_at_player"]), out spawnAtPlayer);
                            }
                            if (batDict != null && batDict.ContainsKey("offset_distance"))
                            {
                                float.TryParse(Convert.ToString(batDict["offset_distance"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out offsetDist);
                            }
                            if (clearFirst)
                            {
                                ClearStationProps();
                            }

                            int bCount = 0;
                            var resultList = new List<Dictionary<string, object>>();

                            if (rawProps != null && rawProps.Count > 0)
                            {
                                float shiftX = 0f, shiftY = 0f, shiftZ = 0f;
                                if (spawnAtPlayer && Game.Player != null && Game.Player.Character != null && Game.Player.Character.Exists())
                                {
                                    Ped ply = Game.Player.Character;
                                    Vector3 targetAnchor = ply.Position + ply.ForwardVector * offsetDist;
                                    float groundZ;
                                    if (TryGetPreciseSurfaceZ(targetAnchor.X, targetAnchor.Y, targetAnchor.Z + 5.0f, out groundZ))
                                    {
                                        targetAnchor.Z = groundZ;
                                    }

                                    float sumX = 0f, sumY = 0f, minZ = float.MaxValue;
                                    int validPts = 0;
                                    foreach (object item in rawProps)
                                    {
                                        Dictionary<string, object> pItem = item as Dictionary<string, object>;
                                        if (pItem == null) continue;
                                        float ix = 0f, iy = 0f, iz = 0f;
                                        if (pItem.ContainsKey("x")) float.TryParse(Convert.ToString(pItem["x"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out ix);
                                        if (pItem.ContainsKey("y")) float.TryParse(Convert.ToString(pItem["y"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out iy);
                                        if (pItem.ContainsKey("z")) float.TryParse(Convert.ToString(pItem["z"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out iz);
                                        sumX += ix;
                                        sumY += iy;
                                        if (iz < minZ) minZ = iz;
                                        validPts++;
                                    }
                                    if (validPts > 0)
                                    {
                                        float avgX = sumX / validPts;
                                        float avgY = sumY / validPts;
                                        shiftX = targetAnchor.X - avgX;
                                        shiftY = targetAnchor.Y - avgY;
                                        shiftZ = targetAnchor.Z - (minZ < float.MaxValue ? minZ : 0f);
                                    }
                                }

                                HashSet<string> uniqueModels = new HashSet<string>(StringComparer.OrdinalIgnoreCase);
                                foreach (object item in rawProps)
                                {
                                    Dictionary<string, object> pItem = item as Dictionary<string, object>;
                                    if (pItem != null && pItem.ContainsKey("model"))
                                    {
                                        uniqueModels.Add(Convert.ToString(pItem["model"]));
                                    }
                                }

                                foreach (string mName in uniqueModels)
                                {
                                    try
                                    {
                                        Model m = new Model(mName);
                                        if (m.IsValid) m.Request(1000);
                                    }
                                    catch { }
                                }

                                foreach (object item in rawProps)
                                {
                                    Dictionary<string, object> pItem = item as Dictionary<string, object>;
                                    if (pItem == null) continue;
                                    string pModel = Convert.ToString(pItem["model"]);
                                    string pZone = pItem.ContainsKey("zone") ? Convert.ToString(pItem["zone"]) : "Station";
                                    float px = 0f, py = 0f, pz = 0f, pHeading = 0f, pPitch = 0f, pRoll = 0f;
                                    if (pItem.ContainsKey("x")) float.TryParse(Convert.ToString(pItem["x"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out px);
                                    if (pItem.ContainsKey("y")) float.TryParse(Convert.ToString(pItem["y"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out py);
                                    if (pItem.ContainsKey("z")) float.TryParse(Convert.ToString(pItem["z"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out pz);
                                    if (pItem.ContainsKey("heading")) float.TryParse(Convert.ToString(pItem["heading"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out pHeading);
                                    if (pItem.ContainsKey("pitch")) float.TryParse(Convert.ToString(pItem["pitch"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out pPitch);
                                    if (pItem.ContainsKey("roll")) float.TryParse(Convert.ToString(pItem["roll"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out pRoll);

                                    px += shiftX;
                                    py += shiftY;
                                    pz += shiftZ;

                                    try
                                    {
                                        Model m = new Model(pModel);
                                        if (m.IsLoaded || m.Request(250))
                                        {
                                            Prop p = CreateConfiguredStationProp(m, pModel, new Vector3(px, py, pz), new Vector3(pPitch, pRoll, pHeading), pZone);
                                            if (p != null && p.Exists())
                                            {
                                                resultList.Add(SerializeCustomProp(_customProps[p.Handle]));
                                                bCount++;
                                            }
                                        }
                                    }
                                    catch { }
                                }
                            }

                            Dictionary<string, object> batAck = new Dictionary<string, object>();
                            batAck["request_id"] = cmd.RequestId;
                            batAck["command"] = cmd.Command;
                            batAck["status"] = "ACK";
                            batAck["spawned_count"] = bCount;
                            batAck["spawned_at_player"] = spawnAtPlayer;
                            batAck["props"] = GetSerializedCustomPropsList();
                            GTA.UI.Screen.ShowSubtitle(spawnAtPlayer
                                ? string.Format("~g~Spawned Composite Entity ({0} props) at Player!~s~", bCount)
                                : string.Format("~g~Batch Spawned {0} Props!~s~", bCount), 2500);
                            EnqueueAck(batAck);
                            break;
                        }

                    case "TOGGLE_GOD_MODE":
                        bool enableGod = !_godModeEnabled;
                        Dictionary<string, object> godDict = cmd.Payload as Dictionary<string, object>;
                        if (godDict != null && godDict.ContainsKey("enabled"))
                        {
                            bool.TryParse(Convert.ToString(godDict["enabled"]), out enableGod);
                        }
                        _godModeEnabled = enableGod;
                        Player curP = Game.Player;
                        if (curP != null && curP.Character != null && curP.Character.Exists())
                        {
                            Ped pp = curP.Character;
                            if (!_godModeEnabled)
                            {
                                Function.Call(Hash.SET_ENTITY_INVINCIBLE, pp.Handle, false);
                                Function.Call(Hash.SET_PLAYER_INVINCIBLE, curP.Handle, false);
                                Function.Call(Hash.SET_ENTITY_CAN_BE_DAMAGED, pp.Handle, true);
                                Function.Call(Hash.SET_ENTITY_PROOFS, pp.Handle, false, false, false, false, false, false, false, false);
                                Function.Call(Hash.SET_PED_CAN_RAGDOLL, pp.Handle, true);
                                Function.Call(Hash.SET_PED_CAN_RAGDOLL_FROM_PLAYER_IMPACT, pp.Handle, true);
                            }
                        }
                        GTA.UI.Screen.ShowSubtitle(_godModeEnabled ? "~g~God Mode: ON (Invincible)~s~" : "~y~God Mode: OFF~s~", 2500);
                        Dictionary<string, object> gAck = new Dictionary<string, object>();
                        gAck["request_id"] = cmd.RequestId;
                        gAck["command"] = cmd.Command;
                        gAck["status"] = "ACK";
                        gAck["god_mode_enabled"] = _godModeEnabled;
                        EnqueueAck(gAck);
                        break;

                    case "CLEAR_WANTED_LEVEL":
                        Player cp = Game.Player;
                        if (cp != null)
                        {
                            cp.WantedLevel = 0;
                            Function.Call(Hash.CLEAR_PLAYER_WANTED_LEVEL, cp.Handle);
                            Function.Call(Hash.SET_MAX_WANTED_LEVEL, 0);
                            Function.Call(Hash.SET_POLICE_IGNORE_PLAYER, cp.Handle, true);
                            Function.Call(Hash.SET_DISPATCH_COPS_FOR_PLAYER, cp.Handle, false);
                            Function.Call(Hash.SET_CREATE_RANDOM_COPS, false);
                            for (int d = 1; d <= 15; d++)
                            {
                                Function.Call(Hash.ENABLE_DISPATCH_SERVICE, d, false);
                            }
                        }
                        GTA.UI.Screen.ShowSubtitle("~g~Wanted Level Cleared & Police Suppressed~s~", 2500);
                        Dictionary<string, object> clAck = new Dictionary<string, object>();
                        clAck["request_id"] = cmd.RequestId;
                        clAck["command"] = cmd.Command;
                        clAck["status"] = "ACK";
                        clAck["wanted_level"] = 0;
                        EnqueueAck(clAck);
                        break;

                    case "TOGGLE_NEVER_WANTED":
                        bool enableNever = !_neverWantedEnabled;
                        Dictionary<string, object> nwDict = cmd.Payload as Dictionary<string, object>;
                        if (nwDict != null && nwDict.ContainsKey("enabled"))
                        {
                            bool.TryParse(Convert.ToString(nwDict["enabled"]), out enableNever);
                        }
                        _neverWantedEnabled = enableNever;
                        Player nPlayer = Game.Player;
                        if (nPlayer != null)
                        {
                            if (_neverWantedEnabled)
                            {
                                nPlayer.WantedLevel = 0;
                                Function.Call(Hash.CLEAR_PLAYER_WANTED_LEVEL, nPlayer.Handle);
                                Function.Call(Hash.SET_MAX_WANTED_LEVEL, 0);
                                Function.Call(Hash.SET_POLICE_IGNORE_PLAYER, nPlayer.Handle, true);
                                Function.Call(Hash.SET_DISPATCH_COPS_FOR_PLAYER, nPlayer.Handle, false);
                                Function.Call(Hash.SET_CREATE_RANDOM_COPS, false);
                                for (int d = 1; d <= 15; d++)
                                {
                                    Function.Call(Hash.ENABLE_DISPATCH_SERVICE, d, false);
                                }
                            }
                            else
                            {
                                Function.Call(Hash.SET_MAX_WANTED_LEVEL, 5);
                                Function.Call(Hash.SET_POLICE_IGNORE_PLAYER, nPlayer.Handle, false);
                                Function.Call(Hash.SET_DISPATCH_COPS_FOR_PLAYER, nPlayer.Handle, true);
                                Function.Call(Hash.SET_CREATE_RANDOM_COPS, true);
                                for (int d = 1; d <= 15; d++)
                                {
                                    Function.Call(Hash.ENABLE_DISPATCH_SERVICE, d, true);
                                }
                            }
                        }
                        GTA.UI.Screen.ShowSubtitle(_neverWantedEnabled ? "~g~Never Wanted: ON (0 Stars Locked)~s~" : "~y~Never Wanted: OFF~s~", 2500);
                        Dictionary<string, object> nwAck = new Dictionary<string, object>();
                        nwAck["request_id"] = cmd.RequestId;
                        nwAck["command"] = cmd.Command;
                        nwAck["status"] = "ACK";
                        nwAck["never_wanted_enabled"] = _neverWantedEnabled;
                        EnqueueAck(nwAck);
                        break;

                    case "GET_TELEMETRY":
                        ProcessGetTelemetryCommand(cmd);
                        break;

                    default:
                        SendErrorAck(cmd, string.Format("Unknown command: '{0}'", cmd.Command));
                        break;
                }
            }
            catch (Exception ex)
            {
                Log(string.Format("ERROR: Command execution threw: {0}", ex.Message));
                SendErrorAck(cmd, "Unhandled exception: " + ex.Message);
            }
        }

                private void ProcessTeleportPlayerCommand(CommandItem cmd)
        {
            try
            {
                Dictionary<string, object> payload = cmd.Payload as Dictionary<string, object>;
                if (payload == null || !payload.ContainsKey("x") || !payload.ContainsKey("y"))
                {
                    SendErrorAck(cmd, "Payload missing 'x' or 'y' coordinates");
                    return;
                }

                float x = Convert.ToSingle(payload["x"], CultureInfo.InvariantCulture);
                float y = Convert.ToSingle(payload["y"], CultureInfo.InvariantCulture);
                float? explicitZ = null;
                if (payload.ContainsKey("z") && payload["z"] != null)
                {
                    float parsedZ;
                    if (float.TryParse(Convert.ToString(payload["z"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out parsedZ))
                    {
                        explicitZ = parsedZ;
                    }
                }

                Ped player = Game.Player.Character;
                if (player == null || !player.Exists())
                {
                    SendErrorAck(cmd, "Player ped is not active in GTA V");
                    return;
                }

                Entity targetEntity = (player.IsInVehicle() && player.CurrentVehicle != null)
                    ? (Entity)player.CurrentVehicle
                    : (Entity)player;

                // 1. FREEZE ENTITY IMMEDIATELY to prevent falling/ragdoll while streaming collision
                targetEntity.IsPositionFrozen = true;
                targetEntity.Velocity = Vector3.Zero;

                // 2. Pre-position entity to focus engine streaming cell
                float startZ = explicitZ.HasValue ? explicitZ.Value : 50.0f;
                targetEntity.Position = new Vector3(x, y, startZ);
                Function.Call(Hash.SET_FOCUS_POS_AND_VEL, x, y, startZ, 0f, 0f, 0f);

                // Request high-priority collision streaming around destination
                Function.Call(Hash.REQUEST_COLLISION_AT_COORD, x, y, startZ);
                Function.Call(Hash.NEW_LOAD_SCENE_START_SPHERE, x, y, startZ, 60.0f, 0);

                // 3. Active probe loop: wait while frozen until ground or prop surface is confirmed loaded
                float resolvedSurfaceZ = -999.0f;
                DateTime deadline = DateTime.UtcNow.AddSeconds(2.0); // max 2s streaming window

                while (DateTime.UtcNow < deadline)
                {
                    Function.Call(Hash.REQUEST_COLLISION_AT_COORD, x, y, startZ);
                    Function.Call(Hash.LOAD_ALL_OBJECTS_NOW);

                    float foundZ;
                    if (TryGetPreciseSurfaceZ(x, y, explicitZ, out foundZ))
                    {
                        resolvedSurfaceZ = foundZ;
                        break; // Solid surface confirmed ready!
                    }

                    Script.Wait(50);
                }

                Function.Call(Hash.NEW_LOAD_SCENE_STOP);

                if (resolvedSurfaceZ <= -50.0f)
                {
                    resolvedSurfaceZ = explicitZ.HasValue ? explicitZ.Value : 15.0f;
                }

                // 4. Place entity gently directly on top of the surface
                float finalZ = resolvedSurfaceZ + 0.15f;
                targetEntity.Position = new Vector3(x, y, finalZ);
                targetEntity.Velocity = Vector3.Zero;

                // 5. Unfreeze entity now that collision is 100% solid
                targetEntity.IsPositionFrozen = false;
                Function.Call(Hash.CLEAR_FOCUS);

                Log(string.Format("INFO: Teleported entity to surface at ({0:F1}, {1:F1}, {2:F1})", x, y, finalZ));

                Dictionary<string, object> ackData = new Dictionary<string, object>();
                ackData["request_id"] = cmd.RequestId;
                ackData["command"] = cmd.Command;
                ackData["status"] = "ACK";
                ackData["game_time"] = Game.GameTime;
                ackData["timestamp_utc"] = DateTime.UtcNow.ToString("o");
                Dictionary<string, object> posDict = new Dictionary<string, object>();
                posDict["x"] = Math.Round(x, 1);
                posDict["y"] = Math.Round(y, 1);
                posDict["z"] = Math.Round(finalZ, 1);
                ackData["teleported_to"] = posDict;

                EnqueueAck(ackData);
            }
            catch (Exception ex)
            {
                Log(string.Format("ERROR: Teleport failed: {0}", ex.Message));
                SendErrorAck(cmd, "Teleport exception: " + ex.Message);
            }
        }

        
        #region God Mode, Fly Mode & Custom Station Builder

        private class BuilderCatalogCategory
        {
            public string Name;
            public string ZoneTag;
            public List<Tuple<string, string>> Items; // (ModelName, DisplayLabel)
        }

        private int _builderTextureVariation = 2; // Menyoo _SET_OBJECT_TEXTURE_VARIATION (concrete/grey default)
        private string _sampledCustomModelName = null;
        private Vector3 _previewModelDims = new Vector3(2f, 2f, 2f);

        private readonly List<BuilderCatalogCategory> _builderCatalog = new List<BuilderCatalogCategory>
        {
            new BuilderCatalogCategory
            {
                Name = "1. Stations of SA & Sandy Shores (Custom)",
                ZoneTag = "Custom_Station",
                Items = new List<Tuple<string, string>>
                {
                    Tuple.Create("prop_walkway1", "SOSA Concrete Foot-Overbridge w/ Stairs & Arches"),
                    Tuple.Create("prop_trainstation2", "SOSA Full Railway Platform w/ Curved Canopy"),
                    Tuple.Create("prop_trainstation1", "SOSA Full Train Station Platform Variant 1"),
                    Tuple.Create("prop_trainstation3", "SOSA Full Train Station Platform Variant 3"),
                    Tuple.Create("prop_traincrossing1", "SOSA Railway Track Crossing & Connector"),
                    Tuple.Create("prop_fib_wallfrag01", "Sandy Shores Concrete Platform Floor Slab"),
                    Tuple.Create("prop_test_elevator", "Sandy Shores Overbridge Elevator Shaft"),
                    Tuple.Create("prop_rf_conc_pillar", "Sandy Shores Heavy Concrete Bridge Pillar"),
                    Tuple.Create("port_xr_stairs_01", "Sandy Shores Full Station Staircase"),
                    Tuple.Create("prop_train_ticket_02", "Official Train Ticket Machine")
                }
            },
            new BuilderCatalogCategory
            {
                Name = "2. Full-Size Overbridges & Decks (FOB)",
                ZoneTag = "FOB_Bridge",
                Items = new List<Tuple<string, string>>
                {
                    Tuple.Create("prop_gate_bridge_ld", "Full-Size Overpass Bridge Span"),
                    Tuple.Create("stt_prop_stunt_track_dwshort", "Full-Size Elevated Bridge w/ Side Walls"),
                    Tuple.Create("stt_prop_stunt_track_straight", "Long Elevated Highway / Bridge Span"),
                    Tuple.Create("bkr_prop_biker_bblock_sml2", "Full-Size Monolithic Concrete Bridge Deck"),
                    Tuple.Create("stt_prop_stunt_bblock_mdm2", "Wide Flat Elevated Bridge Deck Slab"),
                    Tuple.Create("prop_container_03a", "Enclosed Walk-Through Skybridge Corridor")
                }
            },
            new BuilderCatalogCategory
            {
                Name = "2. Full-Size Platforms & Concrete Slabs",
                ZoneTag = "Platform",
                Items = new List<Tuple<string, string>>
                {
                    Tuple.Create("bkr_prop_biker_bblock_lrg1", "Full-Size Concrete Train Platform (Large)"),
                    Tuple.Create("bkr_prop_biker_bblock_mdm1", "Full-Size Concrete Train Platform (Medium)"),
                    Tuple.Create("bkr_prop_biker_bblock_sml1", "Full-Size Concrete Platform Section (Small)"),
                    Tuple.Create("bkr_prop_biker_bblock_xl1", "Extra-Large Concrete Station Platform"),
                    Tuple.Create("bkr_prop_biker_bblock_huge_01", "Mega Concrete Station Foundation Pad"),
                    Tuple.Create("stt_prop_stunt_bblock_lrg2", "Large Smooth Concrete Platform Slab"),
                    Tuple.Create("stt_prop_stunt_bblock_xl2", "Extra-Large Smooth Concrete Platform Slab")
                }
            },
            new BuilderCatalogCategory
            {
                Name = "3. Full-Size Staircases & Ramps",
                ZoneTag = "Stairs",
                Items = new List<Tuple<string, string>>
                {
                    Tuple.Create("hei_prop_carrier_stair_01a", "Full-Height Industrial Staircase w/ Rails"),
                    Tuple.Create("prop_byard_steps_01", "Full-Piece Pedestrian Stairway w/ Rails"),
                    Tuple.Create("prop_steps_big_01", "Wide Solid Concrete Station Steps"),
                    Tuple.Create("bkr_prop_biker_bblock_hump_01", "Full-Width Concrete Walkable Ramp"),
                    Tuple.Create("stt_prop_stunt_wideramp", "Wide Elevated Overbridge Access Ramp")
                }
            },
            new BuilderCatalogCategory
            {
                Name = "4. Station Buildings, Gates & Turnstiles",
                ZoneTag = "Entrance_Hall",
                Items = new List<Tuple<string, string>>
                {
                    Tuple.Create("prop_portacabin01", "Full-Size Modular Station Hall Building"),
                    Tuple.Create("hei_prop_station_gate", "Official Rail / Subway Station Gate"),
                    Tuple.Create("prop_turnstyle_01", "Commuter Single Turnstile Gate"),
                    Tuple.Create("prop_turnstyle_bars", "Multi-Turnstile Array Barrier"),
                    Tuple.Create("prop_tollbooth_1", "Station Ticket & Information Booth"),
                    Tuple.Create("prop_vend_snak_01", "Automated Ticket / Snack Kiosk"),
                    Tuple.Create("prop_vend_soda_01", "Refreshment Vending Kiosk"),
                    Tuple.Create("prop_barier_conc_05a", "Wide Concrete Perimeter Wall")
                }
            },
            new BuilderCatalogCategory
            {
                Name = "5. Simulated Market & Vendor Stalls",
                ZoneTag = "Market",
                Items = new List<Tuple<string, string>>
                {
                    Tuple.Create("prop_gazebo_01", "Market Vendor Canopy Tent (White)"),
                    Tuple.Create("prop_gazebo_02", "Market Vendor Canopy Tent (Blue)"),
                    Tuple.Create("prop_parasol_01", "Outdoor Market Stall Umbrella"),
                    Tuple.Create("prop_ven_market_table1", "Market Vendor Display Stall Table"),
                    Tuple.Create("prop_table_03", "Market Folding Merchandise Table"),
                    Tuple.Create("prop_crate_01a", "Market Goods Wooden Crate"),
                    Tuple.Create("prop_boxpile_02b", "Stacked Market Cargo Boxes"),
                    Tuple.Create("gr_prop_gr_bench_01a", "Modern Commuter Waiting Bench")
                }
            },
            new BuilderCatalogCategory
            {
                Name = "6. Outside Road & Transit Plaza",
                ZoneTag = "Road_Plaza",
                Items = new List<Tuple<string, string>>
                {
                    Tuple.Create("prop_busstop_02", "Glass Roadside Bus / Transit Shelter"),
                    Tuple.Create("prop_busstop_04", "Covered Passenger Waiting Canopy"),
                    Tuple.Create("prop_streetlight_01", "Tall Station Plaza Streetlight"),
                    Tuple.Create("prop_mp_barrier_02b", "Roadway Lane Divider Barrier"),
                    Tuple.Create("prop_traffic_01a", "Roadside Traffic Signal Pole"),
                    Tuple.Create("prop_roadcone02a", "Traffic Channeling Cone")
                }
            }
        };

        private static bool IsPassThroughPropModel(string modelName)
        {
            if (string.IsNullOrEmpty(modelName)) return false;
            string m = modelName.Trim().ToLowerInvariant();
            return m == "prop_turnstyle_01" ||
                   m == "prop_turnstyle_bars" ||
                   m == "hei_prop_station_gate" ||
                   m == "prop_fncsec_01gate" ||
                   m == "prop_gazebo_01" ||
                   m == "prop_gazebo_02" ||
                   m == "prop_parasol_01" ||
                   m == "prop_busstop_02" ||
                   m == "prop_busstop_04" ||
                   m == "prop_streetlight_01" ||
                   m == "prop_traffic_01a" ||
                   m == "prop_roadcone02a";
        }

        private static void GetModelSize(Model m, out float width, out float length, out float height)
        {
            width = 2.0f;
            length = 2.0f;
            height = 2.0f;
            try
            {
                Vector3 minDim, maxDim;
                m.GetDimensions(out minDim, out maxDim);
                width = Math.Max(0.4f, (float)Math.Round(maxDim.X - minDim.X, 2));
                length = Math.Max(0.4f, (float)Math.Round(maxDim.Y - minDim.Y, 2));
                height = Math.Max(0.4f, (float)Math.Round(maxDim.Z - minDim.Z, 2));
            }
            catch { }
        }

        private void ApplyMenyooTextureVariation(Prop p, string modelName)
        {
            if (p == null || !p.Exists()) return;
            try
            {
                // Native _SET_OBJECT_TEXTURE_VARIATION (0x971DA0055324D033): used by Menyoo Object Spooner
                // to give stunt/biker building blocks clean concrete/asphalt/industrial textures
                Function.Call((Hash)0x971DA0055324D033, p.Handle, _builderTextureVariation);
            }
            catch { }
        }

        private void ResolveBuilderPreviewModelAndRot(string catalogItemKey, out string realModelName, out Vector3 previewRot)
        {
            previewRot = new Vector3(_builderPitch, _builderRoll, _builderHeading);
            realModelName = !string.IsNullOrEmpty(_sampledCustomModelName) ? _sampledCustomModelName : catalogItemKey;
        }

        private Prop CreateConfiguredStationProp(Model m, string modelName, Vector3 pos, Vector3 rotPitchRollYaw, string zoneTag)
        {
            Prop p = World.CreateProp(m, pos, rotPitchRollYaw, dynamic: false, placeOnGround: false);
            if (p != null && p.Exists())
            {
                Function.Call(Hash.SET_ENTITY_COORDS_NO_OFFSET, p.Handle, pos.X, pos.Y, pos.Z, false, false, false);
                p.Rotation = rotPitchRollYaw;
                p.IsPositionFrozen = true;
                Function.Call(Hash.SET_ENTITY_CAN_BE_DAMAGED, p.Handle, false);

                ApplyMenyooTextureVariation(p, modelName);

                bool isRoofCanopy = !string.IsNullOrEmpty(zoneTag) &&
                                    zoneTag.IndexOf("Roof", StringComparison.OrdinalIgnoreCase) >= 0;

                if (IsPassThroughPropModel(modelName) || isRoofCanopy)
                {
                    Function.Call(Hash.SET_ENTITY_COLLISION, p.Handle, false, false);
                    p.IsCollisionEnabled = false;
                }

                float w, l, h;
                GetModelSize(m, out w, out l, out h);

                CustomPropData cpd = new CustomPropData
                {
                    Handle = p.Handle,
                    Model = modelName,
                    X = pos.X,
                    Y = pos.Y,
                    Z = pos.Z,
                    Heading = rotPitchRollYaw.Z,
                    Pitch = rotPitchRollYaw.X,
                    Roll = rotPitchRollYaw.Y,
                    Zone = string.IsNullOrEmpty(zoneTag) ? "Station" : zoneTag,
                    Width = w,
                    Length = l,
                    Height = h
                };

                lock (_lock)
                {
                    _customProps[p.Handle] = cpd;
                    if (!_stationPropHandles.Contains(p.Handle))
                    {
                        _stationPropHandles.Add(p.Handle);
                    }
                    _propUndoStack.Remove(p.Handle);
                    _propUndoStack.Add(p.Handle);
                }
            }
            return p;
        }

        private static Dictionary<int, string> _knownPropHashNames;
        private static HashSet<int> _architecturePropHashes;

        private static void EnsurePropHashTablesInitialized()
        {
            if (_knownPropHashNames != null && _architecturePropHashes != null) return;
            var map = new Dictionary<int, string>();
            var arch = new HashSet<int>();

            string[] archModels = new string[]
            {
                "prop_walkway1", "prop_trainstation1", "prop_trainstation2", "prop_trainstation3", "prop_traincrossing1",
                "prop_fib_wallfrag01", "prop_test_elevator", "prop_test_elevator_dr", "prop_rf_conc_pillar", "prop_fncres_03b",
                "prop_temp_block_blocker", "port_xr_stairs_01", "prop_train_ticket_02", "prop_game_clock_02",
                "hei_prop_station_gate", "prop_air_sechut_01",
                "bkr_prop_biker_bblock_lrg1", "bkr_prop_biker_bblock_mdm1", "bkr_prop_biker_bblock_sml1",
                "bkr_prop_biker_bblock_sml2", "bkr_prop_biker_bblock_xl1", "bkr_prop_biker_bblock_huge_01",
                "bkr_prop_biker_bblock_hump_01", "stt_prop_stunt_bblock_lrg2", "stt_prop_stunt_bblock_mdm2",
                "stt_prop_stunt_bblock_sml2", "stt_prop_stunt_bblock_xl2", "stt_prop_stunt_track_dwshort",
                "stt_prop_stunt_track_straight", "stt_prop_stunt_wideramp", "prop_gate_bridge_ld",
                "hei_prop_carrier_stair_01a", "prop_byard_steps_01", "prop_steps_big_01", "prop_portacabin01",
                "prop_container_03a", "prop_barier_conc_05a", "prop_turnstyle_01", "prop_turnstyle_bars",
                "prop_tollbooth_1"
            };
            for (int i = 0; i < archModels.Length; i++)
            {
                int h = Game.GenerateHash(archModels[i]);
                map[h] = archModels[i];
                arch.Add(h);
            }

            string[] extraModels = new string[]
            {
                "prop_vend_snak_01", "prop_vend_soda_01", "gr_prop_gr_bench_01a", "prop_streetlight_01",
                "prop_gazebo_01", "prop_gazebo_02", "prop_parasol_01", "prop_ven_market_table1",
                "prop_table_03", "prop_crate_01a", "prop_boxpile_02b", "prop_busstop_02", "prop_busstop_04",
                "prop_mp_barrier_02b", "prop_traffic_01a", "prop_roadcone02a", "prop_bench_01a", "prop_bench_06",
                "prop_bin_01a", "prop_bin_05a", "prop_sec_barier_04b", "prop_off_chair_05", "prop_table_03b_chr",
                "prop_satdish_s_04a", "prop_Snow_Light_01", "prop_WarningLight_01", "prop_rub_binbag_sd_01"
            };
            for (int i = 0; i < extraModels.Length; i++)
            {
                int h = Game.GenerateHash(extraModels[i]);
                map[h] = extraModels[i];
            }

            _knownPropHashNames = map;
            _architecturePropHashes = arch;
        }

        private static string ResolvePropModelName(int modelHash)
        {
            EnsurePropHashTablesInitialized();
            string name;
            if (_knownPropHashNames.TryGetValue(modelHash, out name))
            {
                return name;
            }
            return "0x" + modelHash.ToString("X8");
        }

        private void SyncWorldPropsWithManager()
        {
            try
            {
                EnsurePropHashTablesInitialized();
                Ped playerPed = Game.Player != null ? Game.Player.Character : null;
                Vector3 refPos = (playerPed != null && playerPed.Exists())
                    ? playerPed.Position
                    : new Vector3(_experiment.CenterX, _experiment.CenterY, _experiment.CenterZ);

                Prop[] allProps = World.GetAllProps();
                if (allProps == null) return;

                for (int i = 0; i < allProps.Length; i++)
                {
                    Prop p = allProps[i];
                    if (p == null || !p.Exists()) continue;
                    int h = p.Handle;
                    if (h == _previewPropHandle) continue;

                    lock (_lock)
                    {
                        if (_customProps.ContainsKey(h))
                        {
                            CustomPropData existing = _customProps[h];
                            existing.X = p.Position.X;
                            existing.Y = p.Position.Y;
                            existing.Z = p.Position.Z;
                            existing.Heading = p.Heading;
                            existing.Pitch = p.Rotation.X;
                            existing.Roll = p.Rotation.Y;
                            continue;
                        }
                    }

                    // Discover Menyoo-spawned props (mission entities) or custom station architecture props near player
                    if ((p.Position - refPos).Length() > 500.0f) continue;
                    if (Function.Call<bool>(Hash.IS_ENTITY_ATTACHED, h)) continue;

                    int modelHash = p.Model.Hash;
                    bool isMissionEnt = Function.Call<bool>(Hash.IS_ENTITY_A_MISSION_ENTITY, h);
                    bool isArchProp = _architecturePropHashes.Contains(modelHash);

                    if (isMissionEnt || isArchProp)
                    {
                        float pw, pl, ph;
                        GetModelSize(p.Model, out pw, out pl, out ph);
                        string resolvedModel = ResolvePropModelName(modelHash);

                        CustomPropData cpd = new CustomPropData
                        {
                            Handle = h,
                            Model = resolvedModel,
                            X = p.Position.X,
                            Y = p.Position.Y,
                            Z = p.Position.Z,
                            Heading = p.Heading,
                            Pitch = p.Rotation.X,
                            Roll = p.Rotation.Y,
                            Zone = "Menyoo",
                            Width = pw,
                            Length = pl,
                            Height = ph
                        };

                        lock (_lock)
                        {
                            _customProps[h] = cpd;
                            if (!_stationPropHandles.Contains(h)) _stationPropHandles.Add(h);
                            if (!_propUndoStack.Contains(h)) _propUndoStack.Add(h);
                            _lastPlacedPropHandle = h;
                        }
                    }
                }
            }
            catch { }
        }

        private bool ForceDeletePropEntity(int handle)
        {
            if (handle == 0) return false;
            bool deleted = false;
            try
            {
                Entity ent = Entity.FromHandle(handle);
                if (ent != null && ent.Exists())
                {
                    Function.Call(Hash.SET_ENTITY_AS_MISSION_ENTITY, ent.Handle, true, true);
                    Function.Call(Hash.DETACH_ENTITY, ent.Handle, true, true);
                    ent.IsPersistent = true;
                    ent.Delete();
                    if (ent.Exists())
                    {
                        Function.Call(Hash.SET_ENTITY_COORDS_NO_OFFSET, ent.Handle, 0f, 0f, -1000f, false, false, false);
                        Function.Call(Hash.SET_ENTITY_VISIBLE, ent.Handle, false, false);
                        Function.Call(Hash.SET_ENTITY_COLLISION, ent.Handle, false, false);
                        ent.MarkAsNoLongerNeeded();
                    }
                    deleted = true;
                }
            }
            catch { }

            lock (_lock)
            {
                if (_customProps.ContainsKey(handle))
                {
                    _customProps.Remove(handle);
                    deleted = true;
                }
                _stationPropHandles.Remove(handle);
                _propUndoStack.Remove(handle);
                if (_lastPlacedPropHandle == handle)
                {
                    _lastPlacedPropHandle = _propUndoStack.Count > 0 ? _propUndoStack[_propUndoStack.Count - 1] : 0;
                }
            }
            if (_selectedPropHandle == handle) _selectedPropHandle = 0;
            if (_aimedPropHandle == handle) _aimedPropHandle = 0;
            return deleted;
        }

        private bool UndoLastProp(out int undoneId, out string undoneModel)
        {
            undoneId = 0;
            undoneModel = "";
            SyncWorldPropsWithManager();

            int candidateHandle = 0;
            lock (_lock)
            {
                while (_propUndoStack.Count > 0)
                {
                    int top = _propUndoStack[_propUndoStack.Count - 1];
                    _propUndoStack.RemoveAt(_propUndoStack.Count - 1);
                    Entity e = Entity.FromHandle(top);
                    if (e != null && e.Exists())
                    {
                        candidateHandle = top;
                        if (_customProps.ContainsKey(top)) undoneModel = _customProps[top].Model;
                        else undoneModel = ResolvePropModelName(e.Model.Hash);
                        break;
                    }
                    else
                    {
                        _customProps.Remove(top);
                        _stationPropHandles.Remove(top);
                    }
                }

                if (candidateHandle == 0 && _customProps.Count > 0)
                {
                    int maxHandle = 0;
                    foreach (var kvp in _customProps)
                    {
                        Entity e = Entity.FromHandle(kvp.Key);
                        if (e != null && e.Exists() && kvp.Key > maxHandle)
                        {
                            maxHandle = kvp.Key;
                            undoneModel = kvp.Value.Model;
                        }
                    }
                    candidateHandle = maxHandle;
                }
            }

            if (candidateHandle == 0)
            {
                GTA.UI.Screen.ShowSubtitle("~y~[Undo Prop] No placed props left to undo.~s~", 2000);
                return false;
            }

            undoneId = candidateHandle;
            ForceDeletePropEntity(candidateHandle);
            GTA.UI.Screen.ShowSubtitle(string.Format("~o~[Undo Prop]~s~ Removed ~y~{0}~s~ [ID: {1}] ({2} left)", undoneModel, undoneId, _customProps.Count), 2200);
            return true;
        }

        private bool DeleteNearestProp(float maxRadius, out int deletedId, out string deletedModel, out float distance)
        {
            deletedId = 0;
            deletedModel = "";
            distance = 0f;
            SyncWorldPropsWithManager();

            Ped playerPed = Game.Player != null ? Game.Player.Character : null;
            if (playerPed == null || !playerPed.Exists()) return false;
            Vector3 pPos = playerPed.Position;

            int bestHandle = 0;
            float bestDist = maxRadius;
            string bestModel = "";

            lock (_lock)
            {
                foreach (var kvp in _customProps)
                {
                    Entity e = Entity.FromHandle(kvp.Key);
                    if (e != null && e.Exists())
                    {
                        float d = (e.Position - pPos).Length();
                        if (d < bestDist)
                        {
                            bestDist = d;
                            bestHandle = kvp.Key;
                            bestModel = kvp.Value.Model;
                        }
                    }
                }
            }

            if (bestHandle == 0)
            {
                return false;
            }

            deletedId = bestHandle;
            deletedModel = bestModel;
            distance = bestDist;
            ForceDeletePropEntity(bestHandle);
            GTA.UI.Screen.ShowSubtitle(string.Format("~r~[Deleted Nearest Prop]~s~ {0} [ID: {1}] ({2:F1}m away)", deletedModel, deletedId, distance), 2200);
            return true;
        }

        private Dictionary<string, object> SerializeCustomProp(CustomPropData cpd)
        {
            return new Dictionary<string, object>
            {
                { "id", cpd.Handle },
                { "model", cpd.Model },
                { "x", Math.Round(cpd.X, 2) },
                { "y", Math.Round(cpd.Y, 2) },
                { "z", Math.Round(cpd.Z, 2) },
                { "heading", Math.Round(cpd.Heading, 1) },
                { "pitch", Math.Round(cpd.Pitch, 1) },
                { "roll", Math.Round(cpd.Roll, 1) },
                { "zone", cpd.Zone ?? "Station" },
                { "width", Math.Round(cpd.Width > 0 ? cpd.Width : 2.0f, 2) },
                { "length", Math.Round(cpd.Length > 0 ? cpd.Length : 2.0f, 2) },
                { "height", Math.Round(cpd.Height > 0 ? cpd.Height : 2.0f, 2) }
            };
        }

        private List<Dictionary<string, object>> GetSerializedCustomPropsList()
        {
            var propList = new List<Dictionary<string, object>>();
            lock (_lock)
            {
                List<int> toRemove = new List<int>();
                foreach (var kvp in _customProps)
                {
                    Entity ent = Entity.FromHandle(kvp.Key);
                    if (ent != null && ent.Exists())
                    {
                        kvp.Value.X = ent.Position.X;
                        kvp.Value.Y = ent.Position.Y;
                        kvp.Value.Z = ent.Position.Z;
                        kvp.Value.Heading = ent.Heading;
                        propList.Add(SerializeCustomProp(kvp.Value));
                    }
                    else
                    {
                        toRemove.Add(kvp.Key);
                    }
                }
                foreach (int remId in toRemove)
                {
                    _customProps.Remove(remId);
                    _stationPropHandles.Remove(remId);
                }
            }
            return propList;
        }

        private void SetPropBuilderMode(bool enabled)
        {
            _propBuilderEnabled = enabled;
            if (_propBuilderEnabled)
            {
                if (!_noclipEnabled)
                {
                    SetNoclip(true);
                }
                _selectedPropHandle = 0;
                GTA.UI.Screen.ShowSubtitle("~b~[3D Prop Studio ON]~s~ Arrows: Browse | Click/Enter: Place | Q/E: Rotate | C: Clone Edge | F10: Save", 4000);
            }
            else
            {
                DeletePreviewProp();
                _selectedPropHandle = 0;
                GTA.UI.Screen.ShowSubtitle("~y~[3D Prop Studio OFF]~s~", 2000);
            }
        }

        private void DeletePreviewProp()
        {
            if (_previewPropHandle != 0)
            {
                try
                {
                    Entity prev = Entity.FromHandle(_previewPropHandle);
                    if (prev != null && prev.Exists())
                    {
                        prev.Delete();
                    }
                }
                catch { }
                _previewPropHandle = 0;
                _previewPropModel = "";
            }
        }

        private CustomPropData ClonePropById(int sourceHandle, bool alongSideAxis, float directionSign)
        {
            CustomPropData src = null;
            lock (_lock)
            {
                if (sourceHandle != 0 && _customProps.ContainsKey(sourceHandle))
                {
                    src = _customProps[sourceHandle];
                }
            }
            if (src == null) return null;

            Entity srcEnt = Entity.FromHandle(src.Handle);
            if (srcEnt == null || !srcEnt.Exists()) return null;

            Model m = new Model(src.Model);
            if (!m.IsValid || (!m.IsLoaded && !m.Request(1000))) return null;

            float w, l, h;
            GetModelSize(m, out w, out l, out h);

            // Offset along the prop's local X (width) or Y (length) axis for seamless edge-to-edge tiling
            float stepDist = alongSideAxis ? l : w;
            Vector3 localOffset = alongSideAxis
                ? new Vector3(0f, stepDist * directionSign, 0f)
                : new Vector3(stepDist * directionSign, 0f, 0f);

            Vector3 newPos = srcEnt.GetOffsetPosition(localOffset);
            Vector3 rot = new Vector3(src.Pitch, src.Roll, src.Heading);

            Prop clonedProp = CreateConfiguredStationProp(m, src.Model, newPos, rot, src.Zone);
            if (clonedProp != null && clonedProp.Exists())
            {
                _lastPlacedPropHandle = clonedProp.Handle;
                if (_selectedPropHandle != 0) _selectedPropHandle = clonedProp.Handle;
                GTA.UI.Screen.ShowSubtitle(string.Format("~g~Edge-Cloned {0}~s~ [ID: {1}]", src.Model, clonedProp.Handle), 1800);
                return _customProps[clonedProp.Handle];
            }
            return null;
        }

        private int SaveStationLayoutDirect(string layoutName)
        {
            try
            {
                // 1. Sync any Menyoo-placed props in the world so everything currently placed is captured
                SyncWorldPropsWithManager();

                // 2. Lock and persist all captured entities in the GTA V world so they permanently stay in world
                lock (_lock)
                {
                    foreach (var kvp in _customProps)
                    {
                        try
                        {
                            Entity ent = Entity.FromHandle(kvp.Key);
                            if (ent != null && ent.Exists())
                            {
                                Function.Call(Hash.SET_ENTITY_AS_MISSION_ENTITY, ent.Handle, true, true);
                                ent.IsPersistent = true;
                                ent.IsPositionFrozen = true;
                                Function.Call(Hash.SET_ENTITY_CAN_BE_DAMAGED, ent.Handle, false);
                                Function.Call(Hash.SET_ENTITY_INVINCIBLE, ent.Handle, true);
                                Function.Call(Hash.SET_ENTITY_LOAD_COLLISION_FLAG, ent.Handle, true);
                                kvp.Value.X = ent.Position.X;
                                kvp.Value.Y = ent.Position.Y;
                                kvp.Value.Z = ent.Position.Z;
                                kvp.Value.Heading = ent.Heading;
                                kvp.Value.Pitch = ent.Rotation.X;
                                kvp.Value.Roll = ent.Rotation.Y;
                                if (!_stationPropHandles.Contains(ent.Handle))
                                {
                                    _stationPropHandles.Add(ent.Handle);
                                }
                            }
                        }
                        catch { }
                    }
                }

                string layoutsDir = @"C:\Users\Teja-Clove\GTA_crowd\experiments\station_layouts";
                if (!Directory.Exists(layoutsDir))
                {
                    Directory.CreateDirectory(layoutsDir);
                }

                var propsList = GetSerializedCustomPropsList();

                // Compute centroid / anchor point so the whole assembly can also be spawned as a single composite entity
                double sumX = 0, sumY = 0, minZ = double.MaxValue;
                foreach (var p in propsList)
                {
                    double px = Convert.ToDouble(p["x"], CultureInfo.InvariantCulture);
                    double py = Convert.ToDouble(p["y"], CultureInfo.InvariantCulture);
                    double pz = Convert.ToDouble(p["z"], CultureInfo.InvariantCulture);
                    sumX += px;
                    sumY += py;
                    if (pz < minZ) minZ = pz;
                }
                double centerX = propsList.Count > 0 ? Math.Round(sumX / propsList.Count, 2) : -1340.0;
                double centerY = propsList.Count > 0 ? Math.Round(sumY / propsList.Count, 2) : -3040.0;
                double baseZ = (propsList.Count > 0 && minZ < double.MaxValue) ? Math.Round(minZ, 2) : 13.95;

                foreach (var p in propsList)
                {
                    p["dx"] = Math.Round(Convert.ToDouble(p["x"], CultureInfo.InvariantCulture) - centerX, 3);
                    p["dy"] = Math.Round(Convert.ToDouble(p["y"], CultureInfo.InvariantCulture) - centerY, 3);
                    p["dz"] = Math.Round(Convert.ToDouble(p["z"], CultureInfo.InvariantCulture) - baseZ, 3);
                }

                var rootObj = new Dictionary<string, object>
                {
                    { "name", layoutName },
                    { "is_composite_entity", true },
                    { "anchor", new Dictionary<string, object> { { "x", centerX }, { "y", centerY }, { "z", baseZ } } },
                    { "saved_at_utc", DateTime.UtcNow.ToString("o") },
                    { "props", propsList }
                };

                JavaScriptSerializer serializer = new JavaScriptSerializer();
                serializer.MaxJsonLength = int.MaxValue;
                string json = serializer.Serialize(rootObj);

                string safeName = layoutName;
                foreach (char c in Path.GetInvalidFileNameChars()) safeName = safeName.Replace(c, '_');

                string filePath = Path.Combine(layoutsDir, safeName + ".json");
                File.WriteAllText(filePath, json, Encoding.UTF8);

                // Also keep Active_World_Props.json and NSRD_Station_Official.json updated
                File.WriteAllText(Path.Combine(layoutsDir, "Active_World_Props.json"), json, Encoding.UTF8);
                File.WriteAllText(Path.Combine(layoutsDir, "NSRD_Station_Official.json"), json, Encoding.UTF8);

                // 3. Export Menyoo Spooner XML so the saved composite entity can also be loaded in Menyoo (F8 -> Object Spooner -> Manage Saved Files)
                try
                {
                    StringBuilder sbXml = new StringBuilder();
                    sbXml.AppendLine("<?xml version=\"1.0\" encoding=\"ISO-8859-1\"?>");
                    sbXml.AppendLine("<SpoonerPlacements>");
                    sbXml.AppendLine("\t<Note>Saved Composite Station Entity from CrowdSim (" + safeName + ")</Note>");
                    sbXml.AppendLine(string.Format(CultureInfo.InvariantCulture, "\t<ReferenceCoords><X>{0:F4}</X><Y>{1:F4}</Y><Z>{2:F4}</Z></ReferenceCoords>", centerX, centerY, baseZ));
                    int idx = 1;
                    foreach (var p in propsList)
                    {
                        string mName = Convert.ToString(p["model"]);
                        int mHash = Function.Call<int>(Hash.GET_HASH_KEY, mName);
                        double px = Convert.ToDouble(p["x"], CultureInfo.InvariantCulture);
                        double py = Convert.ToDouble(p["y"], CultureInfo.InvariantCulture);
                        double pz = Convert.ToDouble(p["z"], CultureInfo.InvariantCulture);
                        double pHead = Convert.ToDouble(p["heading"], CultureInfo.InvariantCulture);
                        double pPitch = p.ContainsKey("pitch") ? Convert.ToDouble(p["pitch"], CultureInfo.InvariantCulture) : 0.0;
                        double pRoll = p.ContainsKey("roll") ? Convert.ToDouble(p["roll"], CultureInfo.InvariantCulture) : 0.0;

                        sbXml.AppendLine("\t<Placement>");
                        sbXml.AppendLine(string.Format(CultureInfo.InvariantCulture, "\t\t<ModelHash>0x{0:x8}</ModelHash>", mHash));
                        sbXml.AppendLine("\t\t<Type>3</Type>");
                        sbXml.AppendLine("\t\t<Dynamic>false</Dynamic>");
                        sbXml.AppendLine("\t\t<FrozenPos>true</FrozenPos>");
                        sbXml.AppendLine("\t\t<HashName>" + mName + "</HashName>");
                        sbXml.AppendLine("\t\t<InitialHandle>" + idx + "</InitialHandle>");
                        sbXml.AppendLine("\t\t<OpacityLevel>255</OpacityLevel>");
                        sbXml.AppendLine("\t\t<LodDistance>1000</LodDistance>");
                        sbXml.AppendLine("\t\t<IsVisible>true</IsVisible>");
                        sbXml.AppendLine("\t\t<MaxHealth>1000</MaxHealth>");
                        sbXml.AppendLine("\t\t<Health>1000</Health>");
                        sbXml.AppendLine("\t\t<HasGravity>false</HasGravity>");
                        sbXml.AppendLine("\t\t<IsOnFire>false</IsOnFire>");
                        sbXml.AppendLine("\t\t<IsInvincible>true</IsInvincible>");
                        sbXml.AppendLine("\t\t<IsBulletProof>true</IsBulletProof>");
                        sbXml.AppendLine("\t\t<IsCollisionProof>false</IsCollisionProof>");
                        sbXml.AppendLine("\t\t<IsExplosionProof>true</IsExplosionProof>");
                        sbXml.AppendLine("\t\t<IsFireProof>true</IsFireProof>");
                        sbXml.AppendLine("\t\t<IsMeleeProof>true</IsMeleeProof>");
                        sbXml.AppendLine("\t\t<IsOnlyDamagedByPlayer>false</IsOnlyDamagedByPlayer>");
                        sbXml.AppendLine("\t\t<PositionRotation>");
                        sbXml.AppendLine(string.Format(CultureInfo.InvariantCulture, "\t\t\t<X>{0:F4}</X>", px));
                        sbXml.AppendLine(string.Format(CultureInfo.InvariantCulture, "\t\t\t<Y>{0:F4}</Y>", py));
                        sbXml.AppendLine(string.Format(CultureInfo.InvariantCulture, "\t\t\t<Z>{0:F4}</Z>", pz));
                        sbXml.AppendLine(string.Format(CultureInfo.InvariantCulture, "\t\t\t<Pitch>{0:F4}</Pitch>", pPitch));
                        sbXml.AppendLine(string.Format(CultureInfo.InvariantCulture, "\t\t\t<Roll>{0:F4}</Roll>", pRoll));
                        sbXml.AppendLine(string.Format(CultureInfo.InvariantCulture, "\t\t\t<Yaw>{0:F4}</Yaw>", pHead));
                        sbXml.AppendLine("\t\t</PositionRotation>");
                        sbXml.AppendLine("\t\t<Attachment isAttached=\"false\" />");
                        sbXml.AppendLine("\t</Placement>");
                        idx++;
                    }
                    sbXml.AppendLine("</SpoonerPlacements>");
                    string xmlContent = sbXml.ToString();
                    File.WriteAllText(Path.Combine(layoutsDir, safeName + ".xml"), xmlContent, Encoding.UTF8);

                    string menyooSpoonerDir = @"D:\Games\Grand Theft Auto V Legacy\menyooStuff\Spooner";
                    if (Directory.Exists(menyooSpoonerDir))
                    {
                        File.WriteAllText(Path.Combine(menyooSpoonerDir, safeName + ".xml"), xmlContent, Encoding.UTF8);
                    }
                }
                catch { }

                GTA.UI.Screen.ShowSubtitle(string.Format("~g~[Saved & Locked in World]~s~ '{0}' ({1} props saved as Composite Entity)!", layoutName, propsList.Count), 3500);
                Log(string.Format("INFO: Saved composite station entity '{0}' with {1} props to {2}", layoutName, propsList.Count, filePath));
                return propsList.Count;
            }
            catch (Exception ex)
            {
                Log("ERROR: SaveStationLayoutDirect failed: " + ex.Message);
                GTA.UI.Screen.ShowSubtitle("~r~Save Layout Failed: " + ex.Message + "~s~", 3000);
                return 0;
            }
        }

        [DllImport("kernel32.dll", CharSet = CharSet.Auto)]
        private static extern IntPtr GetModuleHandle(string lpModuleName);

        private static bool IsMenyooLoaded()
        {
            try
            {
                return GetModuleHandle("Menyoo.asi") != IntPtr.Zero;
            }
            catch
            {
                return false;
            }
        }

        private void OnKeyDown(object sender, KeyEventArgs e)
        {
            if (e.KeyCode == Keys.F6)
            {
                SetNoclip(!_noclipEnabled);
                GTA.UI.Screen.ShowSubtitle(_noclipEnabled ? "~g~Fly Mode ON~s~ [W/S/A/D: Move, Space: UP, Shift: DOWN, Tab: Fast]" : "~r~Fly Mode (Noclip) OFF~s~", 2500);
            }
            else if (e.KeyCode == Keys.F7)
            {
                _godModeEnabled = !_godModeEnabled;
                GTA.UI.Screen.ShowSubtitle(_godModeEnabled ? "~g~God Mode: ON (Invincible)~s~" : "~y~God Mode: OFF~s~", 2500);
            }
            else if (e.KeyCode == Keys.F5)
            {
                _neverWantedEnabled = !_neverWantedEnabled;
                if (_neverWantedEnabled && Game.Player != null)
                {
                    Game.Player.WantedLevel = 0;
                    Function.Call(Hash.CLEAR_PLAYER_WANTED_LEVEL, Game.Player.Handle);
                }
                GTA.UI.Screen.ShowSubtitle(_neverWantedEnabled ? "~g~Never Wanted: ON (0 Stars Locked)~s~" : "~y~Never Wanted: OFF~s~", 2500);
            }
            else if (e.KeyCode == Keys.F8 || e.KeyCode == Keys.F9)
            {
                if (!IsMenyooLoaded())
                {
                    GTA.UI.Screen.ShowSubtitle("~r~Menyoo.asi is not loaded yet!~s~ ~y~Quit GTA V completely and relaunch the game ('Insert' cannot load .asi mods).~s~", 6000);
                }
            }
            else if (e.KeyCode == Keys.F11)
            {
                SetPropBuilderMode(!_propBuilderEnabled);
            }
            else if (e.KeyCode == Keys.F10)
            {
                SaveStationLayoutDirect("NSRD_Station_Official");
            }
            else if (e.Control && e.KeyCode == Keys.Z)
            {
                int uId;
                string uMod;
                UndoLastProp(out uId, out uMod);
            }
            else if (_propBuilderEnabled)
            {
                HandlePropBuilderKeyDown(e);
            }
        }

        private void HandlePropBuilderKeyDown(KeyEventArgs e)
        {
            try
            {
                BuilderCatalogCategory curCat = _builderCatalog[_builderCategoryIdx];

                // Category Navigation: Left / Right or J / L or Numpad 4 / 6
                if (e.KeyCode == Keys.Left || e.KeyCode == Keys.J || e.KeyCode == Keys.NumPad4)
                {
                    _sampledCustomModelName = null;
                    _builderCategoryIdx = (_builderCategoryIdx - 1 + _builderCatalog.Count) % _builderCatalog.Count;
                    _builderItemIdx = 0;
                }
                else if (e.KeyCode == Keys.Right || e.KeyCode == Keys.L || e.KeyCode == Keys.NumPad6)
                {
                    _sampledCustomModelName = null;
                    _builderCategoryIdx = (_builderCategoryIdx + 1) % _builderCatalog.Count;
                    _builderItemIdx = 0;
                }
                // Item Navigation: Up / Down or I / K or Numpad 8 / 2
                else if (e.KeyCode == Keys.Up || e.KeyCode == Keys.I || e.KeyCode == Keys.NumPad8)
                {
                    _sampledCustomModelName = null;
                    _builderItemIdx = (_builderItemIdx - 1 + curCat.Items.Count) % curCat.Items.Count;
                }
                else if (e.KeyCode == Keys.Down || e.KeyCode == Keys.K || e.KeyCode == Keys.NumPad2)
                {
                    _sampledCustomModelName = null;
                    _builderItemIdx = (_builderItemIdx + 1) % curCat.Items.Count;
                }
                // Cycle Menyoo Texture Variation (T)
                else if (e.KeyCode == Keys.T)
                {
                    _builderTextureVariation = (_builderTextureVariation + 1) % 12;
                    if (_previewPropHandle != 0)
                    {
                        Prop gp = Entity.FromHandle(_previewPropHandle) as Prop;
                        ApplyMenyooTextureVariation(gp, _previewPropModel);
                    }
                    if (_selectedPropHandle != 0)
                    {
                        Prop sp = Entity.FromHandle(_selectedPropHandle) as Prop;
                        ApplyMenyooTextureVariation(sp, "");
                    }
                    GTA.UI.Screen.ShowSubtitle(string.Format("~b~Menyoo Texture Variation [T]:~s~ #{0}", _builderTextureVariation), 1500);
                }
                // Sample / Eye-Dropper Any Aimed World Map Prop (M)
                else if (e.KeyCode == Keys.M)
                {
                    Vector3 camPos = GameplayCamera.Position;
                    Vector3 camDir = GameplayCamera.Direction;
                    Entity ignoreEnt = (_previewPropHandle != 0) ? Entity.FromHandle(_previewPropHandle) : (Game.Player != null ? Game.Player.Character : null);
                    RaycastResult ray = World.Raycast(camPos, camPos + camDir * 100.0f, IntersectFlags.Map | IntersectFlags.Objects, ignoreEnt);
                    if (ray.DidHit && ray.HitEntity != null && ray.HitEntity.Exists())
                    {
                        int hash = ray.HitEntity.Model.Hash;
                        _sampledCustomModelName = "0x" + hash.ToString("X8");
                        DeletePreviewProp();
                        float sw, sl, sh;
                        GetModelSize(ray.HitEntity.Model, out sw, out sl, out sh);
                        GTA.UI.Screen.ShowSubtitle(string.Format("~g~Sampled Map Object {0}~s~ (Size: {1:F1}x{2:F1}x{3:F1}m) - Click to Place!", _sampledCustomModelName, sw, sl, sh), 3000);
                    }
                    else
                    {
                        GTA.UI.Screen.ShowSubtitle("~y~Aim at any world building/bridge/stair object and press M to sample it!~s~", 2000);
                    }
                }
                // Rotate Yaw (Q / E)
                else if (e.KeyCode == Keys.Q)
                {
                    _builderHeading = (_builderHeading - _builderRotStep + 360.0f) % 360.0f;
                    ApplyTransformToSelectedPropIfEditing();
                }
                else if (e.KeyCode == Keys.E)
                {
                    _builderHeading = (_builderHeading + _builderRotStep) % 360.0f;
                    ApplyTransformToSelectedPropIfEditing();
                }
                // Cycle Rotation Step (R): 15 -> 45 -> 90 -> 5 -> 1
                else if (e.KeyCode == Keys.R)
                {
                    if (_builderRotStep == 15.0f) _builderRotStep = 45.0f;
                    else if (_builderRotStep == 45.0f) _builderRotStep = 90.0f;
                    else if (_builderRotStep == 90.0f) _builderRotStep = 5.0f;
                    else if (_builderRotStep == 5.0f) _builderRotStep = 1.0f;
                    else _builderRotStep = 15.0f;
                    GTA.UI.Screen.ShowSubtitle(string.Format("~b~Rotation Step:~s~ {0:F0} deg", _builderRotStep), 1200);
                }
                // Cycle Grid Snap (G): Off -> 0.25m -> 0.5m -> 1.0m
                else if (e.KeyCode == Keys.G)
                {
                    if (_builderGridSnap == 0.0f) _builderGridSnap = 0.25f;
                    else if (_builderGridSnap == 0.25f) _builderGridSnap = 0.5f;
                    else if (_builderGridSnap == 0.5f) _builderGridSnap = 1.0f;
                    else _builderGridSnap = 0.0f;
                    GTA.UI.Screen.ShowSubtitle(_builderGridSnap > 0f ? string.Format("~b~XY Grid Snap:~s~ {0:F2}m", _builderGridSnap) : "~y~XY Grid Snap: OFF~s~", 1200);
                }
                // Elevation Z Offset (PageUp / PageDown or U / O)
                else if (e.KeyCode == Keys.PageUp || e.KeyCode == Keys.U)
                {
                    float zStep = (_builderRotStep <= 5.0f) ? 0.05f : 0.25f;
                    if (_selectedPropHandle != 0 && _customProps.ContainsKey(_selectedPropHandle))
                    {
                        _customProps[_selectedPropHandle].Z += zStep;
                        ApplyTransformToSelectedPropIfEditing();
                    }
                    else
                    {
                        _builderManualZOffset += zStep;
                    }
                }
                else if (e.KeyCode == Keys.PageDown || e.KeyCode == Keys.O)
                {
                    float zStep = (_builderRotStep <= 5.0f) ? 0.05f : 0.25f;
                    if (_selectedPropHandle != 0 && _customProps.ContainsKey(_selectedPropHandle))
                    {
                        _customProps[_selectedPropHandle].Z -= zStep;
                        ApplyTransformToSelectedPropIfEditing();
                    }
                    else
                    {
                        _builderManualZOffset -= zStep;
                    }
                }
                // Pitch Tilt (Numpad 7 / Numpad 9)
                else if (e.KeyCode == Keys.NumPad7)
                {
                    _builderPitch = Math.Max(-60.0f, _builderPitch - 5.0f);
                    ApplyTransformToSelectedPropIfEditing();
                }
                else if (e.KeyCode == Keys.NumPad9)
                {
                    _builderPitch = Math.Min(60.0f, _builderPitch + 5.0f);
                    ApplyTransformToSelectedPropIfEditing();
                }
                // Reset manual Z / Pitch / Roll offsets (H)
                else if (e.KeyCode == Keys.H)
                {
                    _builderManualZOffset = 0.0f;
                    _builderPitch = 0.0f;
                    _builderRoll = 0.0f;
                    ApplyTransformToSelectedPropIfEditing();
                    GTA.UI.Screen.ShowSubtitle("~g~Reset Z Offset & Pitch/Roll to 0~s~", 1200);
                }
                // Toggle Clone Axis (V): Width (X) vs Length (Y)
                else if (e.KeyCode == Keys.V)
                {
                    _builderCloneSideAxis = !_builderCloneSideAxis;
                    GTA.UI.Screen.ShowSubtitle(_builderCloneSideAxis ? "~b~Clone Axis:~s~ Length (Y-Axis)" : "~b~Clone Axis:~s~ Width (X-Axis)", 1500);
                }
                // Edge-to-Edge Smart Clone (C)
                else if (e.KeyCode == Keys.C)
                {
                    int targetId = _selectedPropHandle != 0 ? _selectedPropHandle : (_aimedPropHandle != 0 ? _aimedPropHandle : _lastPlacedPropHandle);
                    ClonePropById(targetId, _builderCloneSideAxis, e.Shift ? -1.0f : 1.0f);
                }
                // Place Prop or Confirm Edit (Enter / NumPad5)
                else if (e.KeyCode == Keys.Enter || e.KeyCode == Keys.NumPad5)
                {
                    PlaceOrConfirmBuilderProp();
                }
                // Select / Grab Aimed Prop into Edit Mode (Back)
                else if (e.KeyCode == Keys.Back)
                {
                    ToggleSelectAimedProp();
                }
                // Delete Aimed / Selected Prop (Delete / X)
                else if (e.KeyCode == Keys.Delete || e.KeyCode == Keys.X)
                {
                    DeleteActiveOrAimedProp();
                }
            }
            catch (Exception ex)
            {
                Log("WARN: HandlePropBuilderKeyDown error: " + ex.Message);
            }
        }

        private void ApplyTransformToSelectedPropIfEditing()
        {
            if (_selectedPropHandle == 0) return;
            lock (_lock)
            {
                if (_customProps.ContainsKey(_selectedPropHandle))
                {
                    CustomPropData cpd = _customProps[_selectedPropHandle];
                    cpd.Heading = _builderHeading;
                    cpd.Pitch = _builderPitch;
                    cpd.Roll = _builderRoll;
                    Entity ent = Entity.FromHandle(_selectedPropHandle);
                    if (ent != null && ent.Exists())
                    {
                        Function.Call(Hash.SET_ENTITY_COORDS_NO_OFFSET, ent.Handle, cpd.X, cpd.Y, cpd.Z, false, false, false);
                        ent.Rotation = new Vector3(cpd.Pitch, cpd.Roll, cpd.Heading);
                    }
                }
            }
        }

        private void PlaceOrConfirmBuilderProp()
        {
            if (_selectedPropHandle != 0)
            {
                GTA.UI.Screen.ShowSubtitle(string.Format("~g~Locked Prop [ID: {0}] in place!~s~", _selectedPropHandle), 1500);
                _lastPlacedPropHandle = _selectedPropHandle;
                _selectedPropHandle = 0;
                return;
            }

            BuilderCatalogCategory cat = _builderCatalog[_builderCategoryIdx];
            Tuple<string, string> item = cat.Items[_builderItemIdx];
            string modelName = !string.IsNullOrEmpty(_sampledCustomModelName) ? _sampledCustomModelName : item.Item1;

            if (modelName.StartsWith("prefab_", StringComparison.OrdinalIgnoreCase))
            {
                int built = SpawnConcretePrefab(modelName, _builderPreviewPos, _builderHeading, cat.ZoneTag);
                if (built > 0)
                {
                    GTA.UI.Screen.ShowSubtitle(string.Format("~g~Built {0}~s~ ({1} full-size blocks)", item.Item2, built), 2500);
                }
                return;
            }

            Model m = ParseModelFromString(modelName);
            if (!m.IsValid || (!m.IsLoaded && !m.Request(1000)))
            {
                GTA.UI.Screen.ShowSubtitle("~r~Failed loading model: " + modelName + "~s~", 2000);
                return;
            }

            Vector3 rot = new Vector3(_builderPitch, _builderRoll, _builderHeading);
            Prop created = CreateConfiguredStationProp(m, modelName, _builderPreviewPos, rot, cat.ZoneTag);
            if (created != null && created.Exists())
            {
                _lastPlacedPropHandle = created.Handle;
                GTA.UI.Screen.ShowSubtitle(string.Format("~g~Placed {0}~s~ ({1:F1}x{2:F1}x{3:F1}m) [Press ~b~C~s~ to Edge-Clone]", modelName, _previewModelDims.X, _previewModelDims.Y, _previewModelDims.Z), 2200);
            }
        }

        private static Model ParseModelFromString(string modelNameOrHex)
        {
            if (string.IsNullOrEmpty(modelNameOrHex)) return new Model(0);
            string s = modelNameOrHex.Trim();
            if (s.StartsWith("0x", StringComparison.OrdinalIgnoreCase))
            {
                int parsedHash;
                if (int.TryParse(s.Substring(2), System.Globalization.NumberStyles.HexNumber, System.Globalization.CultureInfo.InvariantCulture, out parsedHash))
                {
                    return new Model(parsedHash);
                }
            }
            return new Model(s);
        }

        private void ToggleSelectAimedProp()
        {
            if (_selectedPropHandle != 0)
            {
                GTA.UI.Screen.ShowSubtitle("~y~Released Selected Prop (Back to Spawn Mode)~s~", 1500);
                _selectedPropHandle = 0;
                return;
            }

            if (_aimedPropHandle != 0)
            {
                lock (_lock)
                {
                    if (_customProps.ContainsKey(_aimedPropHandle))
                    {
                        CustomPropData cpd = _customProps[_aimedPropHandle];
                        _selectedPropHandle = _aimedPropHandle;
                        _builderHeading = cpd.Heading;
                        _builderPitch = cpd.Pitch;
                        _builderRoll = cpd.Roll;
                        DeletePreviewProp();
                        GTA.UI.Screen.ShowSubtitle(string.Format("~b~Grabbed Prop {0} [#{1}]~s~ (Aim to Move, Q/E Rotate, Click/Enter Lock)", cpd.Model, cpd.Handle), 2500);
                    }
                }
            }
            else
            {
                GTA.UI.Screen.ShowSubtitle("~y~Aim crosshair at an existing prop to grab/select it!~s~", 1500);
            }
        }

        private void DeleteActiveOrAimedProp()
        {
            int targetId = _selectedPropHandle != 0 ? _selectedPropHandle : (_aimedPropHandle != 0 ? _aimedPropHandle : _lastPlacedPropHandle);
            if (targetId == 0) return;

            Entity ent = Entity.FromHandle(targetId);
            if (ent != null && ent.Exists())
            {
                ent.Delete();
            }

            string delModel = "Prop";
            lock (_lock)
            {
                if (_customProps.ContainsKey(targetId))
                {
                    delModel = _customProps[targetId].Model;
                    _customProps.Remove(targetId);
                }
                _stationPropHandles.Remove(targetId);
            }

            if (_selectedPropHandle == targetId) _selectedPropHandle = 0;
            if (_aimedPropHandle == targetId) _aimedPropHandle = 0;
            if (_lastPlacedPropHandle == targetId) _lastPlacedPropHandle = 0;

            GTA.UI.Screen.ShowSubtitle(string.Format("~r~Deleted {0} [#{1}]~s~", delModel, targetId), 1500);
        }

        private void TickPropBuilder()
        {
            try
            {
                // Disable weapon wheel & attack/aim while in 3D Prop Builder so mouse clicks & scroll wheel control props
                Function.Call(Hash.DISABLE_CONTROL_ACTION, 0, (int)Control.Attack, true);
                Function.Call(Hash.DISABLE_CONTROL_ACTION, 0, (int)Control.Aim, true);
                Function.Call(Hash.DISABLE_CONTROL_ACTION, 0, (int)Control.SelectWeapon, true);
                Function.Call(Hash.DISABLE_CONTROL_ACTION, 0, (int)Control.WeaponWheelNext, true);
                Function.Call(Hash.DISABLE_CONTROL_ACTION, 0, (int)Control.WeaponWheelPrev, true);

                // Mouse Wheel Rotation
                if (Function.Call<bool>(Hash.IS_DISABLED_CONTROL_JUST_PRESSED, 0, (int)Control.WeaponWheelNext))
                {
                    _builderHeading = (_builderHeading + _builderRotStep) % 360.0f;
                    ApplyTransformToSelectedPropIfEditing();
                }
                else if (Function.Call<bool>(Hash.IS_DISABLED_CONTROL_JUST_PRESSED, 0, (int)Control.WeaponWheelPrev))
                {
                    _builderHeading = (_builderHeading - _builderRotStep + 360.0f) % 360.0f;
                    ApplyTransformToSelectedPropIfEditing();
                }

                // 1. Cast 3D Ray from GameplayCamera
                Vector3 camPos = GameplayCamera.Position;
                Vector3 camDir = GameplayCamera.Direction;
                Entity ignoreEnt = (_previewPropHandle != 0) ? Entity.FromHandle(_previewPropHandle) : (Game.Player != null ? Game.Player.Character : null);

                RaycastResult ray = World.Raycast(camPos, camPos + camDir * 75.0f, IntersectFlags.Map | IntersectFlags.Objects, ignoreEnt);
                Vector3 hitPos = ray.DidHit ? ray.HitPosition : (camPos + camDir * 14.0f);

                // Detect aimed custom prop (either direct raycast hit or closest custom prop to camera ray)
                _aimedPropHandle = 0;
                if (ray.DidHit && ray.HitEntity != null && ray.HitEntity.Exists())
                {
                    int hId = ray.HitEntity.Handle;
                    lock (_lock)
                    {
                        if (_customProps.ContainsKey(hId))
                        {
                            _aimedPropHandle = hId;
                        }
                    }
                }
                if (_aimedPropHandle == 0)
                {
                    float bestDist = 1.6f;
                    lock (_lock)
                    {
                        foreach (var kvp in _customProps)
                        {
                            Vector3 pCenter = new Vector3(kvp.Value.X, kvp.Value.Y, kvp.Value.Z + kvp.Value.Height * 0.4f);
                            Vector3 toProp = pCenter - camPos;
                            float proj = Vector3.Dot(toProp, camDir);
                            if (proj > 1.0f && proj < 60.0f)
                            {
                                Vector3 closestPt = camPos + camDir * proj;
                                float perpDist = (pCenter - closestPt).Length();
                                if (perpDist < bestDist)
                                {
                                    bestDist = perpDist;
                                    _aimedPropHandle = kvp.Key;
                                }
                            }
                        }
                    }
                }

                // Apply Grid Snap & Manual Z Offset
                float targetX = hitPos.X;
                float targetY = hitPos.Y;
                if (_builderGridSnap > 0.01f)
                {
                    targetX = (float)Math.Round(targetX / _builderGridSnap) * _builderGridSnap;
                    targetY = (float)Math.Round(targetY / _builderGridSnap) * _builderGridSnap;
                }
                float surfaceZ = hitPos.Z;
                float probedZ;
                if (TryGetPreciseSurfaceZ(targetX, targetY, hitPos.Z + 2.5f, out probedZ))
                {
                    surfaceZ = probedZ;
                }
                float targetZ = surfaceZ + _builderManualZOffset;
                _builderPreviewPos = new Vector3(targetX, targetY, targetZ);

                // 2. Update either Selected Placed Prop OR Ghost Preview Prop
                BuilderCatalogCategory curCat = _builderCatalog[_builderCategoryIdx];
                Tuple<string, string> curItem = curCat.Items[_builderItemIdx];
                string activeModelName = curItem.Item1;

                if (_selectedPropHandle != 0)
                {
                    DeletePreviewProp();
                    Entity selEnt = Entity.FromHandle(_selectedPropHandle);
                    if (selEnt != null && selEnt.Exists())
                    {
                        Function.Call(Hash.SET_ENTITY_COORDS_NO_OFFSET, selEnt.Handle, _builderPreviewPos.X, _builderPreviewPos.Y, _builderPreviewPos.Z, false, false, false);
                        selEnt.Rotation = new Vector3(_builderPitch, _builderRoll, _builderHeading);
                        lock (_lock)
                        {
                            if (_customProps.ContainsKey(_selectedPropHandle))
                            {
                                _customProps[_selectedPropHandle].X = _builderPreviewPos.X;
                                _customProps[_selectedPropHandle].Y = _builderPreviewPos.Y;
                                _customProps[_selectedPropHandle].Z = _builderPreviewPos.Z;
                                _customProps[_selectedPropHandle].Heading = _builderHeading;
                                _customProps[_selectedPropHandle].Pitch = _builderPitch;
                                _customProps[_selectedPropHandle].Roll = _builderRoll;
                            }
                        }
                        DrawEntityBoundingBox(selEnt, 245, 158, 11, 230); // Gold/Amber wireframe for grabbed prop
                    }
                    else
                    {
                        _selectedPropHandle = 0;
                    }
                }
                else
                {
                    string previewRealModel;
                    Vector3 previewRot;
                    ResolveBuilderPreviewModelAndRot(activeModelName, out previewRealModel, out previewRot);

                    // Maintain Ghost Preview Prop
                    if (_previewPropHandle == 0 || !string.Equals(_previewPropModel, previewRealModel, StringComparison.OrdinalIgnoreCase))
                    {
                        DeletePreviewProp();
                        Model m = ParseModelFromString(previewRealModel);
                        if (m.IsValid && (m.IsLoaded || m.Request(250)))
                        {
                            float pw, pl, ph;
                            GetModelSize(m, out pw, out pl, out ph);
                            _previewModelDims = new Vector3(pw, pl, ph);

                            Prop ghost = World.CreateProp(m, _builderPreviewPos, previewRot, dynamic: false, placeOnGround: false);
                            if (ghost != null && ghost.Exists())
                            {
                                ghost.IsPositionFrozen = true;
                                Function.Call(Hash.SET_ENTITY_COLLISION, ghost.Handle, false, false);
                                ghost.IsCollisionEnabled = false;
                                ApplyMenyooTextureVariation(ghost, previewRealModel);
                                ghost.Opacity = 175;
                                _previewPropHandle = ghost.Handle;
                                _previewPropModel = previewRealModel;
                            }
                        }
                    }

                    if (_previewPropHandle != 0)
                    {
                        Entity ghostEnt = Entity.FromHandle(_previewPropHandle);
                        if (ghostEnt != null && ghostEnt.Exists())
                        {
                            Function.Call(Hash.SET_ENTITY_COORDS_NO_OFFSET, ghostEnt.Handle, _builderPreviewPos.X, _builderPreviewPos.Y, _builderPreviewPos.Z, false, false, false);
                            ghostEnt.Rotation = previewRot;
                            DrawEntityBoundingBox(ghostEnt, 56, 189, 248, 220); // Cyan wireframe for ghost preview
                        }
                        else
                        {
                            _previewPropHandle = 0;
                        }
                    }

                    // Highlight Aimed Existing Prop in Green
                    if (_aimedPropHandle != 0)
                    {
                        Entity aimedEnt = Entity.FromHandle(_aimedPropHandle);
                        if (aimedEnt != null && aimedEnt.Exists())
                        {
                            DrawEntityBoundingBox(aimedEnt, 16, 185, 129, 220);
                        }
                    }
                }

                // 3. Mouse Click Actions (Left Click = Place/Lock, Right Click = Grab/Select Aimed Prop)
                if (Function.Call<bool>(Hash.IS_DISABLED_CONTROL_JUST_PRESSED, 0, (int)Control.Attack))
                {
                    PlaceOrConfirmBuilderProp();
                }
                else if (Function.Call<bool>(Hash.IS_DISABLED_CONTROL_JUST_PRESSED, 0, (int)Control.Aim))
                {
                    ToggleSelectAimedProp();
                }

                // 4. Draw Center Crosshair & Right-Side Mod Menu HUD
                DrawPropBuilderHud(curCat, curItem);
            }
            catch (Exception ex)
            {
                Log("WARN: TickPropBuilder exception: " + ex.Message);
            }
        }

        private void DrawEntityBoundingBox(Entity ent, int r, int g, int b, int a)
        {
            try
            {
                Vector3 min, max;
                ent.Model.GetDimensions(out min, out max);

                Vector3 b1 = ent.GetOffsetPosition(new Vector3(min.X, min.Y, min.Z));
                Vector3 b2 = ent.GetOffsetPosition(new Vector3(max.X, min.Y, min.Z));
                Vector3 b3 = ent.GetOffsetPosition(new Vector3(max.X, max.Y, min.Z));
                Vector3 b4 = ent.GetOffsetPosition(new Vector3(min.X, max.Y, min.Z));

                Vector3 t1 = ent.GetOffsetPosition(new Vector3(min.X, min.Y, max.Z));
                Vector3 t2 = ent.GetOffsetPosition(new Vector3(max.X, min.Y, max.Z));
                Vector3 t3 = ent.GetOffsetPosition(new Vector3(max.X, max.Y, max.Z));
                Vector3 t4 = ent.GetOffsetPosition(new Vector3(min.X, max.Y, max.Z));

                // Bottom rectangle
                Function.Call(Hash.DRAW_LINE, b1.X, b1.Y, b1.Z, b2.X, b2.Y, b2.Z, r, g, b, a);
                Function.Call(Hash.DRAW_LINE, b2.X, b2.Y, b2.Z, b3.X, b3.Y, b3.Z, r, g, b, a);
                Function.Call(Hash.DRAW_LINE, b3.X, b3.Y, b3.Z, b4.X, b4.Y, b4.Z, r, g, b, a);
                Function.Call(Hash.DRAW_LINE, b4.X, b4.Y, b4.Z, b1.X, b1.Y, b1.Z, r, g, b, a);

                // Top rectangle
                Function.Call(Hash.DRAW_LINE, t1.X, t1.Y, t1.Z, t2.X, t2.Y, t2.Z, r, g, b, a);
                Function.Call(Hash.DRAW_LINE, t2.X, t2.Y, t2.Z, t3.X, t3.Y, t3.Z, r, g, b, a);
                Function.Call(Hash.DRAW_LINE, t3.X, t3.Y, t3.Z, t4.X, t4.Y, t4.Z, r, g, b, a);
                Function.Call(Hash.DRAW_LINE, t4.X, t4.Y, t4.Z, t1.X, t1.Y, t1.Z, r, g, b, a);

                // Vertical pillars
                Function.Call(Hash.DRAW_LINE, b1.X, b1.Y, b1.Z, t1.X, t1.Y, t1.Z, r, g, b, a);
                Function.Call(Hash.DRAW_LINE, b2.X, b2.Y, b2.Z, t2.X, t2.Y, t2.Z, r, g, b, a);
                Function.Call(Hash.DRAW_LINE, b3.X, b3.Y, b3.Z, t3.X, t3.Y, t3.Z, r, g, b, a);
                Function.Call(Hash.DRAW_LINE, b4.X, b4.Y, b4.Z, t4.X, t4.Y, t4.Z, r, g, b, a);

                // Heading arrow from center
                Vector3 center = ent.Position;
                Vector3 fwdTip = ent.GetOffsetPosition(new Vector3(0f, max.Y + 1.2f, 0.2f));
                Function.Call(Hash.DRAW_LINE, center.X, center.Y, center.Z + 0.2f, fwdTip.X, fwdTip.Y, fwdTip.Z, 255, 215, 0, 255);
            }
            catch { }
        }

        private void DrawHudText(string text, float x, float y, float scale, int r, int g, int b, int a, bool centered = false)
        {
            Function.Call(Hash.SET_TEXT_FONT, 0);
            Function.Call(Hash.SET_TEXT_SCALE, scale, scale);
            Function.Call(Hash.SET_TEXT_COLOUR, r, g, b, a);
            Function.Call(Hash.SET_TEXT_CENTRE, centered);
            Function.Call(Hash.SET_TEXT_OUTLINE);
            Function.Call(Hash.BEGIN_TEXT_COMMAND_DISPLAY_TEXT, "STRING");
            Function.Call(Hash.ADD_TEXT_COMPONENT_SUBSTRING_PLAYER_NAME, text);
            Function.Call(Hash.END_TEXT_COMMAND_DISPLAY_TEXT, x, y);
        }

        private void DrawPropBuilderHud(BuilderCatalogCategory curCat, Tuple<string, string> curItem)
        {
            // Center Aim Crosshair
            Function.Call(Hash.DRAW_RECT, 0.5f, 0.5f, 0.008f, 0.0015f, 56, 189, 248, 220);
            Function.Call(Hash.DRAW_RECT, 0.5f, 0.5f, 0.001f, 0.012f, 56, 189, 248, 220);

            // Right-side Mod Menu Background Panel
            float panelX = 0.855f;
            float panelW = 0.26f;
            Function.Call(Hash.DRAW_RECT, panelX, 0.065f, panelW, 0.042f, 15, 118, 110, 240); // Teal Header
            DrawHudText("CROWDSIM 3D PROP STUDIO (F9)", panelX, 0.050f, 0.34f, 255, 255, 255, 255, true);

            // Category Bar
            Function.Call(Hash.DRAW_RECT, panelX, 0.102f, panelW, 0.032f, 30, 41, 59, 235);
            DrawHudText("< " + curCat.Name + " >", panelX, 0.090f, 0.28f, 56, 189, 248, 255, true);

            // Catalog Items List
            int itemCount = curCat.Items.Count;
            float startY = 0.132f;
            float rowH = 0.028f;
            for (int i = 0; i < itemCount; i++)
            {
                float ry = startY + i * rowH;
                bool isSel = (i == _builderItemIdx);
                if (isSel)
                {
                    Function.Call(Hash.DRAW_RECT, panelX, ry, panelW, rowH, 2, 132, 199, 230);
                    DrawHudText("> " + curCat.Items[i].Item2, panelX - panelW * 0.47f, ry - 0.011f, 0.25f, 255, 255, 255, 255, false);
                }
                else
                {
                    Function.Call(Hash.DRAW_RECT, panelX, ry, panelW, rowH, 15, 23, 42, 205);
                    DrawHudText("  " + curCat.Items[i].Item2, panelX - panelW * 0.47f, ry - 0.011f, 0.24f, 203, 213, 225, 240, false);
                }
            }

            // Telemetry & Controls Footer Box
            float footY = startY + itemCount * rowH + 0.095f;
            Function.Call(Hash.DRAW_RECT, panelX, footY, panelW, 0.19f, 9, 14, 23, 230);

            string shownModel = !string.IsNullOrEmpty(_sampledCustomModelName) ? _sampledCustomModelName : curItem.Item1;
            string modeStr = (_selectedPropHandle != 0)
                ? string.Format("EDITING #{0} | Size: {1:F1}x{2:F1}x{3:F1}m", _selectedPropHandle, _previewModelDims.X, _previewModelDims.Y, _previewModelDims.Z)
                : string.Format("{0} ({1:F1}x{2:F1}x{3:F1}m)", shownModel, _previewModelDims.X, _previewModelDims.Y, _previewModelDims.Z);

            float tx = panelX - panelW * 0.47f;
            float ty = footY - 0.088f;
            DrawHudText(modeStr, tx, ty, 0.24f, 45, 212, 191, 255, false);
            DrawHudText(string.Format("XYZ: ({0:F1}, {1:F1}, {2:F2}) | Z-Off: {3:+0.00;-0.00;0.00}m", _builderPreviewPos.X, _builderPreviewPos.Y, _builderPreviewPos.Z, _builderManualZOffset), tx, ty + 0.022f, 0.23f, 241, 245, 249, 255, false);
            DrawHudText(string.Format("Yaw: {0:F0} (Step[R]:{1:F0}) | TexVar[T]: #{2} | Placed:{3}", _builderHeading, _builderRotStep, _builderTextureVariation, _customProps.Count), tx, ty + 0.044f, 0.23f, 241, 245, 249, 255, false);
            DrawHudText(string.Format("Grid [G]: {0} | Clone Axis [V]: {1}", _builderGridSnap > 0 ? _builderGridSnap.ToString("F2") + "m" : "OFF", _builderCloneSideAxis ? "Length (Y)" : "Width (X)"), tx, ty + 0.066f, 0.23f, 251, 191, 36, 255, false);
            DrawHudText("[L-Click/Enter] Place  [R-Click/Bksp] Grab", tx, ty + 0.092f, 0.22f, 148, 163, 184, 255, false);
            DrawHudText("[Q/E/Wheel] Rotate  [PgUp/PgDn] Height Z", tx, ty + 0.112f, 0.22f, 148, 163, 184, 255, false);
            DrawHudText("[C] Edge-Clone [T] Texture [M] Sample Map [F10] Save", tx, ty + 0.132f, 0.21f, 148, 163, 184, 255, false);
        }

        private void SetNoclip(bool enabled)
        {
            _noclipEnabled = enabled;
            try
            {
                Ped p = Game.Player.Character;
                if (p != null && p.Exists())
                {
                    Entity ent = (p.IsInVehicle() && p.CurrentVehicle != null) ? (Entity)p.CurrentVehicle : (Entity)p;
                    ent.Velocity = Vector3.Zero;
                    Function.Call(Hash.SET_ENTITY_VELOCITY, ent.Handle, 0f, 0f, 0f);

                    if (_noclipEnabled)
                    {
                        // Enable NoClip: Freeze physics so no gravity or sinking, disable collision
                        Function.Call(Hash.SET_ENTITY_COLLISION, ent.Handle, false, false);
                        ent.IsCollisionEnabled = false;
                        Function.Call(Hash.FREEZE_ENTITY_POSITION, ent.Handle, true);
                        Function.Call(Hash.SET_PED_GRAVITY, p.Handle, false);
                        // Lift slightly off the floor on activation
                        Function.Call(Hash.SET_ENTITY_COORDS_NO_OFFSET, ent.Handle, ent.Position.X, ent.Position.Y, ent.Position.Z + 0.35f, true, true, true);
                    }
                    else
                    {
                        // Disable NoClip: Unfreeze, restore collision and normal gravity
                        Function.Call(Hash.FREEZE_ENTITY_POSITION, ent.Handle, false);
                        Function.Call(Hash.SET_ENTITY_COLLISION, ent.Handle, true, true);
                        ent.IsCollisionEnabled = true;
                        Function.Call(Hash.SET_PED_GRAVITY, p.Handle, true);

                        float gz;
                        if (TryGetPreciseSurfaceZ(ent.Position.X, ent.Position.Y, ent.Position.Z, out gz))
                        {
                            Function.Call(Hash.SET_ENTITY_COORDS_NO_OFFSET, ent.Handle, ent.Position.X, ent.Position.Y, gz + 0.15f, true, true, true);
                        }
                    }
                }
            }
            catch { }
        }

        [System.Runtime.InteropServices.DllImport("user32.dll")]
        private static extern short GetAsyncKeyState(int vKey);

        private void HandleNoclip(Ped playerPed)
        {
            try
            {
                Entity ent = (playerPed.IsInVehicle() && playerPed.CurrentVehicle != null)
                    ? (Entity)playerPed.CurrentVehicle
                    : (Entity)playerPed;

                // 1. Keep entity frozen in physics so gravity and ragdoll NEVER pull or sink the player
                Function.Call(Hash.FREEZE_ENTITY_POSITION, ent.Handle, true);
                Function.Call(Hash.SET_ENTITY_COLLISION, ent.Handle, false, false);
                Function.Call(Hash.SET_PED_GRAVITY, playerPed.Handle, false);
                Function.Call(Hash.SET_ENTITY_VELOCITY, ent.Handle, 0f, 0f, 0f);
                ent.Velocity = Vector3.Zero;

                // 2. Disable default on-foot movement controls so Franklin does NOT walk or sink
                Function.Call(Hash.DISABLE_CONTROL_ACTION, 0, (int)Control.MoveUpDown, true);
                Function.Call(Hash.DISABLE_CONTROL_ACTION, 0, (int)Control.MoveLeftRight, true);
                Function.Call(Hash.DISABLE_CONTROL_ACTION, 0, (int)Control.MoveUpOnly, true);
                Function.Call(Hash.DISABLE_CONTROL_ACTION, 0, (int)Control.MoveDownOnly, true);
                Function.Call(Hash.DISABLE_CONTROL_ACTION, 0, (int)Control.MoveLeftOnly, true);
                Function.Call(Hash.DISABLE_CONTROL_ACTION, 0, (int)Control.MoveRightOnly, true);
                Function.Call(Hash.DISABLE_CONTROL_ACTION, 0, (int)Control.Jump, true);
                Function.Call(Hash.DISABLE_CONTROL_ACTION, 0, (int)Control.Sprint, true);
                Function.Call(Hash.DISABLE_CONTROL_ACTION, 0, (int)Control.Duck, true);
                Function.Call(Hash.DISABLE_CONTROL_ACTION, 0, (int)Control.Attack, true);

                // 3. Calculate horizontal heading vectors from camera
                Vector3 camRot = GameplayCamera.Rotation;
                float yawRad = (float)(camRot.Z * Math.PI / 180.0);
                Vector3 forward2D = new Vector3(-(float)Math.Sin(yawRad), (float)Math.Cos(yawRad), 0f);
                Vector3 right2D = new Vector3((float)Math.Cos(yawRad), (float)Math.Sin(yawRad), 0f);

                // 4. Input detection: Check both GTA disabled controls and Windows hardware keyboard state
                bool isSpace = Function.Call<bool>(Hash.IS_DISABLED_CONTROL_PRESSED, 0, (int)Control.Jump)
                    || Function.Call<bool>(Hash.IS_CONTROL_PRESSED, 0, (int)Control.Jump)
                    || ((GetAsyncKeyState(0x20) & 0x8000) != 0);

                bool isShift = Function.Call<bool>(Hash.IS_DISABLED_CONTROL_PRESSED, 0, (int)Control.Sprint)
                    || Function.Call<bool>(Hash.IS_CONTROL_PRESSED, 0, (int)Control.Sprint)
                    || ((GetAsyncKeyState(0x10) & 0x8000) != 0)
                    || ((GetAsyncKeyState(0xA0) & 0x8000) != 0);

                bool isCtrl = Function.Call<bool>(Hash.IS_DISABLED_CONTROL_PRESSED, 0, (int)Control.Duck)
                    || Function.Call<bool>(Hash.IS_CONTROL_PRESSED, 0, (int)Control.Duck)
                    || ((GetAsyncKeyState(0x11) & 0x8000) != 0)
                    || ((GetAsyncKeyState(0xA2) & 0x8000) != 0);

                bool isW = Function.Call<bool>(Hash.IS_DISABLED_CONTROL_PRESSED, 0, (int)Control.MoveUpOnly)
                    || Function.Call<bool>(Hash.IS_CONTROL_PRESSED, 0, (int)Control.MoveUpOnly)
                    || ((GetAsyncKeyState(0x57) & 0x8000) != 0);

                bool isS = Function.Call<bool>(Hash.IS_DISABLED_CONTROL_PRESSED, 0, (int)Control.MoveDownOnly)
                    || Function.Call<bool>(Hash.IS_CONTROL_PRESSED, 0, (int)Control.MoveDownOnly)
                    || ((GetAsyncKeyState(0x53) & 0x8000) != 0);

                bool isA = Function.Call<bool>(Hash.IS_DISABLED_CONTROL_PRESSED, 0, (int)Control.MoveLeftOnly)
                    || Function.Call<bool>(Hash.IS_CONTROL_PRESSED, 0, (int)Control.MoveLeftOnly)
                    || ((GetAsyncKeyState(0x41) & 0x8000) != 0);

                bool isD = Function.Call<bool>(Hash.IS_DISABLED_CONTROL_PRESSED, 0, (int)Control.MoveRightOnly)
                    || Function.Call<bool>(Hash.IS_CONTROL_PRESSED, 0, (int)Control.MoveRightOnly)
                    || ((GetAsyncKeyState(0x44) & 0x8000) != 0);

                // Speed modifiers (Note: when Prop Builder is open, E is reserved for prop rotation)
                float speed = 0.9f;
                bool isFast = ((GetAsyncKeyState(0x09) & 0x8000) != 0) // Tab
                    || (!_propBuilderEnabled && ((GetAsyncKeyState(0x45) & 0x8000) != 0));
                bool isSlow = ((GetAsyncKeyState(0x12) & 0x8000) != 0); // Alt

                if (isFast) speed = 2.6f;
                else if (isSlow) speed = 0.2f;

                Vector3 newPos = ent.Position;

                // Horizontal translation
                if (isW) newPos += forward2D * speed;
                if (isS) newPos -= forward2D * speed;
                if (isD) newPos += right2D * speed;
                if (isA) newPos -= right2D * speed;

                // SPACE FOR UP
                if (isSpace) newPos += Vector3.WorldUp * speed;

                // SHIFT FOR DOWNWARDS (Ctrl also descends)
                if (isShift || isCtrl) newPos -= Vector3.WorldUp * speed;

                // 5. Instantly update coordinates without offset or ground collision drag
                Function.Call(Hash.SET_ENTITY_COORDS_NO_OFFSET, ent.Handle, newPos.X, newPos.Y, newPos.Z, true, true, true);
                ent.Heading = camRot.Z;
            }
            catch { }
        }

        private void VerifyFullSizeStationModels()
        {
            try
            {
                string[] testModels = new string[]
                {
                    "bkr_prop_biker_bblock_sml1", "bkr_prop_biker_bblock_sml2", "bkr_prop_biker_bblock_mdm1",
                    "bkr_prop_biker_bblock_lrg1", "bkr_prop_biker_bblock_xl1", "bkr_prop_biker_bblock_huge_01",
                    "bkr_prop_biker_bblock_hump_01", "stt_prop_stunt_bblock_sml2", "stt_prop_stunt_bblock_mdm2",
                    "stt_prop_stunt_bblock_lrg2", "stt_prop_stunt_bblock_xl2", "stt_prop_stunt_track_dwshort",
                    "stt_prop_stunt_track_straight", "stt_prop_stunt_wideramp", "prop_gate_bridge_ld",
                    "hei_prop_carrier_stair_01a", "prop_byard_steps_01", "prop_steps_big_01",
                    "prop_portacabin01", "prop_container_03a", "prop_barier_conc_05a",
                    "hei_prop_station_gate", "prop_turnstyle_01", "prop_turnstyle_bars"
                };
                StringBuilder sb = new StringBuilder();
                for (int i = 0; i < testModels.Length; i++)
                {
                    string mName = testModels[i];
                    Model m = new Model(mName);
                    bool valid = m.IsValid;
                    bool loaded = valid && (m.IsLoaded || m.Request(350));
                    float w = 0f, l = 0f, h = 0f;
                    if (loaded) GetModelSize(m, out w, out l, out h);
                    sb.AppendLine(string.Format("{0}: Valid={1}, Loaded={2}, Size=({3:F2}m x {4:F2}m x {5:F2}m)", mName, valid, loaded, w, l, h));
                }
                File.WriteAllText(@"C:\Users\Teja-Clove\GTA_crowd\logs\model_verify.log", sb.ToString(), Encoding.UTF8);
            }
            catch { }
        }

        private void PurgeAirportPropsInWorld()
        {
            try
            {
                int purged = 0;
                int[] bannedHashes = new int[]
                {
                    Game.GenerateHash("prop_air_bridge01"),
                    Game.GenerateHash("prop_air_bridge02"),
                    Game.GenerateHash("prop_air_stair_01"),
                    Game.GenerateHash("prop_air_stair_02"),
                    Game.GenerateHash("prop_barier_conc_01a"),
                    Game.GenerateHash("prop_barier_conc_02a"),
                    Game.GenerateHash("prop_barier_conc_03a"),
                    Game.GenerateHash("prop_gate_bridge_ld"),
                    Game.GenerateHash("prop_byard_steps_01"),
                    Game.GenerateHash("prop_steps_big_01"),
                    Game.GenerateHash("prop_fnclink_03e")
                };

                Vector3 lsiaCenter = new Vector3(-1340.0f, -3040.0f, 13.95f);
                Prop[] allProps = World.GetAllProps();
                if (allProps != null)
                {
                    for (int i = 0; i < allProps.Length; i++)
                    {
                        Prop p = allProps[i];
                        if (p != null && p.Exists())
                        {
                            if ((p.Position - lsiaCenter).Length() > 1000.0f) continue;
                            int h = p.Model.Hash;
                            for (int b = 0; b < bannedHashes.Length; b++)
                            {
                                if (h == bannedHashes[b])
                                {
                                    int pHandle = p.Handle;
                                    p.Delete();
                                    lock (_lock)
                                    {
                                        _customProps.Remove(pHandle);
                                        _stationPropHandles.Remove(pHandle);
                                    }
                                    purged++;
                                    break;
                                }
                            }
                        }
                    }
                }
                if (purged > 0)
                {
                    Log(string.Format("INFO: Purged {0} old airport / small barrier props from LSIA.", purged));
                }
                VerifyFullSizeStationModels();
            }
            catch (Exception ex)
            {
                Log("WARN: PurgeAirportPropsInWorld error: " + ex.Message);
            }
        }

        private void ClearStationProps()
        {
            SyncWorldPropsWithManager();
            DeletePreviewProp();
            _selectedPropHandle = 0;
            _aimedPropHandle = 0;
            _lastPlacedPropHandle = 0;
            List<int> allHandles;
            lock (_lock)
            {
                allHandles = new List<int>(_stationPropHandles);
                foreach (int k in _customProps.Keys)
                {
                    if (!allHandles.Contains(k)) allHandles.Add(k);
                }
            }
            for (int i = 0; i < allHandles.Count; i++)
            {
                ForceDeletePropEntity(allHandles[i]);
            }
            lock (_lock)
            {
                _stationPropHandles.Clear();
                _customProps.Clear();
                _propUndoStack.Clear();
            }
            PurgeAirportPropsInWorld();
            Log("INFO: Cleared all custom station props.");
        }

        private Prop SpawnSingleConcreteProp(string modelName, Vector3 pos, Vector3 rotPitchRollYaw, string zoneTag, ref int counter)
        {
            try
            {
                Model m = ParseModelFromString(modelName);
                if (m.IsValid && (m.IsLoaded || m.Request(600)))
                {
                    Prop p = CreateConfiguredStationProp(m, modelName, pos, rotPitchRollYaw, zoneTag);
                    if (p != null && p.Exists())
                    {
                        _lastPlacedPropHandle = p.Handle;
                        counter++;
                        return p;
                    }
                }
            }
            catch { }
            return null;
        }

        private int SpawnConcretePrefab(string prefabName, Vector3 origin, float heading, string zoneTag)
        {
            int count = 0;
            SpawnSingleConcreteProp("bkr_prop_biker_bblock_mdm1", origin, new Vector3(0f, 0f, heading), zoneTag, ref count);
            return count;
        }

        private int BuildCustomStation(float bx, float by, float bz)
        {
            ClearStationProps();
            int spawnedCount = 0;

            string[] preloadModels = new string[]
            {
                "bkr_prop_biker_bblock_lrg1", "bkr_prop_biker_bblock_mdm1", "bkr_prop_biker_bblock_sml1",
                "bkr_prop_biker_bblock_sml2", "stt_prop_stunt_track_dwshort", "prop_gate_bridge_ld",
                "hei_prop_carrier_stair_01a", "prop_byard_steps_01", "prop_steps_big_01",
                "prop_portacabin01", "prop_barier_conc_05a", "hei_prop_station_gate",
                "prop_turnstyle_01", "prop_turnstyle_bars", "prop_tollbooth_1",
                "prop_vend_snak_01", "prop_vend_soda_01", "gr_prop_gr_bench_01a",
                "prop_streetlight_01", "prop_gazebo_01", "prop_gazebo_02",
                "prop_parasol_01", "prop_ven_market_table1", "prop_table_03",
                "prop_crate_01a", "prop_boxpile_02b", "prop_busstop_02",
                "prop_busstop_04", "prop_mp_barrier_02b"
            };
            for (int mIdx = 0; mIdx < preloadModels.Length; mIdx++)
            {
                try
                {
                    Model m = new Model(preloadModels[mIdx]);
                    if (m.IsValid) m.Request(800);
                }
                catch { }
            }

            // =========================================================================================
            // FULL-SIZE SINGLE-PIECE MENYOO STATION & OUTSIDE MARKET COMPLEX
            // Uses massive single-piece concrete platforms (bkr_prop_biker_bblock_lrg1/mdm1/sml1),
            // full-size overpass bridges (prop_gate_bridge_ld / stt_prop_stunt_track_dwshort),
            // and full-height staircases (hei_prop_carrier_stair_01a / prop_byard_steps_01 / prop_steps_big_01)
            // =========================================================================================

            // --- ZONE 1A: PLATFORM 2 (North Full-Size Concrete Platform: y = by + 9.0f) ---
            SpawnSingleConcreteProp("bkr_prop_biker_bblock_lrg1", new Vector3(bx - 10.0f, by + 9.0f, bz - 0.35f), new Vector3(0f, 0f, 0f), "Platform_2", ref spawnedCount);
            SpawnSingleConcreteProp("bkr_prop_biker_bblock_lrg1", new Vector3(bx + 12.0f, by + 9.0f, bz - 0.35f), new Vector3(0f, 0f, 0f), "Platform_2", ref spawnedCount);
            SpawnSingleConcreteProp("prop_gazebo_02", new Vector3(bx - 12.0f, by + 9.5f, bz), new Vector3(0f, 0f, 0f), "Platform_2", ref spawnedCount);
            SpawnSingleConcreteProp("prop_gazebo_02", new Vector3(bx + 13.0f, by + 9.5f, bz), new Vector3(0f, 0f, 0f), "Platform_2", ref spawnedCount);
            SpawnSingleConcreteProp("gr_prop_gr_bench_01a", new Vector3(bx - 14.0f, by + 10.8f, bz), new Vector3(0f, 0f, 180f), "Platform_2", ref spawnedCount);
            SpawnSingleConcreteProp("gr_prop_gr_bench_01a", new Vector3(bx - 9.0f, by + 10.8f, bz), new Vector3(0f, 0f, 180f), "Platform_2", ref spawnedCount);
            SpawnSingleConcreteProp("gr_prop_gr_bench_01a", new Vector3(bx + 11.0f, by + 10.8f, bz), new Vector3(0f, 0f, 180f), "Platform_2", ref spawnedCount);
            SpawnSingleConcreteProp("gr_prop_gr_bench_01a", new Vector3(bx + 16.0f, by + 10.8f, bz), new Vector3(0f, 0f, 180f), "Platform_2", ref spawnedCount);
            SpawnSingleConcreteProp("prop_streetlight_01", new Vector3(bx - 17.0f, by + 12.0f, bz), new Vector3(0f, 0f, 180f), "Platform_2", ref spawnedCount);
            SpawnSingleConcreteProp("prop_streetlight_01", new Vector3(bx + 18.0f, by + 12.0f, bz), new Vector3(0f, 0f, 180f), "Platform_2", ref spawnedCount);

            // --- ZONE 1B: PLATFORM 1 (South Full-Size Concrete Platform: y = by - 9.0f) ---
            SpawnSingleConcreteProp("bkr_prop_biker_bblock_lrg1", new Vector3(bx - 10.0f, by - 9.0f, bz - 0.35f), new Vector3(0f, 0f, 0f), "Platform_1", ref spawnedCount);
            SpawnSingleConcreteProp("bkr_prop_biker_bblock_lrg1", new Vector3(bx + 12.0f, by - 9.0f, bz - 0.35f), new Vector3(0f, 0f, 0f), "Platform_1", ref spawnedCount);
            SpawnSingleConcreteProp("prop_gazebo_02", new Vector3(bx - 12.0f, by - 8.5f, bz), new Vector3(0f, 0f, 0f), "Platform_1", ref spawnedCount);
            SpawnSingleConcreteProp("gr_prop_gr_bench_01a", new Vector3(bx - 14.0f, by - 10.0f, bz), new Vector3(0f, 0f, 0f), "Platform_1", ref spawnedCount);
            SpawnSingleConcreteProp("gr_prop_gr_bench_01a", new Vector3(bx - 9.0f, by - 10.0f, bz), new Vector3(0f, 0f, 0f), "Platform_1", ref spawnedCount);
            SpawnSingleConcreteProp("prop_streetlight_01", new Vector3(bx - 17.0f, by - 11.2f, bz), new Vector3(0f, 0f, 0f), "Platform_1", ref spawnedCount);

            // --- ZONE 2: FULL-SIZE FOOT OVER BRIDGE (FOB) & FULL-HEIGHT STAIRCASES (x = bx + 4.0f) ---
            float bridgeZ = bz + 3.6f;
            SpawnSingleConcreteProp("prop_gate_bridge_ld", new Vector3(bx + 4.0f, by + 1.5f, bridgeZ), new Vector3(0f, 0f, 0f), "FOB_Bridge", ref spawnedCount);
            SpawnSingleConcreteProp("prop_gate_bridge_ld", new Vector3(bx + 4.0f, by - 2.5f, bridgeZ), new Vector3(0f, 0f, 0f), "FOB_Bridge", ref spawnedCount);
            SpawnSingleConcreteProp("bkr_prop_biker_bblock_sml2", new Vector3(bx + 4.0f, by, bridgeZ - 0.25f), new Vector3(0f, 0f, 90f), "FOB_Bridge", ref spawnedCount);

            // Full-Height North Staircase (Platform 2 -> FOB Deck)
            SpawnSingleConcreteProp("hei_prop_carrier_stair_01a", new Vector3(bx + 4.0f, by + 6.0f, bz), new Vector3(0f, 0f, 180f), "Stairs", ref spawnedCount);
            SpawnSingleConcreteProp("prop_byard_steps_01", new Vector3(bx + 4.0f, by + 5.5f, bz), new Vector3(0f, 0f, 0f), "Stairs", ref spawnedCount);
            SpawnSingleConcreteProp("prop_steps_big_01", new Vector3(bx + 4.0f, by + 7.5f, bz), new Vector3(0f, 0f, 0f), "Stairs", ref spawnedCount);

            // Full-Height South Staircase (FOB Deck -> Platform 1 / Concourse Hall)
            SpawnSingleConcreteProp("hei_prop_carrier_stair_01a", new Vector3(bx + 4.0f, by - 6.0f, bz), new Vector3(0f, 0f, 0f), "Stairs", ref spawnedCount);
            SpawnSingleConcreteProp("prop_byard_steps_01", new Vector3(bx + 4.0f, by - 5.5f, bz), new Vector3(0f, 0f, 180f), "Stairs", ref spawnedCount);
            SpawnSingleConcreteProp("prop_steps_big_01", new Vector3(bx + 4.0f, by - 7.5f, bz), new Vector3(0f, 0f, 180f), "Stairs", ref spawnedCount);

            // --- ZONE 3: MAIN ENTRANCE / EXIT CONCOURSE HALL & TURNSTILES (y = by - 12 .. by - 18) ---
            SpawnSingleConcreteProp("bkr_prop_biker_bblock_mdm1", new Vector3(bx + 11.0f, by - 15.0f, bz - 0.35f), new Vector3(0f, 0f, 0f), "Entrance_Hall", ref spawnedCount);
            SpawnSingleConcreteProp("prop_portacabin01", new Vector3(bx + 20.5f, by - 14.5f, bz), new Vector3(0f, 0f, 90f), "Entrance_Hall", ref spawnedCount);
            SpawnSingleConcreteProp("prop_tollbooth_1", new Vector3(bx + 17.5f, by - 14.2f, bz), new Vector3(0f, 0f, 270f), "Entrance_Hall", ref spawnedCount);
            SpawnSingleConcreteProp("prop_vend_snak_01", new Vector3(bx + 2.8f, by - 14.2f, bz), new Vector3(0f, 0f, 90f), "Entrance_Hall", ref spawnedCount);
            SpawnSingleConcreteProp("prop_vend_soda_01", new Vector3(bx + 2.8f, by - 15.8f, bz), new Vector3(0f, 0f, 90f), "Entrance_Hall", ref spawnedCount);

            // Turnstile Gate Line (y = by - 18.0f opening South into Outside Market)
            SpawnSingleConcreteProp("prop_barier_conc_05a", new Vector3(bx + 3.5f, by - 18.0f, bz), new Vector3(0f, 0f, 0f), "Entrance_Hall", ref spawnedCount);
            SpawnSingleConcreteProp("hei_prop_station_gate", new Vector3(bx + 7.5f, by - 18.0f, bz), new Vector3(0f, 0f, 0f), "Turnstiles", ref spawnedCount);
            SpawnSingleConcreteProp("prop_turnstyle_01", new Vector3(bx + 10.5f, by - 18.0f, bz), new Vector3(0f, 0f, 0f), "Turnstiles", ref spawnedCount);
            SpawnSingleConcreteProp("prop_turnstyle_bars", new Vector3(bx + 13.0f, by - 18.0f, bz), new Vector3(0f, 0f, 0f), "Turnstiles", ref spawnedCount);
            SpawnSingleConcreteProp("prop_turnstyle_01", new Vector3(bx + 15.5f, by - 18.0f, bz), new Vector3(0f, 0f, 0f), "Turnstiles", ref spawnedCount);
            SpawnSingleConcreteProp("prop_barier_conc_05a", new Vector3(bx + 18.5f, by - 18.0f, bz), new Vector3(0f, 0f, 0f), "Entrance_Hall", ref spawnedCount);

            // --- ZONE 4: SIMULATED OUTSIDE STREET MARKET & TRANSIT ROAD (y = by - 21 .. by - 36) ---
            SpawnSingleConcreteProp("prop_gazebo_01", new Vector3(bx + 3.0f, by - 23.0f, bz), new Vector3(0f, 0f, 90f), "Market", ref spawnedCount);
            SpawnSingleConcreteProp("prop_ven_market_table1", new Vector3(bx + 3.0f, by - 23.0f, bz), new Vector3(0f, 0f, 90f), "Market", ref spawnedCount);
            SpawnSingleConcreteProp("prop_crate_01a", new Vector3(bx + 1.5f, by - 24.5f, bz), new Vector3(0f, 0f, 15f), "Market", ref spawnedCount);
            SpawnSingleConcreteProp("prop_gazebo_02", new Vector3(bx + 3.0f, by - 28.0f, bz), new Vector3(0f, 0f, 90f), "Market", ref spawnedCount);
            SpawnSingleConcreteProp("prop_table_03", new Vector3(bx + 3.0f, by - 28.0f, bz), new Vector3(0f, 0f, 90f), "Market", ref spawnedCount);
            SpawnSingleConcreteProp("prop_boxpile_02b", new Vector3(bx + 1.5f, by - 29.5f, bz), new Vector3(0f, 0f, 0f), "Market", ref spawnedCount);

            SpawnSingleConcreteProp("prop_gazebo_02", new Vector3(bx + 19.0f, by - 23.0f, bz), new Vector3(0f, 0f, 270f), "Market", ref spawnedCount);
            SpawnSingleConcreteProp("prop_ven_market_table1", new Vector3(bx + 19.0f, by - 23.0f, bz), new Vector3(0f, 0f, 270f), "Market", ref spawnedCount);
            SpawnSingleConcreteProp("prop_gazebo_01", new Vector3(bx + 19.0f, by - 28.0f, bz), new Vector3(0f, 0f, 270f), "Market", ref spawnedCount);
            SpawnSingleConcreteProp("prop_table_03", new Vector3(bx + 19.0f, by - 28.0f, bz), new Vector3(0f, 0f, 270f), "Market", ref spawnedCount);
            SpawnSingleConcreteProp("prop_crate_01a", new Vector3(bx + 20.5f, by - 26.0f, bz), new Vector3(0f, 0f, 45f), "Market", ref spawnedCount);

            SpawnSingleConcreteProp("prop_parasol_01", new Vector3(bx + 11.0f, by - 25.5f, bz), new Vector3(0f, 0f, 0f), "Market", ref spawnedCount);
            SpawnSingleConcreteProp("gr_prop_gr_bench_01a", new Vector3(bx + 9.0f, by - 25.5f, bz), new Vector3(0f, 0f, 90f), "Market", ref spawnedCount);
            SpawnSingleConcreteProp("gr_prop_gr_bench_01a", new Vector3(bx + 13.0f, by - 25.5f, bz), new Vector3(0f, 0f, 270f), "Market", ref spawnedCount);

            SpawnSingleConcreteProp("prop_busstop_02", new Vector3(bx + 5.0f, by - 33.5f, bz), new Vector3(0f, 0f, 0f), "Road_Plaza", ref spawnedCount);
            SpawnSingleConcreteProp("prop_busstop_04", new Vector3(bx + 17.0f, by - 33.5f, bz), new Vector3(0f, 0f, 0f), "Road_Plaza", ref spawnedCount);
            SpawnSingleConcreteProp("prop_streetlight_01", new Vector3(bx + 0.0f, by - 33.5f, bz), new Vector3(0f, 0f, 0f), "Road_Plaza", ref spawnedCount);
            SpawnSingleConcreteProp("prop_streetlight_01", new Vector3(bx + 22.0f, by - 33.5f, bz), new Vector3(0f, 0f, 0f), "Road_Plaza", ref spawnedCount);
            for (int r = -2; r <= 6; r++)
            {
                SpawnSingleConcreteProp("prop_mp_barrier_02b", new Vector3(bx + r * 4.0f, by - 36.5f, bz), new Vector3(0f, 0f, 0f), "Road_Plaza", ref spawnedCount);
            }

            Log(string.Format("INFO: Built Full-Size Single-Piece LSIA Station & Market Complex with {0} props at ({1:F1}, {2:F1}, {3:F1})", spawnedCount, bx, by, bz));
            return spawnedCount;
        }

        #endregion

        
        #region Precision Surface Detection (Props, Props-on-Props & Terrain)

        /// <summary>
        /// Bulletproof surface height detector using physics raycasts with IntersectFlags.Map | IntersectFlags.Objects.
        /// Accurately detects static map terrain, custom modular props, and props stacked on top of props.
        /// </summary>
        private bool TryGetPreciseSurfaceZ(float x, float y, float? hintZ, out float surfaceZ)
        {
            surfaceZ = 0f;
            Entity ignoreEnt = (_previewPropHandle != 0) ? Entity.FromHandle(_previewPropHandle) : null;

            // Strategy 1: Targeted vertical Raycast from above expected surface downwards
            float topZ = hintZ.HasValue ? Math.Max(hintZ.Value + 15.0f, 150.0f) : 350.0f;
            float bottomZ = -60.0f;

            RaycastResult ray = World.Raycast(
                new Vector3(x, y, topZ),
                new Vector3(x, y, bottomZ),
                IntersectFlags.Map | IntersectFlags.Objects,
                ignoreEnt
            );

            if (ray.DidHit && ray.HitPosition.Z > -50.0f)
            {
                surfaceZ = ray.HitPosition.Z;
                return true;
            }

            // Strategy 2: High-altitude sky Raycast (for high bridges, roofs, or steep hills)
            RaycastResult highRay = World.Raycast(
                new Vector3(x, y, 950.0f),
                new Vector3(x, y, -60.0f),
                IntersectFlags.Map | IntersectFlags.Objects,
                ignoreEnt
            );

            if (highRay.DidHit && highRay.HitPosition.Z > -50.0f)
            {
                surfaceZ = highRay.HitPosition.Z;
                return true;
            }

            // Strategy 3: Multi-altitude native ground height probe
            float[] probeAltitudes = new float[] { 800f, 300f, 100f, 50f, 20f };
            foreach (float alt in probeAltitudes)
            {
                float nativeGz = 0f;
                if (World.GetGroundHeight(new Vector3(x, y, alt), out nativeGz) && nativeGz > -50.0f)
                {
                    surfaceZ = nativeGz;
                    return true;
                }
            }

            return false;
        }

        #endregion

        private void ProcessPingCommand(CommandItem cmd)
        {
            Player player = Game.Player;
            int playerHandle = (player != null && player.Character != null) ? player.Character.Handle : -1;
            int gameTime = Game.GameTime;

            Vector3 pos = (player != null && player.Character != null) ? player.Character.Position : Vector3.Zero;
            float heading = (player != null && player.Character != null) ? player.Character.Heading : 0f;

            Log(string.Format("DIAG: Processed PING_GAME (PlayerHandle: {0}, GameTime: {1}, ReqID: {2}, Pos: {3},{4})",
                playerHandle, gameTime, cmd.RequestId, Math.Round(pos.X, 1), Math.Round(pos.Y, 1)));

            Dictionary<string, object> ackData = new Dictionary<string, object>();
            ackData["request_id"] = cmd.RequestId;
            ackData["command"] = cmd.Command;
            ackData["status"] = "ACK";
            ackData["player_handle"] = playerHandle;
            ackData["game_time"] = gameTime;
            ackData["timestamp_utc"] = DateTime.UtcNow.ToString("o");

            Dictionary<string, object> posDict = new Dictionary<string, object>();
            posDict["x"] = Math.Round(pos.X, 2);
            posDict["y"] = Math.Round(pos.Y, 2);
            posDict["z"] = Math.Round(pos.Z, 2);
            posDict["heading"] = Math.Round(heading, 1);
            ackData["player_position"] = posDict;

            EnqueueAck(ackData);
        }

        private void ProcessSpawnPedCommand(CommandItem cmd)
        {
            string modelName = "a_m_y_hipster_01";
            float distance = 4.0f;

            if (cmd.Payload != null)
            {
                if (cmd.Payload.ContainsKey("model") && cmd.Payload["model"] != null)
                {
                    string m = Convert.ToString(cmd.Payload["model"]).Trim();
                    if (!string.IsNullOrEmpty(m)) modelName = m;
                }
                if (cmd.Payload.ContainsKey("distance") && cmd.Payload["distance"] != null)
                {
                    float d;
                    if (float.TryParse(Convert.ToString(cmd.Payload["distance"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out d))
                    {
                        distance = Math.Max(2.0f, Math.Min(10.0f, d));
                    }
                }
            }

            // Cap validation against total population limit
            int currentTotal;
            lock (_lock) { currentTotal = _crowdRegistry.Count; }
            if (currentTotal >= MaxTotalPopulation)
            {
                SendErrorAck(cmd, string.Format("Total population limit reached ({0}/{1}).", currentTotal, MaxTotalPopulation));
                return;
            }

            Model model = new Model(modelName);
            if (!model.IsValid)
            {
                SendErrorAck(cmd, string.Format("Invalid pedestrian model: '{0}'", modelName));
                return;
            }

            if (!model.IsLoaded)
            {
                model.Request(1500);
                if (!model.IsLoaded)
                {
                    model.MarkAsNoLongerNeeded();
                    SendErrorAck(cmd, string.Format("Model streaming timeout (1500ms): '{0}'", modelName));
                    return;
                }
            }

            Player player = Game.Player;
            if (player == null || player.Character == null || !player.Character.Exists())
            {
                model.MarkAsNoLongerNeeded();
                SendErrorAck(cmd, "Player character not found in world.");
                return;
            }

            Ped playerPed = player.Character;
            Vector3 forward = playerPed.ForwardVector;
            Vector3 targetSpawnPos = playerPed.Position + (forward * distance);

            Ped spawnedPed = null;
            try
            {
                spawnedPed = Ped.Create(model, targetSpawnPos, (playerPed.Heading + 180f) % 360f);
            }
            catch (Exception ex)
            {
                model.MarkAsNoLongerNeeded();
                SendErrorAck(cmd, string.Format("World.CreatePed failed: {0}", ex.Message));
                return;
            }

            if (spawnedPed == null || !spawnedPed.Exists())
            {
                model.MarkAsNoLongerNeeded();
                SendErrorAck(cmd, "World.CreatePed returned null or invalid entity.");
                return;
            }

            model.MarkAsNoLongerNeeded();

            try
            {
                spawnedPed.IsPersistent = true;
                spawnedPed.BlockPermanentEvents = true;
                spawnedPed.Task.WanderAround(spawnedPed.Position, 25.0f);
            }
            catch (Exception ex)
            {
                Log(string.Format("WARN: Task assignment threw on ped {0}: {1}", spawnedPed.Handle, ex.Message));
            }

            lock (_lock)
            {
                _crowdRegistry.Add(new CrowdPedRecord
                {
                    Handle = spawnedPed.Handle,
                    ModelName = modelName,
                    CreatedAt = DateTime.UtcNow,
                    GroupId = null
                });
            }

            Dictionary<string, object> ackData = new Dictionary<string, object>();
            ackData["request_id"] = cmd.RequestId;
            ackData["command"] = cmd.Command;
            ackData["status"] = "ACK";
            ackData["entity_handle"] = spawnedPed.Handle;
            ackData["model"] = modelName;
            ackData["game_time"] = Game.GameTime;
            ackData["timestamp_utc"] = DateTime.UtcNow.ToString("o");

            Dictionary<string, object> coords = new Dictionary<string, object>();
            coords["x"] = Math.Round(spawnedPed.Position.X, 2);
            coords["y"] = Math.Round(spawnedPed.Position.Y, 2);
            coords["z"] = Math.Round(spawnedPed.Position.Z, 2);
            ackData["spawn_coords"] = coords;

            EnqueueAck(ackData);
        }

        private void ProcessClearPedsCommand(CommandItem cmd)
        {
            int cleared = 0;
            int failed = 0;
            string targetGroupId = "";
            if (cmd.Payload != null)
            {
                if (cmd.Payload.ContainsKey("group_id")) targetGroupId = Convert.ToString(cmd.Payload["group_id"]).Trim();
                else if (cmd.Payload.ContainsKey("id")) targetGroupId = Convert.ToString(cmd.Payload["id"]).Trim();
            }

            lock (_lock)
            {
                if (!string.IsNullOrEmpty(targetGroupId))
                {
                    if (_groups.ContainsKey(targetGroupId))
                    {
                        CrowdGroup grp = _groups[targetGroupId];
                        for (int i = 0; i < grp.MemberHandles.Count; i++)
                        {
                            try
                            {
                                Ped p = Entity.FromHandle(grp.MemberHandles[i]) as Ped;
                                if (p != null && p.Exists())
                                {
                                    p.IsPersistent = false;
                                    p.Delete();
                                    cleared++;
                                }
                            }
                            catch
                            {
                                failed++;
                            }
                        }
                        _crowdRegistry.RemoveAll(delegate (CrowdPedRecord r) { return r.GroupId == targetGroupId; });
                        grp.MemberHandles.Clear();
                        grp.SpawnedCount = 0;
                        grp.PendingCount = 0;
                        grp.Status = "CONFIGURED";
                        ReleaseGroupModels(grp);
                        Log(string.Format("INFO: Cleared {0} pedestrians for group '{1}' ({2}) (Failed: {3})", cleared, grp.Name, targetGroupId, failed));
                    }
                }
                else
                {
                    for (int i = 0; i < _crowdRegistry.Count; i++)
                    {
                        try
                        {
                            Ped p = Entity.FromHandle(_crowdRegistry[i].Handle) as Ped;
                            if (p != null && p.Exists())
                            {
                                p.IsPersistent = false;
                                p.Delete();
                                cleared++;
                            }
                        }
                        catch
                        {
                            failed++;
                        }
                    }
                    _crowdRegistry.Clear();

                    foreach (CrowdGroup grp in _groups.Values)
                    {
                        grp.MemberHandles.Clear();
                        grp.LeaderHandle = 0;
                        grp.SpawnedCount = 0;
                        grp.PendingCount = 0;
                        grp.Status = "CONFIGURED";
                        ReleaseGroupModels(grp);
                    }
                    Log(string.Format("INFO: Cleared all {0} CrowdSim pedestrians (Failed: {1})", cleared, failed));
                }
            }

            Dictionary<string, object> ackData = new Dictionary<string, object>();
            ackData["request_id"] = cmd.RequestId;
            ackData["command"] = cmd.Command;
            ackData["status"] = "ACK";
            ackData["cleared_count"] = cleared;
            ackData["failed_count"] = failed;
            ackData["game_time"] = Game.GameTime;
            ackData["timestamp_utc"] = DateTime.UtcNow.ToString("o");

            EnqueueAck(ackData);
        }

        private void ProcessCreateGroupCommand(CommandItem cmd)
        {
            Dictionary<string, object> payload = cmd.Payload ?? new Dictionary<string, object>();

            string groupName = payload.ContainsKey("name") ? Convert.ToString(payload["name"]).Trim() : "";
            if (string.IsNullOrEmpty(groupName))
            {
                groupName = "Group_" + (++_groupCounter);
            }

            int targetCount = DefaultGroupSize;
            if (payload.ContainsKey("count") && payload["count"] != null)
            {
                int c;
                if (int.TryParse(Convert.ToString(payload["count"]), out c))
                {
                    targetCount = Math.Max(1, Math.Min(MaxGroupPopulation, c));
                }
            }

            // Global Population Capacity Check
            int totalActiveAndPending = 0;
            lock (_lock)
            {
                totalActiveAndPending = _crowdRegistry.Count;
                foreach (CrowdGroup g in _groups.Values)
                {
                    if (g.Status == "SPAWNING")
                    {
                        totalActiveAndPending += g.PendingCount;
                    }
                }
            }

            if (totalActiveAndPending + targetCount > MaxTotalPopulation)
            {
                int remainingAllowed = Math.Max(0, MaxTotalPopulation - totalActiveAndPending);
                SendErrorAck(cmd, string.Format("Total population limit ({0}) exceeded. Currently active/pending: {1}. Maximum allowed new peds: {2}.",
                    MaxTotalPopulation, totalActiveAndPending, remainingAllowed));
                return;
            }

            float spawnRadius = 20.0f;
            if (payload.ContainsKey("spawn_radius"))
            {
                float sr;
                if (float.TryParse(Convert.ToString(payload["spawn_radius"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out sr))
                    spawnRadius = Math.Max(5.0f, Math.Min(150.0f, sr));
            }
            else if (payload.ContainsKey("radius"))
            {
                float r;
                if (float.TryParse(Convert.ToString(payload["radius"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out r))
                    spawnRadius = Math.Max(5.0f, Math.Min(150.0f, r));
            }

            float moveRadius = 30.0f;
            if (payload.ContainsKey("movement_radius"))
            {
                float mr;
                if (float.TryParse(Convert.ToString(payload["movement_radius"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out mr))
                    moveRadius = Math.Max(5.0f, Math.Min(150.0f, mr));
            }

            float spawnRate = 2.0f;
            if (payload.ContainsKey("spawn_rate"))
            {
                float srate;
                if (float.TryParse(Convert.ToString(payload["spawn_rate"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out srate))
                    spawnRate = Math.Max(0.5f, Math.Min(100.0f, srate));
            }

            string behavior = "INDEPENDENT_WANDER";
            if (payload.ContainsKey("behavior") && payload["behavior"] != null)
            {
                string b = Convert.ToString(payload["behavior"]).Trim().ToUpperInvariant();
                if (!string.IsNullOrEmpty(b)) behavior = b;
            }

            float followDistance = 3.0f;
            if (payload.ContainsKey("follow_distance"))
            {
                float fd;
                if (float.TryParse(Convert.ToString(payload["follow_distance"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out fd))
                    followDistance = Math.Max(1.0f, Math.Min(20.0f, fd));
            }

            bool densityAware = false;
            if (payload.ContainsKey("density_aware"))
            {
                bool da;
                if (bool.TryParse(Convert.ToString(payload["density_aware"]), out da))
                    densityAware = da;
            }

            float densityLimit = 0.2f;
            if (payload.ContainsKey("density_limit"))
            {
                float dl;
                if (float.TryParse(Convert.ToString(payload["density_limit"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out dl))
                    densityLimit = Math.Max(0.01f, Math.Min(5.0f, dl));
            }

            // Stage 4 Route Parameters: Origin, Destination, Waypoints, Speed, ArrivalBehavior, Color
            Vector3? explicitOrigin = null;
            float originRadius = spawnRadius;
            if (payload.ContainsKey("origin") && payload["origin"] is Dictionary<string, object>)
            {
                explicitOrigin = ParseVector3Dict((Dictionary<string, object>)payload["origin"]);
            }
            if (payload.ContainsKey("origin_radius"))
            {
                float orad;
                if (float.TryParse(Convert.ToString(payload["origin_radius"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out orad))
                    originRadius = Math.Max(2.0f, Math.Min(100.0f, orad));
            }

            Vector3? explicitDestination = null;
            float destRadius = 8.0f;
            if (payload.ContainsKey("destination") && payload["destination"] is Dictionary<string, object>)
            {
                explicitDestination = ParseVector3Dict((Dictionary<string, object>)payload["destination"]);
            }
            if (payload.ContainsKey("destination_radius"))
            {
                float dr;
                if (float.TryParse(Convert.ToString(payload["destination_radius"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out dr))
                    destRadius = Math.Max(2.0f, Math.Min(100.0f, dr));
            }

            List<Vector3> waypoints = new List<Vector3>();
            if (payload.ContainsKey("waypoints") && payload["waypoints"] is System.Collections.IEnumerable)
            {
                foreach (object wObj in (System.Collections.IEnumerable)payload["waypoints"])
                {
                    if (wObj is Dictionary<string, object>)
                    {
                        Vector3? wpt = ParseVector3Dict((Dictionary<string, object>)wObj);
                        if (wpt.HasValue) waypoints.Add(wpt.Value);
                    }
                }
            }

            float moveSpeed = 1.4f;
            string speedKey = payload.ContainsKey("move_speed") ? "move_speed" : "speed";
            if (payload.ContainsKey(speedKey))
            {
                float spd;
                if (float.TryParse(Convert.ToString(payload[speedKey], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out spd))
                    moveSpeed = Math.Max(0.5f, Math.Min(4.0f, spd));
            }

            string arrivalBehavior = "WANDER";
            if (payload.ContainsKey("arrival_behavior") && payload["arrival_behavior"] != null)
            {
                string ab = Convert.ToString(payload["arrival_behavior"]).Trim().ToUpperInvariant();
                if (!string.IsNullOrEmpty(ab)) arrivalBehavior = ab;
            }

            string groupColor = "#38bdf8";
            if (payload.ContainsKey("color") && payload["color"] != null)
            {
                string col = Convert.ToString(payload["color"]).Trim();
                if (!string.IsNullOrEmpty(col)) groupColor = col;
            }

            bool despawnChkEnabled = false;
            if (payload.ContainsKey("despawn_checkpoint_enabled"))
                bool.TryParse(Convert.ToString(payload["despawn_checkpoint_enabled"]), out despawnChkEnabled);
            Vector3? despawnCheckpoint = null;
            if (payload.ContainsKey("despawn_checkpoint") && payload["despawn_checkpoint"] is Dictionary<string, object>)
                despawnCheckpoint = ParseVector3Dict((Dictionary<string, object>)payload["despawn_checkpoint"]);
            float despawnRadius = 8.0f;
            if (payload.ContainsKey("despawn_radius"))
            {
                float dr;
                if (float.TryParse(Convert.ToString(payload["despawn_radius"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out dr))
                    despawnRadius = Math.Max(2.0f, Math.Min(100.0f, dr));
            }

            bool contStream = true;
            if (payload.ContainsKey("continuous_stream"))
                bool.TryParse(Convert.ToString(payload["continuous_stream"]), out contStream);

            // If destination is specified, behavior defaults to ROUTE_TRAVEL
            if (explicitDestination.HasValue && behavior == "INDEPENDENT_WANDER")
            {
                behavior = "ROUTE_TRAVEL";
            }

            // Parse Models list
            List<ModelCatalogItem> catalog = new List<ModelCatalogItem>();
            string primaryModel = "a_m_y_hipster_01";

            if (payload.ContainsKey("models") && payload["models"] is System.Collections.IEnumerable)
            {
                foreach (object itemObj in (System.Collections.IEnumerable)payload["models"])
                {
                    if (itemObj is Dictionary<string, object>)
                    {
                        Dictionary<string, object> mDict = (Dictionary<string, object>)itemObj;
                        string mName = mDict.ContainsKey("model") ? Convert.ToString(mDict["model"]).Trim() : "";
                        int weight = 50;
                        if (mDict.ContainsKey("weight"))
                        {
                            int w;
                            if (int.TryParse(Convert.ToString(mDict["weight"]), out w)) weight = Math.Max(1, w);
                        }
                        if (!string.IsNullOrEmpty(mName))
                        {
                            catalog.Add(new ModelCatalogItem { ModelName = mName, Weight = weight });
                        }
                    }
                }
            }

            if (catalog.Count == 0)
            {
                if (payload.ContainsKey("model") && payload["model"] != null)
                {
                    string m = Convert.ToString(payload["model"]).Trim();
                    if (!string.IsNullOrEmpty(m)) primaryModel = m;
                }
                catalog.Add(new ModelCatalogItem { ModelName = primaryModel, Weight = 100 });
            }
            else
            {
                primaryModel = catalog[0].ModelName;
            }

            // Determine spawn center
            Vector3 centerPos = Vector3.Zero;
            if (explicitOrigin.HasValue)
            {
                centerPos = explicitOrigin.Value;
            }
            else
            {
                Player player = Game.Player;
                if (player != null && player.Character != null && player.Character.Exists())
                {
                    centerPos = player.Character.Position;
                }
                else
                {
                    centerPos = new Vector3(_experiment.CenterX, _experiment.CenterY, _experiment.CenterZ);
                }
            }

            string groupId = "";
            if (payload.ContainsKey("group_id") && !string.IsNullOrEmpty(Convert.ToString(payload["group_id"])))
            {
                groupId = Convert.ToString(payload["group_id"]).Trim();
            }
            else if (payload.ContainsKey("id") && !string.IsNullOrEmpty(Convert.ToString(payload["id"])))
            {
                groupId = Convert.ToString(payload["id"]).Trim();
            }
            else
            {
                groupId = "grp_" + DateTime.UtcNow.Ticks;
            }

            bool grpVehClean = false;
            if (payload.ContainsKey("vehicle_cleanup"))
            {
                bool.TryParse(Convert.ToString(payload["vehicle_cleanup"]), out grpVehClean);
            }
            float grpVehRad = 40.0f;
            if (payload.ContainsKey("vehicle_cleanup_radius"))
            {
                float.TryParse(Convert.ToString(payload["vehicle_cleanup_radius"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out grpVehRad);
            }
            grpVehRad = Math.Max(5.0f, Math.Min(300.0f, grpVehRad));
            string grpVehCenter = payload.ContainsKey("vehicle_cleanup_center") ? Convert.ToString(payload["vehicle_cleanup_center"]).Trim().ToUpperInvariant() : "ORIGIN";

            bool spawnNow = true;
            if (payload.ContainsKey("spawn")) bool.TryParse(Convert.ToString(payload["spawn"]), out spawnNow);
            bool restartNow = false;
            if (payload.ContainsKey("restart")) bool.TryParse(Convert.ToString(payload["restart"]), out restartNow);
            if (restartNow) spawnNow = true;

            CrowdGroup grp = null;
            lock (_lock)
            {
                if (_groups.ContainsKey(groupId))
                {
                    grp = _groups[groupId];
                    string sigBefore = RouteSignature(grp);
                    grp.Name = groupName;
                    grp.PrimaryModel = primaryModel;
                    grp.Models = catalog;
                    grp.TargetCount = targetCount;
                    grp.SpawnRadius = spawnRadius;
                    grp.MovementRadius = moveRadius;
                    grp.SpawnRate = spawnRate;
                    grp.Behavior = behavior;
                    grp.FollowDistance = followDistance;
                    grp.DensityAware = densityAware;
                    grp.DensityLimit = densityLimit;
                    grp.SpawnCenter = centerPos;
                    grp.Origin = explicitOrigin;
                    grp.OriginRadius = originRadius;
                    grp.Destination = explicitDestination;
                    grp.DestinationRadius = destRadius;
                    grp.RouteWaypoints = waypoints;
                    grp.MoveSpeed = moveSpeed;
                    grp.ArrivalBehavior = arrivalBehavior;
                    grp.Color = groupColor;
                    grp.VehicleCleanup = grpVehClean;
                    grp.VehicleCleanupRadius = grpVehRad;
                    grp.VehicleCleanupCenter = grpVehCenter;
                    grp.DespawnCheckpointEnabled = despawnChkEnabled;
                    grp.DespawnCheckpoint = despawnCheckpoint;
                    grp.DespawnRadius = despawnRadius;
                    grp.ContinuousStream = contStream;

                    if (RouteSignature(grp) != sigBefore) grp.RouteVersion++;

                    int alive = grp.MemberHandles.Count;
                    if (restartNow)
                    {
                        RestartGroupLocked(grp);
                    }
                    else if (spawnNow || grp.Status == "ACTIVE" || grp.Status == "SPAWNING")
                    {
                        if (targetCount > alive)
                        {
                            grp.PendingCount = targetCount - alive;
                            grp.Status = "SPAWNING";
                        }
                        else
                        {
                            grp.PendingCount = 0;
                            grp.Status = "ACTIVE";
                        }
                    }
                    // else: config-only sync of a paused/stopped/configured group - leave state untouched
                }
                else
                {
                    grp = new CrowdGroup
                    {
                        GroupId = groupId,
                        Name = groupName,
                        PrimaryModel = primaryModel,
                        Models = catalog,
                        TargetCount = targetCount,
                        SpawnedCount = 0,
                        FailedCount = 0,
                        PendingCount = spawnNow ? targetCount : 0,
                        SpawnRadius = spawnRadius,
                        MovementRadius = moveRadius,
                        SpawnRate = spawnRate,
                        Behavior = behavior,
                        FollowDistance = followDistance,
                        DensityAware = densityAware,
                        DensityLimit = densityLimit,
                        Status = spawnNow ? "SPAWNING" : "CONFIGURED",
                        CreatedAt = DateTime.UtcNow,
                        SpawnCenter = centerPos,
                        Origin = explicitOrigin,
                        OriginRadius = originRadius,
                        Destination = explicitDestination,
                        DestinationRadius = destRadius,
                        RouteWaypoints = waypoints,
                        MoveSpeed = moveSpeed,
                        ArrivalBehavior = arrivalBehavior,
                        Color = groupColor,
                        VehicleCleanup = grpVehClean,
                        VehicleCleanupRadius = grpVehRad,
                        VehicleCleanupCenter = grpVehCenter,
                        DespawnCheckpointEnabled = despawnChkEnabled,
                        DespawnCheckpoint = despawnCheckpoint,
                        DespawnRadius = despawnRadius,
                        ContinuousStream = contStream,
                        ExitedCount = 0
                    };
                    _groups[groupId] = grp;
                }
            }

            if (restartNow && grp.VehicleCleanup && grp.Origin.HasValue && _experiment.State == "RUNNING")
            {
                PerformSafeVehicleCleanup(grp.Origin.Value.X, grp.Origin.Value.Y, grp.VehicleCleanupRadius);
            }

            Log(string.Format("SUCCESS: Created/synced group {0} ('{1}') - Target: {2}, Behavior: {3}, Origin: ({4},{5}), Dest: ({6},{7}), Speed: {8}",
                groupId, groupName, targetCount, behavior,
                explicitOrigin.HasValue ? Math.Round(explicitOrigin.Value.X, 1).ToString() : "N/A",
                explicitOrigin.HasValue ? Math.Round(explicitOrigin.Value.Y, 1).ToString() : "N/A",
                explicitDestination.HasValue ? Math.Round(explicitDestination.Value.X, 1).ToString() : "N/A",
                explicitDestination.HasValue ? Math.Round(explicitDestination.Value.Y, 1).ToString() : "N/A",
                moveSpeed));

            Dictionary<string, object> ackData = new Dictionary<string, object>();
            ackData["request_id"] = cmd.RequestId;
            ackData["command"] = cmd.Command;
            ackData["status"] = "ACK";
            ackData["group_id"] = groupId;
            ackData["name"] = groupName;
            ackData["target_count"] = targetCount;
            ackData["group_status"] = grp.Status;
            ackData["game_time"] = Game.GameTime;
            ackData["timestamp_utc"] = DateTime.UtcNow.ToString("o");

            EnqueueAck(ackData);
        }

        private void ProcessGetGroupsCommand(CommandItem cmd)
        {
            List<Dictionary<string, object>> groupList = new List<Dictionary<string, object>>();
            int totalActivePeds = 0;
            int totalPendingReservations = 0;

            lock (_lock)
            {
                totalActivePeds = _crowdRegistry.Count;

                foreach (CrowdGroup grp in _groups.Values)
                {
                    totalPendingReservations += grp.PendingCount;
                    groupList.Add(SerializeGroup(grp));
                }
            }

            Dictionary<string, object> ackData = new Dictionary<string, object>();
            ackData["request_id"] = cmd.RequestId;
            ackData["command"] = cmd.Command;
            ackData["status"] = "ACK";
            ackData["groups"] = groupList;
            ackData["total_alive"] = totalActivePeds;
            ackData["total_pending"] = totalPendingReservations;
            ackData["total_active_crowd_peds"] = totalActivePeds;
            ackData["total_pending_reservations"] = totalPendingReservations;
            ackData["max_total_population"] = MaxTotalPopulation;
            ackData["max_group_population"] = MaxGroupPopulation;
            ackData["game_time"] = Game.GameTime;
            ackData["timestamp_utc"] = DateTime.UtcNow.ToString("o");

            EnqueueAck(ackData);
        }

        private void ProcessGetGroupStatusCommand(CommandItem cmd)
        {
            string groupId = (cmd.Payload != null && cmd.Payload.ContainsKey("group_id")) ? Convert.ToString(cmd.Payload["group_id"]).Trim() : "";
            CrowdGroup grp = null;

            lock (_lock)
            {
                if (_groups.ContainsKey(groupId))
                {
                    grp = _groups[groupId];
                }
            }

            if (grp == null)
            {
                SendErrorAck(cmd, string.Format("Group with ID '{0}' not found.", groupId));
                return;
            }

            Dictionary<string, object> ackData = new Dictionary<string, object>();
            ackData["request_id"] = cmd.RequestId;
            ackData["command"] = cmd.Command;
            ackData["status"] = "ACK";
            ackData["group"] = SerializeGroup(grp);
            ackData["group_status"] = grp.Status;
            ackData["game_time"] = Game.GameTime;
            ackData["timestamp_utc"] = DateTime.UtcNow.ToString("o");

            EnqueueAck(ackData);
        }

        private void ProcessRemoveGroupCommand(CommandItem cmd)
        {
            string groupId = (cmd.Payload != null && cmd.Payload.ContainsKey("group_id")) ? Convert.ToString(cmd.Payload["group_id"]).Trim() : "";
            CrowdGroup grp = null;

            lock (_lock)
            {
                if (_groups.ContainsKey(groupId))
                {
                    grp = _groups[groupId];
                }
            }

            if (grp == null)
            {
                SendErrorAck(cmd, string.Format("Group '{0}' not found for removal.", groupId));
                return;
            }

            int clearedCount = 0;
            lock (_lock)
            {
                grp.PendingCount = 0;
                grp.Status = "REMOVED";
                ReleaseGroupModels(grp);

                for (int i = 0; i < grp.MemberHandles.Count; i++)
                {
                    try
                    {
                        Ped p = Entity.FromHandle(grp.MemberHandles[i]) as Ped;
                        if (p != null && p.Exists())
                        {
                            p.Delete();
                            clearedCount++;
                        }
                    }
                    catch { }
                }

                _crowdRegistry.RemoveAll(r => r.GroupId == groupId);
                grp.MemberHandles.Clear();
                _groups.Remove(groupId);
            }

            Log(string.Format("INFO: Removed group {0} ('{1}'). Cleared {2} entities.", groupId, grp.Name, clearedCount));

            Dictionary<string, object> ackData = new Dictionary<string, object>();
            ackData["request_id"] = cmd.RequestId;
            ackData["command"] = cmd.Command;
            ackData["status"] = "ACK";
            ackData["group_id"] = groupId;
            ackData["cleared_count"] = clearedCount;
            ackData["game_time"] = Game.GameTime;
            ackData["timestamp_utc"] = DateTime.UtcNow.ToString("o");

            EnqueueAck(ackData);
        }

        private void ProcessClearAllGroupsCommand(CommandItem cmd)
        {
            int totalCleared = 0;
            int groupsCleared = 0;

            lock (_lock)
            {
                groupsCleared = _groups.Count;
                foreach (CrowdGroup grp in _groups.Values)
                {
                    grp.PendingCount = 0;
                    grp.Status = "REMOVED";
                    ReleaseGroupModels(grp);

                    for (int i = 0; i < grp.MemberHandles.Count; i++)
                    {
                        try
                        {
                            Ped p = Entity.FromHandle(grp.MemberHandles[i]) as Ped;
                            if (p != null && p.Exists())
                            {
                                p.Delete();
                                totalCleared++;
                            }
                        }
                        catch { }
                    }
                    grp.MemberHandles.Clear();
                }

                _groups.Clear();
                _crowdRegistry.Clear();
                _currentHeatmapCells.Clear();
            }

            Log(string.Format("INFO: Cleared all groups ({0} groups, {1} entities deleted).", groupsCleared, totalCleared));

            Dictionary<string, object> ackData = new Dictionary<string, object>();
            ackData["request_id"] = cmd.RequestId;
            ackData["command"] = cmd.Command;
            ackData["status"] = "ACK";
            ackData["groups_cleared"] = groupsCleared;
            ackData["cleared_groups_count"] = groupsCleared;
            ackData["cleared_count"] = totalCleared;
            ackData["game_time"] = Game.GameTime;
            ackData["timestamp_utc"] = DateTime.UtcNow.ToString("o");

            EnqueueAck(ackData);
        }

        private void ProcessSetGroupLeaderCommand(CommandItem cmd)
        {
            string groupId = (cmd.Payload != null && cmd.Payload.ContainsKey("group_id")) ? Convert.ToString(cmd.Payload["group_id"]).Trim() : "";
            int leaderHandle = 0;
            if (cmd.Payload != null && cmd.Payload.ContainsKey("leader_handle"))
            {
                int.TryParse(Convert.ToString(cmd.Payload["leader_handle"]), out leaderHandle);
            }

            CrowdGroup grp = null;
            lock (_lock)
            {
                if (_groups.ContainsKey(groupId)) grp = _groups[groupId];
            }

            if (grp == null)
            {
                SendErrorAck(cmd, string.Format("Group '{0}' not found.", groupId));
                return;
            }

            Ped leaderPed = Entity.FromHandle(leaderHandle) as Ped;
            if (leaderPed == null || !leaderPed.Exists() || leaderPed.IsDead)
            {
                SendErrorAck(cmd, string.Format("Ped handle {0} does not exist or is dead.", leaderHandle));
                return;
            }

            grp.LeaderHandle = leaderHandle;
            Log(string.Format("INFO: Group {0} ('{1}') leader set to Ped #{2}", grp.GroupId, grp.Name, leaderHandle));

            Dictionary<string, object> ackData = new Dictionary<string, object>();
            ackData["request_id"] = cmd.RequestId;
            ackData["command"] = cmd.Command;
            ackData["status"] = "ACK";
            ackData["group_id"] = groupId;
            ackData["leader_handle"] = leaderHandle;
            ackData["game_time"] = Game.GameTime;
            ackData["timestamp_utc"] = DateTime.UtcNow.ToString("o");

            EnqueueAck(ackData);
        }

        private void ProcessSetExperimentCommand(CommandItem cmd)
        {
            Dictionary<string, object> p = cmd.Payload ?? new Dictionary<string, object>();

            lock (_lock)
            {
                if (p.ContainsKey("name") && p["name"] != null)
                {
                    string nm = Convert.ToString(p["name"]).Trim();
                    if (!string.IsNullOrEmpty(nm)) _experiment.Name = nm;
                }

                if (p.ContainsKey("area_type") && p["area_type"] != null)
                {
                    string at = Convert.ToString(p["area_type"]).Trim().ToUpperInvariant();
                    if (at == "CIRCLE" || at == "RECTANGLE") _experiment.AreaType = at;
                }

                if (p.ContainsKey("center_x"))
                {
                    float cx;
                    if (float.TryParse(Convert.ToString(p["center_x"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out cx))
                        _experiment.CenterX = cx;
                }
                if (p.ContainsKey("center_y"))
                {
                    float cy;
                    if (float.TryParse(Convert.ToString(p["center_y"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out cy))
                        _experiment.CenterY = cy;
                }
                if (p.ContainsKey("center_z"))
                {
                    float cz;
                    if (float.TryParse(Convert.ToString(p["center_z"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out cz))
                        _experiment.CenterZ = cz;
                }

                if (p.ContainsKey("width"))
                {
                    float w;
                    if (float.TryParse(Convert.ToString(p["width"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out w))
                        _experiment.Width = Math.Max(20f, Math.Min(2000f, w));
                }
                if (p.ContainsKey("height"))
                {
                    float h;
                    if (float.TryParse(Convert.ToString(p["height"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out h))
                        _experiment.Height = Math.Max(20f, Math.Min(2000f, h));
                }
                if (p.ContainsKey("radius"))
                {
                    float r;
                    if (float.TryParse(Convert.ToString(p["radius"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out r))
                        _experiment.Radius = Math.Max(10f, Math.Min(1000f, r));
                }

                if (p.ContainsKey("vehicle_cleanup"))
                {
                    bool vc;
                    if (bool.TryParse(Convert.ToString(p["vehicle_cleanup"]), out vc))
                        _experiment.VehicleCleanup = vc;
                }

                if (p.ContainsKey("grid_resolution"))
                {
                    float gr;
                    if (float.TryParse(Convert.ToString(p["grid_resolution"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out gr))
                        _experiment.GridResolution = Math.Max(5f, Math.Min(50f, gr));
                }

                if (p.ContainsKey("allow_outside_routing"))
                {
                    bool aor;
                    if (bool.TryParse(Convert.ToString(p["allow_outside_routing"]), out aor))
                        _experiment.AllowOutsideRouting = aor;
                }
            }

            Log(string.Format("INFO: Experiment '{0}' updated: Type={1}, Center=({2},{3}), Size={4}x{5}, R={6}, VehCleanup={7}, GridRes={8}m",
                _experiment.Name, _experiment.AreaType, _experiment.CenterX, _experiment.CenterY, _experiment.Width, _experiment.Height, _experiment.Radius, _experiment.VehicleCleanup, _experiment.GridResolution));

            Dictionary<string, object> ackData = new Dictionary<string, object>();
            ackData["request_id"] = cmd.RequestId;
            ackData["command"] = cmd.Command;
            ackData["status"] = "ACK";
            ackData["experiment"] = SerializeExperiment();
            ackData["game_time"] = Game.GameTime;
            ackData["timestamp_utc"] = DateTime.UtcNow.ToString("o");

            EnqueueAck(ackData);
        }

        private void ProcessStartExperimentCommand(CommandItem cmd)
        {
            bool validateOnly = false;
            if (cmd.Payload != null && cmd.Payload.ContainsKey("validate_only"))
            {
                bool.TryParse(Convert.ToString(cmd.Payload["validate_only"]), out validateOnly);
            }

            // Validation checks
            List<string> validationWarnings = new List<string>();
            List<string> validationErrors = new List<string>();

            lock (_lock)
            {
                if (_groups.Count == 0)
                {
                    validationWarnings.Add("No pedestrian groups configured in experiment.");
                }

                foreach (CrowdGroup grp in _groups.Values)
                {
                    if (!_experiment.AllowOutsideRouting)
                    {
                        if (grp.Origin.HasValue && !IsInsideExperimentArea(grp.Origin.Value))
                        {
                            validationWarnings.Add(string.Format("Group '{0}' origin ({1},{2}) is outside experiment area.", grp.Name, Math.Round(grp.Origin.Value.X, 1), Math.Round(grp.Origin.Value.Y, 1)));
                        }
                        if (grp.Destination.HasValue && !IsInsideExperimentArea(grp.Destination.Value))
                        {
                            validationWarnings.Add(string.Format("Group '{0}' destination ({1},{2}) is outside experiment area.", grp.Name, Math.Round(grp.Destination.Value.X, 1), Math.Round(grp.Destination.Value.Y, 1)));
                        }
                    }
                }
            }

            if (validationErrors.Count > 0)
            {
                SendErrorAck(cmd, "Validation failed: " + string.Join("; ", validationErrors.ToArray()));
                return;
            }

            if (validateOnly)
            {
                Dictionary<string, object> valAck = new Dictionary<string, object>();
                valAck["request_id"] = cmd.RequestId;
                valAck["command"] = cmd.Command;
                valAck["status"] = "ACK";
                valAck["validated"] = true;
                valAck["warnings"] = validationWarnings;
                valAck["experiment"] = SerializeExperiment();
                valAck["game_time"] = Game.GameTime;
                valAck["timestamp_utc"] = DateTime.UtcNow.ToString("o");
                EnqueueAck(valAck);
                return;
            }

            // Start Experiment execution
            int vehiclesRemoved = 0;
            if (_experiment.VehicleCleanup)
            {
                vehiclesRemoved = PerformSafeVehicleCleanup();
            }

            lock (_lock)
            {
                _experiment.State = "RUNNING";

                // Resume or start spawning for groups
                foreach (CrowdGroup grp in _groups.Values)
                {
                    if (grp.Status == "PAUSED" || grp.Status == "STOPPED" || grp.Status == "CONFIGURED" || grp.Status == "COMPLETED" || grp.Status == "ERROR")
                    {
                        int alive = grp.MemberHandles.Count;
                        if (grp.TargetCount > alive)
                        {
                            grp.PendingCount = grp.TargetCount - alive;
                            grp.Status = "SPAWNING";
                        }
                        else
                        {
                            grp.Status = "ACTIVE";
                        }
                    }
                }
            }

            Log(string.Format("SUCCESS: Experiment '{0}' STARTED. Running groups: {1}, Ambient vehicles removed: {2}",
                _experiment.Name, _groups.Count, vehiclesRemoved));

            Notification.PostTicker(string.Format("~g~[CrowdSim]~s~ Experiment '{0}' STARTED", _experiment.Name), false, true);

            Dictionary<string, object> ackData = new Dictionary<string, object>();
            ackData["request_id"] = cmd.RequestId;
            ackData["command"] = cmd.Command;
            ackData["status"] = "ACK";
            ackData["experiment_state"] = _experiment.State;
            ackData["vehicles_cleaned"] = vehiclesRemoved;
            ackData["warnings"] = validationWarnings;
            ackData["experiment"] = SerializeExperiment();
            ackData["game_time"] = Game.GameTime;
            ackData["timestamp_utc"] = DateTime.UtcNow.ToString("o");

            EnqueueAck(ackData);
        }

        private void ProcessPauseExperimentCommand(CommandItem cmd)
        {
            lock (_lock)
            {
                _experiment.State = "PAUSED";
            }

            Log(string.Format("INFO: Experiment '{0}' PAUSED.", _experiment.Name));
            Notification.PostTicker("~y~[CrowdSim]~s~ Experiment PAUSED", false, true);

            Dictionary<string, object> ackData = new Dictionary<string, object>();
            ackData["request_id"] = cmd.RequestId;
            ackData["command"] = cmd.Command;
            ackData["status"] = "ACK";
            ackData["experiment_state"] = _experiment.State;
            ackData["game_time"] = Game.GameTime;
            ackData["timestamp_utc"] = DateTime.UtcNow.ToString("o");

            EnqueueAck(ackData);
        }

        private void ProcessResumeExperimentCommand(CommandItem cmd)
        {
            lock (_lock)
            {
                _experiment.State = "RUNNING";
            }

            Log(string.Format("INFO: Experiment '{0}' RESUMED.", _experiment.Name));
            Notification.PostTicker("~g~[CrowdSim]~s~ Experiment RESUMED", false, true);

            Dictionary<string, object> ackData = new Dictionary<string, object>();
            ackData["request_id"] = cmd.RequestId;
            ackData["command"] = cmd.Command;
            ackData["status"] = "ACK";
            ackData["experiment_state"] = _experiment.State;
            ackData["game_time"] = Game.GameTime;
            ackData["timestamp_utc"] = DateTime.UtcNow.ToString("o");

            EnqueueAck(ackData);
        }

        private void ProcessStopExperimentCommand(CommandItem cmd)
        {
            bool clearPeds = false;
            if (cmd.Payload != null && cmd.Payload.ContainsKey("clear_peds"))
            {
                bool.TryParse(Convert.ToString(cmd.Payload["clear_peds"]), out clearPeds);
            }

            int pedsCleared = 0;
            lock (_lock)
            {
                _experiment.State = "STOPPED";

                foreach (CrowdGroup grp in _groups.Values)
                {
                    grp.PendingCount = 0;
                    grp.Status = "STOPPED";
                    ReleaseGroupModels(grp);
                }

                if (clearPeds)
                {
                    for (int i = 0; i < _crowdRegistry.Count; i++)
                    {
                        try
                        {
                            Ped p = Entity.FromHandle(_crowdRegistry[i].Handle) as Ped;
                            if (p != null && p.Exists())
                            {
                                p.Delete();
                                pedsCleared++;
                            }
                        }
                        catch { }
                    }
                    _crowdRegistry.Clear();
                    _currentHeatmapCells.Clear();
                }
            }

            Log(string.Format("INFO: Experiment '{0}' STOPPED (PedsCleared: {1}).", _experiment.Name, pedsCleared));
            Notification.PostTicker("~r~[CrowdSim]~s~ Experiment STOPPED", false, true);

            Dictionary<string, object> ackData = new Dictionary<string, object>();
            ackData["request_id"] = cmd.RequestId;
            ackData["command"] = cmd.Command;
            ackData["status"] = "ACK";
            ackData["experiment_state"] = _experiment.State;
            ackData["peds_cleared"] = pedsCleared;
            ackData["game_time"] = Game.GameTime;
            ackData["timestamp_utc"] = DateTime.UtcNow.ToString("o");

            EnqueueAck(ackData);
        }

        private void ProcessResetExperimentCommand(CommandItem cmd)
        {
            int pedsCleared = 0;
            int groupsCleared = 0;

            lock (_lock)
            {
                _experiment.State = "STOPPED";
                groupsCleared = _groups.Count;

                foreach (CrowdGroup grp in _groups.Values)
                {
                    ReleaseGroupModels(grp);
                    grp.MemberHandles.Clear();
                }
                _groups.Clear();

                for (int i = 0; i < _crowdRegistry.Count; i++)
                {
                    try
                    {
                        Ped p = Entity.FromHandle(_crowdRegistry[i].Handle) as Ped;
                        if (p != null && p.Exists())
                        {
                            p.Delete();
                            pedsCleared++;
                        }
                    }
                    catch { }
                }
                _crowdRegistry.Clear();
                _currentHeatmapCells.Clear();
            }

            Log(string.Format("INFO: Experiment RESET. Groups cleared: {0}, Peds deleted: {1}", groupsCleared, pedsCleared));

            Dictionary<string, object> ackData = new Dictionary<string, object>();
            ackData["request_id"] = cmd.RequestId;
            ackData["command"] = cmd.Command;
            ackData["status"] = "ACK";
            ackData["experiment_state"] = _experiment.State;
            ackData["groups_cleared"] = groupsCleared;
            ackData["peds_cleared"] = pedsCleared;
            ackData["game_time"] = Game.GameTime;
            ackData["timestamp_utc"] = DateTime.UtcNow.ToString("o");

            EnqueueAck(ackData);
        }

        private void ProcessCleanupVehiclesCommand(CommandItem cmd)
        {
            Dictionary<string, object> p = cmd.Payload ?? new Dictionary<string, object>();
            float? cx = null;
            float? cy = null;
            float? rad = null;

            if (p.ContainsKey("center_x") && p["center_x"] != null)
            {
                float val;
                if (float.TryParse(Convert.ToString(p["center_x"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out val))
                    cx = val;
            }
            if (p.ContainsKey("center_y") && p["center_y"] != null)
            {
                float val;
                if (float.TryParse(Convert.ToString(p["center_y"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out val))
                    cy = val;
            }
            if (p.ContainsKey("radius") && p["radius"] != null)
            {
                float val;
                if (float.TryParse(Convert.ToString(p["radius"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out val))
                    rad = Math.Max(5.0f, Math.Min(500.0f, val));
            }

            int removed = PerformSafeVehicleCleanup(cx, cy, rad);

            Dictionary<string, object> ackData = new Dictionary<string, object>();
            ackData["request_id"] = cmd.RequestId;
            ackData["command"] = cmd.Command;
            ackData["status"] = "ACK";
            ackData["cleared_vehicles_count"] = removed;
            if (cx.HasValue) ackData["center_x"] = cx.Value;
            if (cy.HasValue) ackData["center_y"] = cy.Value;
            if (rad.HasValue) ackData["radius"] = rad.Value;
            ackData["game_time"] = Game.GameTime;
            ackData["timestamp_utc"] = DateTime.UtcNow.ToString("o");

            EnqueueAck(ackData);
        }

        private void ProcessUpdateGroupCommand(CommandItem cmd)
        {
            Dictionary<string, object> payload = cmd.Payload ?? new Dictionary<string, object>();
            string groupId = payload.ContainsKey("group_id") ? Convert.ToString(payload["group_id"]).Trim() : "";
            if (string.IsNullOrEmpty(groupId) && payload.ContainsKey("id"))
            {
                groupId = Convert.ToString(payload["id"]).Trim();
            }

            if (string.IsNullOrEmpty(groupId))
            {
                SendErrorAck(cmd, "Missing 'group_id' in UPDATE_GROUP payload.");
                return;
            }

            lock (_lock)
            {
                if (!_groups.ContainsKey(groupId))
                {
                    SendErrorAck(cmd, string.Format("Group '{0}' not found for update.", groupId));
                    return;
                }

                CrowdGroup grp = _groups[groupId];
                string sigBefore = RouteSignature(grp);

                if (payload.ContainsKey("name") && payload["name"] != null)
                {
                    string nm = Convert.ToString(payload["name"]).Trim();
                    if (!string.IsNullOrEmpty(nm)) grp.Name = nm;
                }

                if (payload.ContainsKey("color") && payload["color"] != null)
                {
                    grp.Color = Convert.ToString(payload["color"]).Trim();
                }

                if (payload.ContainsKey("count") && payload["count"] != null)
                {
                    int c;
                    if (int.TryParse(Convert.ToString(payload["count"]), out c))
                    {
                        int newTarget = Math.Max(1, Math.Min(MaxGroupPopulation, c));
                        grp.TargetCount = newTarget;
                        int alive = grp.MemberHandles.Count;
                        if (newTarget > alive)
                        {
                            grp.PendingCount = newTarget - alive;
                            if (grp.Status != "PAUSED" && grp.Status != "STOPPED")
                            {
                                grp.Status = "SPAWNING";
                            }
                        }
                        else
                        {
                            grp.PendingCount = 0;
                            if (grp.Status == "SPAWNING")
                            {
                                grp.Status = "ACTIVE";
                            }
                        }
                    }
                }

                if (payload.ContainsKey("spawn_rate"))
                {
                    float sr;
                    if (float.TryParse(Convert.ToString(payload["spawn_rate"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out sr))
                        grp.SpawnRate = Math.Max(0.5f, Math.Min(100.0f, sr));
                }

                if (payload.ContainsKey("spawn_radius"))
                {
                    float srad;
                    if (float.TryParse(Convert.ToString(payload["spawn_radius"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out srad))
                    {
                        grp.SpawnRadius = Math.Max(2.0f, Math.Min(150.0f, srad));
                        grp.OriginRadius = grp.SpawnRadius;
                    }
                }

                if (payload.ContainsKey("origin") && payload["origin"] is Dictionary<string, object>)
                {
                    grp.Origin = ParseVector3Dict((Dictionary<string, object>)payload["origin"]);
                    if (grp.Origin.HasValue) grp.SpawnCenter = grp.Origin.Value;
                }

                if (payload.ContainsKey("origin_radius"))
                {
                    float orad;
                    if (float.TryParse(Convert.ToString(payload["origin_radius"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out orad))
                        grp.OriginRadius = Math.Max(2.0f, Math.Min(100.0f, orad));
                }

                if (payload.ContainsKey("destination") && payload["destination"] is Dictionary<string, object>)
                {
                    grp.Destination = ParseVector3Dict((Dictionary<string, object>)payload["destination"]);
                }

                if (payload.ContainsKey("destination_radius"))
                {
                    float dr;
                    if (float.TryParse(Convert.ToString(payload["destination_radius"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out dr))
                        grp.DestinationRadius = Math.Max(2.0f, Math.Min(100.0f, dr));
                }

                string updSpeedKey = payload.ContainsKey("move_speed") ? "move_speed" : "speed";
                if (payload.ContainsKey(updSpeedKey))
                {
                    float spd;
                    if (float.TryParse(Convert.ToString(payload[updSpeedKey], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out spd))
                        grp.MoveSpeed = Math.Max(0.5f, Math.Min(4.0f, spd));
                }

                if (payload.ContainsKey("behavior") && payload["behavior"] != null)
                {
                    string b = Convert.ToString(payload["behavior"]).Trim().ToUpperInvariant();
                    if (!string.IsNullOrEmpty(b)) grp.Behavior = b;
                }

                if (payload.ContainsKey("arrival_behavior") && payload["arrival_behavior"] != null)
                {
                    string ab = Convert.ToString(payload["arrival_behavior"]).Trim().ToUpperInvariant();
                    if (!string.IsNullOrEmpty(ab)) grp.ArrivalBehavior = ab;
                }

                                if (payload.ContainsKey("despawn_checkpoint_enabled"))
                {
                    bool dce;
                    if (bool.TryParse(Convert.ToString(payload["despawn_checkpoint_enabled"]), out dce))
                        grp.DespawnCheckpointEnabled = dce;
                }

                if (payload.ContainsKey("despawn_checkpoint") && payload["despawn_checkpoint"] is Dictionary<string, object>)
                {
                    grp.DespawnCheckpoint = ParseVector3Dict((Dictionary<string, object>)payload["despawn_checkpoint"]);
                }

                if (payload.ContainsKey("despawn_radius"))
                {
                    float dcr;
                    if (float.TryParse(Convert.ToString(payload["despawn_radius"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out dcr))
                        grp.DespawnRadius = Math.Max(2.0f, Math.Min(100.0f, dcr));
                }

                if (payload.ContainsKey("continuous_stream"))
                {
                    bool cs;
                    if (bool.TryParse(Convert.ToString(payload["continuous_stream"]), out cs))
                        grp.ContinuousStream = cs;
                }

                if (payload.ContainsKey("density_aware"))
                {
                    bool da;
                    if (bool.TryParse(Convert.ToString(payload["density_aware"]), out da))
                        grp.DensityAware = da;
                }

                if (payload.ContainsKey("vehicle_cleanup"))
                {
                    bool vc;
                    if (bool.TryParse(Convert.ToString(payload["vehicle_cleanup"]), out vc))
                        grp.VehicleCleanup = vc;
                }

                if (payload.ContainsKey("vehicle_cleanup_radius"))
                {
                    float vcr;
                    if (float.TryParse(Convert.ToString(payload["vehicle_cleanup_radius"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out vcr))
                        grp.VehicleCleanupRadius = Math.Max(5.0f, Math.Min(300.0f, vcr));
                }

                if (payload.ContainsKey("vehicle_cleanup_center") && payload["vehicle_cleanup_center"] != null)
                {
                    grp.VehicleCleanupCenter = Convert.ToString(payload["vehicle_cleanup_center"]).Trim().ToUpperInvariant();
                }

                if (payload.ContainsKey("waypoints") && payload["waypoints"] is System.Collections.IEnumerable)
                {
                    List<Vector3> wps = new List<Vector3>();
                    foreach (object wObj in (System.Collections.IEnumerable)payload["waypoints"])
                    {
                        if (wObj is Dictionary<string, object>)
                        {
                            Vector3? wpVec = ParseVector3Dict((Dictionary<string, object>)wObj);
                            if (wpVec.HasValue) wps.Add(wpVec.Value);
                        }
                    }
                    grp.RouteWaypoints = wps;
                }

                if (payload.ContainsKey("status") && payload["status"] != null)
                {
                    string st = Convert.ToString(payload["status"]).Trim().ToUpperInvariant();
                    if (st == "PAUSED" || st == "SPAWNING" || st == "ACTIVE" || st == "DISABLED")
                    {
                        grp.Status = st;
                    }
                }

                if (RouteSignature(grp) != sigBefore) grp.RouteVersion++;

                Log(string.Format("INFO: Group '{0}' ({1}) updated successfully.", grp.Name, grp.GroupId));

                Dictionary<string, object> ackData = new Dictionary<string, object>();
                ackData["request_id"] = cmd.RequestId;
                ackData["command"] = cmd.Command;
                ackData["status"] = "ACK";
                ackData["group"] = SerializeGroup(grp);
                ackData["game_time"] = Game.GameTime;
                ackData["timestamp_utc"] = DateTime.UtcNow.ToString("o");
                EnqueueAck(ackData);
            }
        }

        private void ProcessStartGroupCommand(CommandItem cmd)
        {
            Dictionary<string, object> payload = cmd.Payload ?? new Dictionary<string, object>();
            string groupId = payload.ContainsKey("group_id") ? Convert.ToString(payload["group_id"]).Trim() : "";
            if (string.IsNullOrEmpty(groupId) && payload.ContainsKey("id"))
            {
                groupId = Convert.ToString(payload["id"]).Trim();
            }

            bool restart = false;
            if (payload.ContainsKey("restart")) bool.TryParse(Convert.ToString(payload["restart"]), out restart);

            CrowdGroup cleanupGrp = null;
            lock (_lock)
            {
                if (!_groups.ContainsKey(groupId))
                {
                    SendErrorAck(cmd, string.Format("Group '{0}' not found to start.", groupId));
                    return;
                }

                CrowdGroup grp = _groups[groupId];

                // A group Spawn must work on its own, without requiring the top-level experiment Start first.
                if (_experiment.State != "RUNNING")
                {
                    _experiment.State = "RUNNING";
                }

                int alive = grp.MemberHandles.Count;
                if (restart)
                {
                    RestartGroupLocked(grp);
                    cleanupGrp = grp;
                }
                else if (grp.TargetCount > alive)
                {
                    grp.PendingCount = grp.TargetCount - alive;
                    grp.Status = "SPAWNING";
                }
                else
                {
                    grp.PendingCount = 0;
                    grp.Status = "ACTIVE";
                }

                Log(string.Format("INFO: Group '{0}' ({1}) started/resumed (Restart: {2}, Status: {3}, Alive: {4}, Target: {5}, Pending: {6}, HasRoute: {7}).",
                    grp.Name, grp.GroupId, restart, grp.Status, grp.MemberHandles.Count, grp.TargetCount, grp.PendingCount, HasRoute(grp)));

                Dictionary<string, object> ackData = new Dictionary<string, object>();
                ackData["request_id"] = cmd.RequestId;
                ackData["command"] = cmd.Command;
                ackData["status"] = "ACK";
                ackData["group"] = SerializeGroup(grp);
                ackData["game_time"] = Game.GameTime;
                ackData["timestamp_utc"] = DateTime.UtcNow.ToString("o");
                EnqueueAck(ackData);
            }

            if (cleanupGrp != null && cleanupGrp.VehicleCleanup && cleanupGrp.Origin.HasValue)
            {
                PerformSafeVehicleCleanup(cleanupGrp.Origin.Value.X, cleanupGrp.Origin.Value.Y, cleanupGrp.VehicleCleanupRadius);
            }
        }

        private void ProcessPauseGroupCommand(CommandItem cmd)
        {
            Dictionary<string, object> payload = cmd.Payload ?? new Dictionary<string, object>();
            string groupId = payload.ContainsKey("group_id") ? Convert.ToString(payload["group_id"]).Trim() : "";

            lock (_lock)
            {
                if (!_groups.ContainsKey(groupId))
                {
                    SendErrorAck(cmd, string.Format("Group '{0}' not found to pause.", groupId));
                    return;
                }

                CrowdGroup grp = _groups[groupId];
                grp.Status = "PAUSED";

                Log(string.Format("INFO: Group '{0}' paused.", grp.Name));

                Dictionary<string, object> ackData = new Dictionary<string, object>();
                ackData["request_id"] = cmd.RequestId;
                ackData["command"] = cmd.Command;
                ackData["status"] = "ACK";
                ackData["group"] = SerializeGroup(grp);
                ackData["game_time"] = Game.GameTime;
                ackData["timestamp_utc"] = DateTime.UtcNow.ToString("o");
                EnqueueAck(ackData);
            }
        }

        private void ProcessGetTelemetryCommand(CommandItem cmd)
        {
            Player player = Game.Player;
            Vector3 playerPos = (player != null && player.Character != null) ? player.Character.Position : Vector3.Zero;
            float heading = (player != null && player.Character != null) ? player.Character.Heading : 0f;

            Dictionary<string, object> playerDict = new Dictionary<string, object>();
            playerDict["x"] = Math.Round(playerPos.X, 2);
            playerDict["y"] = Math.Round(playerPos.Y, 2);
            playerDict["z"] = Math.Round(playerPos.Z, 2);
            playerDict["heading"] = Math.Round(heading, 1);
            playerDict["god_mode"] = _godModeEnabled;
            playerDict["never_wanted"] = _neverWantedEnabled;
            playerDict["noclip"] = _noclipEnabled;
            playerDict["prop_builder"] = _propBuilderEnabled;
            playerDict["wanted_level"] = player != null ? player.WantedLevel : 0;

            List<Dictionary<string, object>> groupList = new List<Dictionary<string, object>>();
            List<Dictionary<string, object>> pedList = new List<Dictionary<string, object>>();
            List<Dictionary<string, object>> heatmapList = new List<Dictionary<string, object>>();

            lock (_lock)
            {
                foreach (CrowdGroup grp in _groups.Values)
                {
                    groupList.Add(SerializeGroup(grp));
                }

                // Sample up to 100 live ped positions for live map dots
                int sampleCap = Math.Min(100, _crowdRegistry.Count);
                for (int i = 0; i < sampleCap; i++)
                {
                    CrowdPedRecord rec = _crowdRegistry[i];
                    Ped p = Entity.FromHandle(rec.Handle) as Ped;
                    if (p != null && p.Exists() && !p.IsDead)
                    {
                        Vector3 pp = p.Position;
                        Dictionary<string, object> pd = new Dictionary<string, object>();
                        pd["handle"] = rec.Handle;
                        pd["group_id"] = rec.GroupId;
                        pd["x"] = Math.Round(pp.X, 2);
                        pd["y"] = Math.Round(pp.Y, 2);
                        pd["z"] = Math.Round(pp.Z, 2);
                        if (_groups.ContainsKey(rec.GroupId)) pd["color"] = _groups[rec.GroupId].Color;
                        pedList.Add(pd);
                    }
                }

                // Heatmap cells
                for (int i = 0; i < _currentHeatmapCells.Count; i++)
                {
                    HeatmapCell c = _currentHeatmapCells[i];
                    Dictionary<string, object> cd = new Dictionary<string, object>();
                    cd["col"] = c.Col;
                    cd["row"] = c.Row;
                    cd["x"] = c.X;
                    cd["y"] = c.Y;
                    cd["count"] = c.Count;
                    cd["group_counts"] = c.GroupCounts;
                    heatmapList.Add(cd);
                }
            }

            Dictionary<string, object> heatmapDict = new Dictionary<string, object>();
            heatmapDict["grid_resolution"] = _experiment.GridResolution;
            heatmapDict["cells"] = heatmapList;
            heatmapDict["sample_time"] = DateTime.UtcNow.ToString("o");

            Dictionary<string, object> ackData = new Dictionary<string, object>();
            ackData["request_id"] = cmd.RequestId;
            ackData["command"] = cmd.Command;
            ackData["status"] = "ACK";
            ackData["player"] = playerDict;
            ackData["experiment"] = SerializeExperiment();
            ackData["groups"] = groupList;
            ackData["heatmap"] = heatmapDict;
            ackData["pedestrians"] = pedList;
            ackData["props"] = GetSerializedCustomPropsList();
            ackData["total_managed_peds"] = _crowdRegistry.Count;
            ackData["game_time"] = Game.GameTime;
            ackData["timestamp_utc"] = DateTime.UtcNow.ToString("o");

            EnqueueAck(ackData);
        }

        #endregion

        #region Spawning State Machine & Global Scheduler

        private void TickSpawningGroups()
        {
            List<CrowdGroup> spawningGroups = new List<CrowdGroup>();
            foreach (CrowdGroup g in _groups.Values)
            {
                if (g.Status == "SPAWNING")
                {
                    spawningGroups.Add(g);
                }
            }

            if (spawningGroups.Count == 0) return;

            int spawnsRemainingBudget = GlobalSpawnBudgetPerTick;
            int totalGroups = spawningGroups.Count;

            for (int step = 0; step < totalGroups && spawnsRemainingBudget > 0; step++)
            {
                int groupIdx = (_spawningRoundRobinIndex + step) % totalGroups;
                CrowdGroup grp = spawningGroups[groupIdx];

                if (grp.PendingCount <= 0) continue;

                // Rate limiting check
                double spawnIntervalSec = 1.0 / Math.Max(1.0, grp.SpawnRate);
                if ((DateTime.UtcNow - grp.LastSpawnTime).TotalSeconds < spawnIntervalSec)
                {
                    continue;
                }

                // Global population & engine concurrent safety check:
                // Allows scaling up to MaxTotalPopulation when running with an expanded engine ped pool.
                // Global population & engine concurrent safety check:
                // Keeping concurrent living peds at 240 ensures total engine entities (240 + player) = 241 <= 255,
                // completely preventing the 256 stack-buffer overflow in GTA5.exe.
                // In Continuous Stream mode, peds exit at destination and immediately recycle at origin,
                // allowing thousands of peds to flow through the scene with 100% stability.
                int currentTotal;
                lock (_lock) { currentTotal = _crowdRegistry.Count; }
                if (currentTotal >= 240)
                {
                    grp.LastSpawnTime = DateTime.UtcNow.AddSeconds(0.5);
                    break;
                }

                // Stage 3C Asynchronous Streaming State Machine
                string chosenModel = PickModelFromCatalog(grp.Models, grp.PrimaryModel);

                if (!grp.ModelPool.ContainsKey(chosenModel))
                {
                    grp.ModelPool[chosenModel] = new Model(chosenModel);
                    grp.ModelRequestedPool[chosenModel] = false;
                    grp.ModelLoadedPool[chosenModel] = false;
                    grp.ModelRequestStartPool[chosenModel] = DateTime.MinValue;
                }

                Model m = grp.ModelPool[chosenModel];

                if (!m.IsValid)
                {
                    Log(string.Format("WARN: Model '{0}' in group {1} is invalid. Marking ped failed.", chosenModel, grp.GroupId));
                    grp.FailedCount++;
                    grp.PendingCount--;
                    continue;
                }

                if (!grp.ModelLoadedPool[chosenModel])
                {
                    if (!grp.ModelRequestedPool[chosenModel])
                    {
                        m.Request();
                        grp.ModelRequestedPool[chosenModel] = true;
                        grp.ModelRequestStartPool[chosenModel] = DateTime.UtcNow;
                        continue;
                    }
                    else
                    {
                        if (m.IsLoaded)
                        {
                            grp.ModelLoadedPool[chosenModel] = true;
                        }
                        else
                        {
                            if ((DateTime.UtcNow - grp.ModelRequestStartPool[chosenModel]).TotalMilliseconds > 1500)
                            {
                                Log(string.Format("WARN: Model '{0}' request timed out after 1500ms for group {1}.", chosenModel, grp.GroupId));
                                grp.FailedCount++;
                                grp.PendingCount--;
                                grp.ModelRequestedPool[chosenModel] = false;
                            }
                            continue;
                        }
                    }
                }

                // Compute candidate spawn position
                Vector3 candidatePos = Vector3.Zero;
                float heading = (float)(_rng.NextDouble() * 360.0);

                if (grp.Origin.HasValue)
                {
                    Vector3 baseOrig = grp.Origin.Value;
                    float angle = (float)(_rng.NextDouble() * 2 * Math.PI);
                    float r = (float)(Math.Sqrt(_rng.NextDouble()) * grp.OriginRadius);
                    candidatePos = new Vector3(baseOrig.X + (float)Math.Cos(angle) * r, baseOrig.Y + (float)Math.Sin(angle) * r, baseOrig.Z);
                }
                else
                {
                    float angle = (float)(_rng.NextDouble() * 2 * Math.PI);
                    float r = (float)(Math.Sqrt(_rng.NextDouble()) * grp.SpawnRadius);
                    candidatePos = new Vector3(grp.SpawnCenter.X + (float)Math.Cos(angle) * r, grp.SpawnCenter.Y + (float)Math.Sin(angle) * r, grp.SpawnCenter.Z);
                }

                // Resolve exact surface Z using precision Raycast (Map + Objects)
                // Accurately detects ground, platforms, and props stacked on props!
                float surfaceZ;
                float? hintZ = grp.Origin.HasValue ? (float?)grp.Origin.Value.Z : null;
                if (TryGetPreciseSurfaceZ(candidatePos.X, candidatePos.Y, hintZ, out surfaceZ))
                {
                    candidatePos.Z = surfaceZ + 0.05f;
                }
                else if (grp.Origin.HasValue)
                {
                    candidatePos.Z = grp.Origin.Value.Z + 0.05f;
                }

                // Optional Density-Aware check
                if (grp.DensityAware)
                {
                    int nearby = 0;
                    lock (_lock)
                    {
                        for (int k = 0; k < _crowdRegistry.Count; k++)
                        {
                            Ped cp = Entity.FromHandle(_crowdRegistry[k].Handle) as Ped;
                            if (cp != null && cp.Exists() && (cp.Position - candidatePos).Length() < 5.0f)
                            {
                                nearby++;
                            }
                        }
                    }
                    float localDensity = nearby / 78.5f;
                    if (localDensity > grp.DensityLimit)
                    {
                        continue;
                    }
                }

                Ped spawnedPed = null;
                string spawnFailureReason = "";
                try
                {
                    spawnedPed = Ped.Create(m, candidatePos, heading);
                }
                catch (Exception ex)
                {
                    spawnFailureReason = ex.Message;
                    Log(string.Format("WARN: Ped.Create threw exception for group {0}: {1}", grp.GroupId, ex.Message));
                }

                grp.LastSpawnTime = DateTime.UtcNow;
                spawnsRemainingBudget--;

                if (spawnedPed != null && spawnedPed.Exists())
                {
                    int handle = spawnedPed.Handle;
                    spawnedPed.IsPersistent = true;
                    spawnedPed.BlockPermanentEvents = true;

                    Vector3 dispersedDest = ComputeDispersedDestination(grp);

                    CrowdPedRecord rec = new CrowdPedRecord
                    {
                        Handle = handle,
                        ModelName = chosenModel,
                        CreatedAt = DateTime.UtcNow,
                        GroupId = grp.GroupId,
                        CurrentWaypointIndex = 0,
                        IsReverseRoute = false,
                        HasReachedDestination = false,
                        DispersedDestination = dispersedDest,
                        DispersedOrigin = candidatePos,
                        LastTaskAssignTime = DateTime.UtcNow,
                        RouteVersion = grp.RouteVersion
                    };

                    lock (_lock)
                    {
                        _crowdRegistry.Add(rec);
                        grp.MemberHandles.Add(handle);
                        grp.SpawnedCount++;
                        grp.PendingCount--;
                    }

                    Log(string.Format("SUCCESS: [SPAWN] Ped handle {0} (model: {1}) created for group {2} ('{3}') at ({4},{5},{6}) heading {7}. Alive: {8}, Target: {9}, Pending: {10}",
                        handle, chosenModel, grp.GroupId, grp.Name,
                        Math.Round(candidatePos.X, 1), Math.Round(candidatePos.Y, 1), Math.Round(candidatePos.Z, 1),
                        Math.Round(heading, 1), grp.MemberHandles.Count, grp.TargetCount, grp.PendingCount));

                    // Assign initial behavior task
                    AssignInitialBehaviorTask(grp, spawnedPed, candidatePos, rec);
                }
                else
                {
                    // If the native engine pool is saturated (null returned), throttle gracefully without burning pending queue or spamming memory
                    if (string.IsNullOrEmpty(spawnFailureReason))
                    {
                        grp.LastSpawnTime = DateTime.UtcNow.AddSeconds(3.0);
                        grp.Status = "ACTIVE";
                        Log(string.Format("INFO: [MAX_CAPACITY] Native engine ped pool saturated at {0} active peds. Spawning throttled for 3s to protect engine memory; holding {1} pending peds for open slots.", grp.MemberHandles.Count, grp.PendingCount));
                        break; // Stop trying to spawn in this frame
                    }
                    else
                    {
                        grp.FailedCount++;
                        grp.PendingCount--;
                        Log(string.Format("ERROR: [SPAWN_FAIL] Ped creation failed for group {0} ('{1}') model '{2}' at ({3},{4},{5}). Reason: {6}. Failed: {7}, Pending: {8}",
                            grp.GroupId, grp.Name, chosenModel,
                            Math.Round(candidatePos.X, 1), Math.Round(candidatePos.Y, 1), Math.Round(candidatePos.Z, 1),
                            spawnFailureReason,
                            grp.FailedCount, grp.PendingCount));
                    }
                }

                // Check group completion after spawn
                if (grp.PendingCount <= 0)
                {
                    grp.Status = (grp.MemberHandles.Count > 0) ? "ACTIVE" : (grp.SpawnedCount > 0 ? "COMPLETED" : "ERROR");
                    ReleaseGroupModels(grp);
                    Log(string.Format("INFO: Group {0} ('{1}') finished spawning. Spawned: {2}, Alive: {3}, Failed: {4}, Status: {5}",
                        grp.GroupId, grp.Name, grp.SpawnedCount, grp.MemberHandles.Count, grp.FailedCount, grp.Status));
                    Notification.PostTicker(string.Format("~g~[CrowdSim]~s~ Group '{0}' is now {1} ({2} alive)", grp.Name, grp.Status, grp.MemberHandles.Count), false, true);
                }
            }

            _spawningRoundRobinIndex = (_spawningRoundRobinIndex + 1) % totalGroups;
        }

        private static float Dist2D(Vector3 a, Vector3 b)
        {
            float dx = a.X - b.X;
            float dy = a.Y - b.Y;
            return (float)Math.Sqrt(dx * dx + dy * dy);
        }

        private static bool HasRoute(CrowdGroup grp)
        {
            return grp.Destination.HasValue || (grp.RouteWaypoints != null && grp.RouteWaypoints.Count > 0);
        }

        // The dashboard only sends X/Y for route points, so Z must be resolved from the world
        // (otherwise nav targets sit ~30m underground and peds never arrive).
        private Vector3 ResolveNavTarget(Vector3 target, Vector3 refPos)
        {
            float surfaceZ;
            float? hintZ = (Math.Abs(target.Z) > 1.0f) ? (float?)target.Z : (float?)Math.Max(refPos.Z, 18.5f);
            if (TryGetPreciseSurfaceZ(target.X, target.Y, hintZ, out surfaceZ))
            {
                return new Vector3(target.X, target.Y, surfaceZ);
            }
            return target;
        }

        /// <summary>
        /// Hybrid 3D Navigation Controller:
        /// Uses direct 3D steering (TASK_GO_STRAIGHT_TO_COORD) when traversing custom station props,
        /// stairs, elevated Foot Over Bridges (FOB), or turnstile corridors (where baked .ynv NavMesh is absent),
        /// and falls back to FollowNavMeshTo on open ground segments.
        /// </summary>
        private void TaskPedMoveToTarget(Ped p, Vector3 pedPos, Vector3 rawTarget, float moveSpeed, float arriveRadius, bool isStuckOrClimbing = false)
        {
            Vector3 resolved = ResolveNavTarget(rawTarget, pedPos);
            float dz = Math.Abs(resolved.Z - pedPos.Z);
            float dist2d = Dist2D(pedPos, resolved);
            bool hasCustomStation = _customProps.Count > 0;
            bool isElevatedOrStairs = (dz > 0.35f) || (pedPos.Z > 14.8f) || (resolved.Z > 14.8f);

            // Stair & Overbridge Slope Assist: if a ped is snagged against a custom stair lip or bridge edge,
            // smoothly advance and snap its Z height onto the stair/bridge surface so crowds never bottleneck.
            if (isStuckOrClimbing && (isElevatedOrStairs || hasCustomStation) && dist2d > 0.6f)
            {
                float nudgeDist = Math.Min(1.35f, dist2d * 0.45f);
                float nx = pedPos.X + ((resolved.X - pedPos.X) / dist2d) * nudgeDist;
                float ny = pedPos.Y + ((resolved.Y - pedPos.Y) / dist2d) * nudgeDist;
                float nz = pedPos.Z + (resolved.Z - pedPos.Z) * Math.Min(1.0f, nudgeDist / Math.Max(1.0f, dist2d));
                float surfZ;
                if (TryGetPreciseSurfaceZ(nx, ny, Math.Max(pedPos.Z, resolved.Z) + 2.5f, out surfZ))
                {
                    nz = surfZ + 0.08f;
                }
                Function.Call(Hash.SET_ENTITY_COORDS_NO_OFFSET, p.Handle, nx, ny, nz, false, false, false);
                pedPos = new Vector3(nx, ny, nz);
            }

            if (isElevatedOrStairs || (hasCustomStation && dist2d < 45.0f))
            {
                float dx = resolved.X - pedPos.X;
                float dy = resolved.Y - pedPos.Y;
                float heading = (float)(Math.Atan2(-dx, dy) * 180.0 / Math.PI);
                if (heading < 0f) heading += 360f;

                Function.Call(Hash.TASK_GO_STRAIGHT_TO_COORD, p.Handle, resolved.X, resolved.Y, resolved.Z, moveSpeed, -1, heading, Math.Max(0.4f, arriveRadius));
                Function.Call(Hash.SET_PED_MOVE_RATE_OVERRIDE, p.Handle, moveSpeed);
            }
            else
            {
                p.Task.FollowNavMeshTo(resolved, (PedMoveBlendRatio)moveSpeed, radius: Math.Max(0.8f, arriveRadius));
                Function.Call(Hash.SET_PED_MOVE_RATE_OVERRIDE, p.Handle, moveSpeed);
            }
        }

        private Vector3 ComputeDispersedPoint(Vector3 center, float radius)
        {
            float dAngle = (float)(_rng.NextDouble() * 2 * Math.PI);
            float dR = (float)(Math.Sqrt(_rng.NextDouble()) * Math.Max(1.0f, radius));
            return new Vector3(
                center.X + (float)Math.Cos(dAngle) * dR,
                center.Y + (float)Math.Sin(dAngle) * dR,
                center.Z);
        }

        private Vector3 ComputeDispersedDestination(CrowdGroup grp)
        {
            if (grp.Destination.HasValue)
            {
                return ComputeDispersedPoint(grp.Destination.Value, grp.DestinationRadius);
            }
            if (grp.RouteWaypoints != null && grp.RouteWaypoints.Count > 0)
            {
                return grp.RouteWaypoints[grp.RouteWaypoints.Count - 1];
            }
            return Vector3.Zero;
        }

        private static string RouteSignature(CrowdGroup grp)
        {
            System.Text.StringBuilder sb = new System.Text.StringBuilder();
            if (grp.Origin.HasValue) sb.AppendFormat(CultureInfo.InvariantCulture, "O{0:F1},{1:F1};", grp.Origin.Value.X, grp.Origin.Value.Y);
            if (grp.Destination.HasValue) sb.AppendFormat(CultureInfo.InvariantCulture, "D{0:F1},{1:F1};", grp.Destination.Value.X, grp.Destination.Value.Y);
            sb.AppendFormat(CultureInfo.InvariantCulture, "r{0:F1},{1:F1},{2:F1};s{3:F2};{4};{5};", grp.OriginRadius, grp.DestinationRadius, grp.SpawnRadius, grp.MoveSpeed, grp.Behavior, grp.ArrivalBehavior);
            if (grp.RouteWaypoints != null)
            {
                for (int i = 0; i < grp.RouteWaypoints.Count; i++)
                    sb.AppendFormat(CultureInfo.InvariantCulture, "W{0:F1},{1:F1};", grp.RouteWaypoints[i].X, grp.RouteWaypoints[i].Y);
            }
            if (grp.DespawnCheckpointEnabled && grp.DespawnCheckpoint.HasValue)
                sb.AppendFormat(CultureInfo.InvariantCulture, "DSP{0:F1},{1:F1},{2:F1};", grp.DespawnCheckpoint.Value.X, grp.DespawnCheckpoint.Value.Y, grp.DespawnRadius);
            return sb.ToString();
        }

        // Must be called while holding _lock. Removes the group's peds and re-queues the full target.
        private void RestartGroupLocked(CrowdGroup grp)
        {
            int removed = 0;
            for (int i = 0; i < grp.MemberHandles.Count; i++)
            {
                try
                {
                    Ped p = Entity.FromHandle(grp.MemberHandles[i]) as Ped;
                    if (p != null && p.Exists())
                    {
                        p.IsPersistent = false;
                        p.Delete();
                        removed++;
                    }
                }
                catch (Exception ex)
                {
                    Log(string.Format("WARN: RestartGroup failed deleting ped {0}: {1}", grp.MemberHandles[i], ex.Message));
                }
            }
            string gid = grp.GroupId;
            _crowdRegistry.RemoveAll(delegate (CrowdPedRecord r) { return r.GroupId == gid; });
            grp.MemberHandles.Clear();
            grp.SpawnedCount = 0;
            grp.FailedCount = 0;
            grp.PendingCount = grp.TargetCount;
            grp.Status = "SPAWNING";
            grp.LastSpawnTime = DateTime.MinValue;
            ReleaseGroupModels(grp);
            Log(string.Format("INFO: Group '{0}' ({1}) restarted: removed {2} peds, respawning {3}.", grp.Name, grp.GroupId, removed, grp.TargetCount));
        }

        private void AssignInitialBehaviorTask(CrowdGroup grp, Ped ped, Vector3 spawnPos, CrowdPedRecord rec)
        {
            try
            {
                if (HasRoute(grp))
                {
                    Vector3 target = (grp.RouteWaypoints != null && grp.RouteWaypoints.Count > 0) ? grp.RouteWaypoints[0] : rec.DispersedDestination;
                    TaskPedMoveToTarget(ped, spawnPos, target, grp.MoveSpeed, 1.0f, false);
                    return;
                }

                if (grp.Behavior == "ROUTE_TRAVEL")
                {
                    // Route behavior selected but no destination/waypoints yet: idle-wander instead of walking to (0,0,0)
                    ped.Task.WanderAround(spawnPos, 25.0f);
                    return;
                }

                switch (grp.Behavior)
                {
                    case "COHESIVE_WANDER":
                        ped.Task.WanderAround(grp.SpawnCenter, grp.MovementRadius);
                        break;

                    case "STATIONARY_GATHERING":
                        ped.Task.WanderAround(spawnPos, 4.0f);
                        break;

                    case "FOLLOW_LEADER":
                        if (grp.LeaderHandle != 0 && grp.LeaderHandle != ped.Handle)
                        {
                            Ped leader = Entity.FromHandle(grp.LeaderHandle) as Ped;
                            if (leader != null && leader.Exists())
                            {
                                ped.Task.GoTo(leader, Vector3.Zero, -1);
                            }
                            else
                            {
                                ped.Task.WanderAround(grp.SpawnCenter, grp.MovementRadius);
                            }
                        }
                        else
                        {
                            ped.Task.WanderAround(grp.SpawnCenter, grp.MovementRadius);
                        }
                        break;

                    case "FOLLOW_PLAYER":
                        Player p = Game.Player;
                        if (p != null && p.Character != null && p.Character.Exists())
                        {
                            ped.Task.FollowNavMeshTo(p.Character.Position);
                        }
                        else
                        {
                            ped.Task.WanderAround(grp.SpawnCenter, grp.MovementRadius);
                        }
                        break;

                    case "PATROL":
                        if (grp.PatrolWaypoints != null && grp.PatrolWaypoints.Count > 0)
                        {
                            ped.Task.FollowNavMeshTo(grp.PatrolWaypoints[0]);
                        }
                        else
                        {
                            ped.Task.WanderAround(grp.SpawnCenter, grp.MovementRadius);
                        }
                        break;

                    case "INDEPENDENT_WANDER":
                    default:
                        ped.Task.WanderAround(spawnPos, grp.MovementRadius);
                        break;
                }
            }
            catch (Exception ex)
            {
                Log(string.Format("WARN: AssignInitialBehaviorTask threw on ped {0}: {1}", ped.Handle, ex.Message));
            }
        }

        #endregion

        #region Behavior Controllers

        private void TickGroupBehaviors()
        {
            foreach (CrowdGroup grp in _groups.Values)
            {
                bool groupPaused = (grp.Status == "PAUSED");
                if (grp.Status != "ACTIVE" && grp.Status != "SPAWNING" && !groupPaused) continue;

                // Throttled behavior updates: once every 1.5s per group
                if ((DateTime.UtcNow - grp.LastBehaviorUpdate).TotalSeconds < 1.5) continue;
                grp.LastBehaviorUpdate = DateTime.UtcNow;

                List<Ped> aliveMembers = new List<Ped>();
                for (int i = 0; i < grp.MemberHandles.Count; i++)
                {
                    Ped p = Entity.FromHandle(grp.MemberHandles[i]) as Ped;
                    if (p != null && p.Exists() && !p.IsDead)
                    {
                        aliveMembers.Add(p);
                    }
                }

                if (aliveMembers.Count == 0) continue;

                // Handle Paused Experiment state
                if (_experiment.State == "PAUSED" || groupPaused)
                {
                    foreach (Ped p in aliveMembers)
                    {
                        p.Task.StandStill(2000);
                    }
                    continue;
                }

                // Stage 4 Destination & Route Travel Behavior
                if (HasRoute(grp))
                {
                    UpdateRouteTravelBehavior(grp, aliveMembers);
                    continue;
                }

                switch (grp.Behavior)
                {
                    case "FOLLOW_LEADER":
                        UpdateFollowLeaderBehavior(grp, aliveMembers);
                        break;

                    case "FOLLOW_PLAYER":
                        UpdateFollowPlayerBehavior(grp, aliveMembers);
                        break;

                    case "COHESIVE_WANDER":
                        UpdateCohesiveWanderBehavior(grp, aliveMembers);
                        break;

                    case "PATROL":
                        UpdatePatrolBehavior(grp, aliveMembers);
                        break;

                    case "STATIONARY_GATHERING":
                        UpdateStationaryGatheringBehavior(grp, aliveMembers);
                        break;

                    case "INDEPENDENT_WANDER":
                    default:
                        UpdateIndependentWanderBehavior(grp, aliveMembers);
                        break;
                }
            }
        }

        private void UpdateRouteTravelBehavior(CrowdGroup grp, List<Ped> members)
        {
            bool hasDest = grp.Destination.HasValue;
            bool hasWps = grp.RouteWaypoints != null && grp.RouteWaypoints.Count > 0;
            if (!hasDest && !hasWps) return;

            Vector3 dest = hasDest ? grp.Destination.Value : grp.RouteWaypoints[grp.RouteWaypoints.Count - 1];
            float arriveRadius = hasDest ? grp.DestinationRadius : 4.0f;
            if (arriveRadius < 2.0f) arriveRadius = 2.0f;

            bool isLooping = (grp.ArrivalBehavior == "LOOP_ROUTE" ||
                              grp.ArrivalBehavior == "NEXT_WAYPOINT" ||
                              grp.ArrivalBehavior == "LOOP" ||
                              grp.ArrivalBehavior == "PING_PONG" ||
                              grp.ArrivalBehavior == "CYCLE");

            for (int i = 0; i < members.Count; i++)
            {
                Ped p = members[i];
                CrowdPedRecord rec = FindPedRecord(p.Handle);
                if (rec == null) continue;

                Vector3 pedPos = p.Position;

                // Route was edited after this ped spawned: re-initialise its personal route state
                if (rec.RouteVersion != grp.RouteVersion)
                {
                    rec.RouteVersion = grp.RouteVersion;
                    rec.DispersedDestination = ComputeDispersedDestination(grp);
                    rec.CurrentWaypointIndex = 0;
                    rec.IsReverseRoute = false;
                    rec.HasReachedDestination = false;
                    rec.LastTaskAssignTime = DateTime.MinValue;
                }

                // If heading to final separate despawn checkpoint
                if (rec.HeadingToDespawn)
                {
                    if (grp.DespawnCheckpointEnabled && grp.DespawnCheckpoint.HasValue)
                    {
                        Vector3 dspTarget = grp.DespawnCheckpoint.Value;
                        float dspRad = Math.Max(3.0f, grp.DespawnRadius);
                        if (Dist2D(pedPos, dspTarget) <= dspRad)
                        {
                            p.IsPersistent = false;
                            p.Delete();
                            lock (_lock)
                            {
                                _crowdRegistry.Remove(rec);
                                grp.MemberHandles.Remove(p.Handle);
                                grp.ExitedCount++;
                                if (grp.ContinuousStream && grp.Status != "PAUSED" && grp.Status != "STOPPED")
                                {
                                    int alive = grp.MemberHandles.Count;
                                    if (alive < grp.TargetCount)
                                    {
                                        grp.PendingCount = grp.TargetCount - alive;
                                        grp.Status = "SPAWNING";
                                    }
                                }
                            }
                            continue;
                        }

                        // Only retask if unassigned or stuck
                        bool stuckDsp = (p.Velocity.Length() < 0.25f && (DateTime.UtcNow - rec.LastTaskAssignTime).TotalSeconds >= 2.2);
                        if (rec.LastTaskAssignTime == DateTime.MinValue || stuckDsp)
                        {
                            rec.LastTaskAssignTime = DateTime.UtcNow;
                            TaskPedMoveToTarget(p, pedPos, dspTarget, grp.MoveSpeed, 1.0f, stuckDsp);
                        }
                        continue;
                    }
                    else
                    {
                        rec.HeadingToDespawn = false;
                        if (isLooping) rec.IsReverseRoute = true;
                        else rec.HasReachedDestination = true;
                    }
                }

                // If ped has reached its permanent destination (STOP, WANDER, GATHER)
                if (rec.HasReachedDestination)
                {
                    if (grp.DespawnCheckpointEnabled && grp.DespawnCheckpoint.HasValue)
                    {
                        rec.HasReachedDestination = false;
                        rec.HeadingToDespawn = true;
                        rec.LastTaskAssignTime = DateTime.UtcNow;
                        Vector3 dspTarget = grp.DespawnCheckpoint.Value;
                        TaskPedMoveToTarget(p, pedPos, dspTarget, grp.MoveSpeed, 1.0f, false);
                        continue;
                    }
                    if ((DateTime.UtcNow - rec.LastTaskAssignTime).TotalSeconds >= 10.0)
                    {
                        rec.LastTaskAssignTime = DateTime.UtcNow;
                        if (grp.ArrivalBehavior == "STOP")
                        {
                            p.Task.StandStill(12000);
                        }
                        else if (grp.ArrivalBehavior == "WANDER")
                        {
                            p.Task.WanderAround(ResolveNavTarget(dest, pedPos), arriveRadius);
                        }
                        else if (grp.ArrivalBehavior == "GATHER")
                        {
                            p.Task.WanderAround(ResolveNavTarget(rec.DispersedDestination, pedPos), 3.0f);
                        }
                    }
                    continue;
                }

                // -------------------------------------------------------------
                // FORWARD TRAVERSAL (Towards Destination)
                // -------------------------------------------------------------
                if (!rec.IsReverseRoute)
                {
                    // Advance through intermediate waypoints (tighter 2.6m radius for accurate stair/bridge alignment)
                    if (hasWps && rec.CurrentWaypointIndex < grp.RouteWaypoints.Count)
                    {
                        Vector3 wp = grp.RouteWaypoints[rec.CurrentWaypointIndex];
                        if (Dist2D(pedPos, wp) <= 2.6f)
                        {
                            rec.CurrentWaypointIndex++;
                            rec.LastTaskAssignTime = DateTime.MinValue; // Retask immediately to next waypoint
                        }
                    }

                    Vector3 currentTarget;
                    bool isAtFinalDestNode = !hasWps || rec.CurrentWaypointIndex >= grp.RouteWaypoints.Count;

                    if (!isAtFinalDestNode)
                    {
                        currentTarget = grp.RouteWaypoints[rec.CurrentWaypointIndex];
                    }
                    else
                    {
                        currentTarget = hasDest ? rec.DispersedDestination : dest;

                        // Check if ped reached final destination
                        if (Dist2D(pedPos, dest) <= arriveRadius || (hasDest && Dist2D(pedPos, rec.DispersedDestination) <= 3.2f))
                        {
                            if (grp.DespawnCheckpointEnabled && grp.DespawnCheckpoint.HasValue)
                            {
                                rec.HeadingToDespawn = true;
                                rec.HasReachedDestination = false; // Do not trigger terminal STOP
                                rec.LastTaskAssignTime = DateTime.UtcNow;
                                Vector3 dspTarget = grp.DespawnCheckpoint.Value;
                                TaskPedMoveToTarget(p, pedPos, dspTarget, grp.MoveSpeed, 1.5f, false);
                                continue;
                            }
                            else if (grp.ArrivalBehavior == "DESPAWN" || grp.ArrivalBehavior == "DESPAWN_AT_DEST")
                            {
                                p.IsPersistent = false;
                                p.Delete();
                                lock (_lock)
                                {
                                    _crowdRegistry.Remove(rec);
                                    grp.MemberHandles.Remove(p.Handle);
                                    grp.ExitedCount++;
                                    if (grp.ContinuousStream && grp.Status != "PAUSED" && grp.Status != "STOPPED")
                                    {
                                        int alive = grp.MemberHandles.Count;
                                        if (alive < grp.TargetCount)
                                        {
                                            grp.PendingCount = grp.TargetCount - alive;
                                            grp.Status = "SPAWNING";
                                        }
                                    }
                                }
                                continue;
                            }
                            else if (isLooping)
                            {
                                // Reverse route: start heading back towards Origin!
                                rec.IsReverseRoute = true;
                                rec.HasReachedDestination = false;
                                rec.CurrentWaypointIndex = hasWps ? grp.RouteWaypoints.Count - 1 : -1;
                                rec.DispersedOrigin = grp.Origin.HasValue
                                    ? ComputeDispersedPoint(grp.Origin.Value, grp.OriginRadius)
                                    : pedPos;
                                rec.LastTaskAssignTime = DateTime.MinValue; // Retask immediately
                                currentTarget = (hasWps && rec.CurrentWaypointIndex >= 0)
                                    ? grp.RouteWaypoints[rec.CurrentWaypointIndex]
                                    : rec.DispersedOrigin;
                            }
                            else
                            {
                                // Terminal arrival (STOP, WANDER, GATHER)
                                rec.HasReachedDestination = true;
                                rec.LastTaskAssignTime = DateTime.UtcNow;
                                if (grp.ArrivalBehavior == "STOP") p.Task.StandStill(10000);
                                else if (grp.ArrivalBehavior == "WANDER") p.Task.WanderAround(ResolveNavTarget(dest, pedPos), arriveRadius);
                                else if (grp.ArrivalBehavior == "GATHER") p.Task.WanderAround(ResolveNavTarget(rec.DispersedDestination, pedPos), 3.0f);
                                continue;
                            }
                        }
                    }

                    // Task ped to continue towards currentTarget when unassigned, waypoint changed, or stuck/climbing
                    bool isStuckFwd = (p.Velocity.Length() < 0.25f && (DateTime.UtcNow - rec.LastTaskAssignTime).TotalSeconds >= 2.2);
                    bool needsRetask = (rec.LastTaskAssignTime == DateTime.MinValue) || isStuckFwd;
                    if (needsRetask)
                    {
                        rec.LastTaskAssignTime = DateTime.UtcNow;
                        TaskPedMoveToTarget(p, pedPos, currentTarget, grp.MoveSpeed, 1.0f, isStuckFwd);
                    }
                }
                // -------------------------------------------------------------
                // REVERSE TRAVERSAL (Towards Origin in Loop Mode)
                // -------------------------------------------------------------
                else
                {
                    // Check if reaching intermediate waypoint in reverse
                    if (hasWps && rec.CurrentWaypointIndex >= 0)
                    {
                        Vector3 wp = grp.RouteWaypoints[rec.CurrentWaypointIndex];
                        if (Dist2D(pedPos, wp) <= 2.6f)
                        {
                            rec.CurrentWaypointIndex--;
                            rec.LastTaskAssignTime = DateTime.MinValue; // Retask immediately
                        }
                    }

                    Vector3 currentTarget;
                    bool isAtOriginNode = !hasWps || rec.CurrentWaypointIndex < 0;

                    if (!isAtOriginNode)
                    {
                        currentTarget = grp.RouteWaypoints[rec.CurrentWaypointIndex];
                    }
                    else
                    {
                        Vector3 originPos = grp.Origin.HasValue ? grp.Origin.Value : (hasWps ? grp.RouteWaypoints[0] : dest);
                        float originRad = grp.OriginRadius > 0 ? grp.OriginRadius : 4.0f;
                        currentTarget = rec.DispersedOrigin;

                        // Check if ped reached Origin
                        if (Dist2D(pedPos, originPos) <= originRad || Dist2D(pedPos, rec.DispersedOrigin) <= 3.2f)
                        {
                            // Reached Origin! Turn around and head forward towards Destination again!
                            rec.IsReverseRoute = false;
                            rec.HasReachedDestination = false;
                            rec.CurrentWaypointIndex = 0;
                            rec.DispersedDestination = ComputeDispersedDestination(grp);
                            rec.LastTaskAssignTime = DateTime.MinValue; // Retask immediately
                            currentTarget = hasWps ? grp.RouteWaypoints[0] : rec.DispersedDestination;
                        }
                    }

                    // Task ped to continue towards currentTarget when unassigned, waypoint changed, or stuck/climbing
                    bool isStuckRev = (p.Velocity.Length() < 0.25f && (DateTime.UtcNow - rec.LastTaskAssignTime).TotalSeconds >= 2.2);
                    bool needsRetask = (rec.LastTaskAssignTime == DateTime.MinValue) || isStuckRev;
                    if (needsRetask)
                    {
                        rec.LastTaskAssignTime = DateTime.UtcNow;
                        TaskPedMoveToTarget(p, pedPos, currentTarget, grp.MoveSpeed, 1.0f, isStuckRev);
                    }
                }
            }
        }

        private void UpdateFollowLeaderBehavior(CrowdGroup grp, List<Ped> members)
        {
            Ped leader = null;
            if (grp.LeaderHandle != 0)
            {
                leader = Entity.FromHandle(grp.LeaderHandle) as Ped;
            }

            if (leader == null || !leader.Exists() || leader.IsDead)
            {
                leader = ElectNewLeader(grp);
            }

            if (leader == null) return;

            Vector3 leaderPos = leader.Position;
            float followDist = grp.FollowDistance;

            for (int i = 0; i < members.Count; i++)
            {
                Ped p = members[i];
                if (p.Handle == leader.Handle)
                {
                    if ((p.Position - grp.SpawnCenter).Length() > grp.MovementRadius)
                    {
                        p.Task.FollowNavMeshTo(grp.SpawnCenter);
                    }
                    continue;
                }

                float dist = (p.Position - leaderPos).Length();
                if (dist > followDist * 3.0f)
                {
                    p.Task.FollowNavMeshTo(leaderPos);
                }
                else if (dist > followDist * 1.5f)
                {
                    p.Task.GoTo(leader, Vector3.Zero, -1);
                }
            }
        }

        private void UpdateFollowPlayerBehavior(CrowdGroup grp, List<Ped> members)
        {
            Player player = Game.Player;
            if (player == null || player.Character == null || !player.Character.Exists()) return;

            Vector3 playerPos = player.Character.Position;
            float followDist = grp.FollowDistance;

            for (int i = 0; i < members.Count; i++)
            {
                Ped p = members[i];
                float dist = (p.Position - playerPos).Length();
                if (dist > followDist * 2.5f)
                {
                    p.Task.FollowNavMeshTo(playerPos);
                }
                else if (dist > followDist)
                {
                    p.Task.GoTo(player.Character, Vector3.Zero, -1);
                }
            }
        }

        private void UpdateCohesiveWanderBehavior(CrowdGroup grp, List<Ped> members)
        {
            Vector3 center = grp.SpawnCenter;
            float radius = grp.MovementRadius;

            for (int i = 0; i < members.Count; i++)
            {
                Ped p = members[i];
                if ((p.Position - center).Length() > radius)
                {
                    p.Task.FollowNavMeshTo(center);
                }
            }
        }

        private void UpdateStationaryGatheringBehavior(CrowdGroup grp, List<Ped> members)
        {
            Vector3 center = grp.SpawnCenter;
            for (int i = 0; i < members.Count; i++)
            {
                Ped p = members[i];
                if ((p.Position - center).Length() > 6.0f)
                {
                    p.Task.FollowNavMeshTo(center);
                }
            }
        }

        private void UpdatePatrolBehavior(CrowdGroup grp, List<Ped> members)
        {
            if (grp.PatrolWaypoints == null || grp.PatrolWaypoints.Count == 0) return;

            int wpIndex = grp.CurrentPatrolIndex % grp.PatrolWaypoints.Count;
            Vector3 targetWp = grp.PatrolWaypoints[wpIndex];

            int arrivedCount = 0;
            for (int i = 0; i < members.Count; i++)
            {
                Ped p = members[i];
                if ((p.Position - targetWp).Length() < 5.0f)
                {
                    arrivedCount++;
                }
            }

            if (arrivedCount >= Math.Max(1, members.Count / 2))
            {
                grp.CurrentPatrolIndex = (grp.CurrentPatrolIndex + 1) % grp.PatrolWaypoints.Count;
                targetWp = grp.PatrolWaypoints[grp.CurrentPatrolIndex];
            }

            for (int i = 0; i < members.Count; i++)
            {
                members[i].Task.FollowNavMeshTo(targetWp);
            }
        }

        private void UpdateIndependentWanderBehavior(CrowdGroup grp, List<Ped> members)
        {
            Vector3 center = grp.SpawnCenter;
            float radius = grp.MovementRadius;

            for (int i = 0; i < members.Count; i++)
            {
                Ped p = members[i];
                if ((p.Position - center).Length() > radius * 1.3f)
                {
                    p.Task.FollowNavMeshTo(center);
                }
            }
        }

        private Ped ElectNewLeader(CrowdGroup grp)
        {
            grp.LeaderHandle = 0;
            for (int i = 0; i < grp.MemberHandles.Count; i++)
            {
                Ped p = Entity.FromHandle(grp.MemberHandles[i]) as Ped;
                if (p != null && p.Exists() && !p.IsDead)
                {
                    grp.LeaderHandle = p.Handle;
                    Log(string.Format("INFO: Elected new leader Ped #{0} for group {1}", p.Handle, grp.GroupId));
                    return p;
                }
            }
            return null;
        }

        private CrowdPedRecord FindPedRecord(int handle)
        {
            lock (_lock)
            {
                for (int i = 0; i < _crowdRegistry.Count; i++)
                {
                    if (_crowdRegistry[i].Handle == handle) return _crowdRegistry[i];
                }
            }
            return null;
        }

        private void ReleaseGroupModels(CrowdGroup grp)
        {
            if (grp.ModelPool == null) return;
            foreach (Model m in grp.ModelPool.Values)
            {
                try
                {
                    if (m != null && m.IsLoaded)
                    {
                        m.MarkAsNoLongerNeeded();
                    }
                }
                catch { }
            }
            grp.ModelPool.Clear();
            grp.ModelRequestedPool.Clear();
            grp.ModelLoadedPool.Clear();
            grp.ModelRequestStartPool.Clear();
        }

        private string PickModelFromCatalog(List<ModelCatalogItem> catalog, string fallback)
        {
            if (catalog == null || catalog.Count == 0) return fallback;
            if (catalog.Count == 1) return catalog[0].ModelName;

            int totalWeight = 0;
            for (int i = 0; i < catalog.Count; i++) totalWeight += catalog[i].Weight;
            if (totalWeight <= 0) return catalog[0].ModelName;

            int r = _rng.Next(totalWeight);
            int accum = 0;
            for (int i = 0; i < catalog.Count; i++)
            {
                accum += catalog[i].Weight;
                if (r < accum) return catalog[i].ModelName;
            }
            return catalog[0].ModelName;
        }

        private Vector3? ParseVector3Dict(Dictionary<string, object> dict)
        {
            if (dict == null) return null;
            float x = 0f, y = 0f, z = 0f;
            if (dict.ContainsKey("x")) float.TryParse(Convert.ToString(dict["x"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out x);
            if (dict.ContainsKey("y")) float.TryParse(Convert.ToString(dict["y"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out y);
            if (dict.ContainsKey("z")) float.TryParse(Convert.ToString(dict["z"], CultureInfo.InvariantCulture), NumberStyles.Float, CultureInfo.InvariantCulture, out z);
            return new Vector3(x, y, z);
        }

        private Dictionary<string, object> SerializeVector3(Vector3 v)
        {
            Dictionary<string, object> d = new Dictionary<string, object>();
            d["x"] = Math.Round(v.X, 2);
            d["y"] = Math.Round(v.Y, 2);
            d["z"] = Math.Round(v.Z, 2);
            return d;
        }

        private Dictionary<string, object> SerializeGroup(CrowdGroup grp)
        {
            Dictionary<string, object> d = new Dictionary<string, object>();
            d["group_id"] = grp.GroupId;
            d["name"] = grp.Name;
            d["primary_model"] = grp.PrimaryModel;
            d["target_count"] = grp.TargetCount;
            d["spawned_count"] = grp.SpawnedCount;
            d["alive_count"] = grp.MemberHandles.Count;
            d["failed_count"] = grp.FailedCount;
            d["pending_count"] = grp.PendingCount;
            d["status"] = grp.Status;
            d["spawn_radius"] = Math.Round(grp.SpawnRadius, 2);
            d["movement_radius"] = Math.Round(grp.MovementRadius, 2);
            d["spawn_rate"] = Math.Round(grp.SpawnRate, 2);
            d["behavior"] = grp.Behavior;
            d["leader_handle"] = grp.LeaderHandle;
            d["density_aware"] = grp.DensityAware;
            d["color"] = grp.Color;
            d["move_speed"] = grp.MoveSpeed;
            d["arrival_behavior"] = grp.ArrivalBehavior;
            d["vehicle_cleanup"] = grp.VehicleCleanup;
            d["vehicle_cleanup_radius"] = Math.Round(grp.VehicleCleanupRadius, 2);
            d["vehicle_cleanup_center"] = grp.VehicleCleanupCenter ?? "ORIGIN";
            d["created_at"] = grp.CreatedAt.ToString("o");

            if (grp.Origin.HasValue)
            {
                d["origin"] = SerializeVector3(grp.Origin.Value);
                d["origin_radius"] = Math.Round(grp.OriginRadius, 2);
            }
            if (grp.Destination.HasValue)
            {
                d["destination"] = SerializeVector3(grp.Destination.Value);
                d["destination_radius"] = Math.Round(grp.DestinationRadius, 2);
            }

            List<Dictionary<string, object>> wpList = new List<Dictionary<string, object>>();
            if (grp.RouteWaypoints != null)
            {
                for (int i = 0; i < grp.RouteWaypoints.Count; i++)
                {
                    wpList.Add(SerializeVector3(grp.RouteWaypoints[i]));
                }
            }
            d["waypoints"] = wpList;

            d["despawn_checkpoint_enabled"] = grp.DespawnCheckpointEnabled;
            if (grp.DespawnCheckpoint.HasValue)
            {
                d["despawn_checkpoint"] = SerializeVector3(grp.DespawnCheckpoint.Value);
                d["despawn_radius"] = Math.Round(grp.DespawnRadius, 2);
            }
            d["continuous_stream"] = grp.ContinuousStream;
            d["exited_count"] = grp.ExitedCount;

            return d;
        }

        private Dictionary<string, object> SerializeExperiment()
        {
            Dictionary<string, object> d = new Dictionary<string, object>();
            d["name"] = _experiment.Name;
            d["state"] = _experiment.State;
            d["area_type"] = _experiment.AreaType;
            d["center_x"] = _experiment.CenterX;
            d["center_y"] = _experiment.CenterY;
            d["center_z"] = _experiment.CenterZ;
            d["width"] = _experiment.Width;
            d["height"] = _experiment.Height;
            d["radius"] = _experiment.Radius;
            d["vehicle_cleanup"] = _experiment.VehicleCleanup;
            d["grid_resolution"] = _experiment.GridResolution;
            d["allow_outside_routing"] = _experiment.AllowOutsideRouting;
            return d;
        }

        #endregion

        #region Background Networking Worker

        private void EnqueueAck(Dictionary<string, object> ackData)
        {
            JavaScriptSerializer serializer = new JavaScriptSerializer();
            string ackJson = serializer.Serialize(ackData);
            lock (_lock)
            {
                _outboundQueue.Enqueue(ackJson);
            }
        }

        private void SendErrorAck(CommandItem cmd, string errorMsg)
        {
            Log(string.Format("WARN: Command failed: {0} (ReqID: {1}) - {2}", cmd.Command, cmd.RequestId, errorMsg));
            Dictionary<string, object> ackData = new Dictionary<string, object>();
            ackData["request_id"] = cmd.RequestId;
            ackData["command"] = cmd.Command;
            ackData["status"] = "ERROR";
            ackData["error"] = errorMsg;
            ackData["game_time"] = Game.GameTime;
            ackData["timestamp_utc"] = DateTime.UtcNow.ToString("o");

            EnqueueAck(ackData);
        }

        private void NetworkWorkerLoop()
        {
            int consecutiveAckFailures = 0;

            while (_isRunning)
            {
                // Step A: Send pending acknowledgments
                try
                {
                    string ackToSend = null;
                    lock (_lock)
                    {
                        if (_outboundQueue.Count > 0)
                        {
                            ackToSend = _outboundQueue.Peek();
                        }
                    }

                    if (!string.IsNullOrEmpty(ackToSend))
                    {
                        Log(string.Format("DIAG: Posting ACK from outbound queue: {0}", ackToSend));
                        bool sent = SendHttpPost(AckUrl, ackToSend);
                        if (sent)
                        {
                            consecutiveAckFailures = 0;
                            lock (_lock)
                            {
                                if (_outboundQueue.Count > 0 && _outboundQueue.Peek() == ackToSend)
                                {
                                    _outboundQueue.Dequeue();
                                }
                            }
                        }
                        else
                        {
                            consecutiveAckFailures++;
                            if (consecutiveAckFailures >= 5)
                            {
                                Log(string.Format("ERROR: Discarding un-acknowledgeable item after 5 failed attempts: {0}", ackToSend));
                                lock (_lock)
                                {
                                    if (_outboundQueue.Count > 0 && _outboundQueue.Peek() == ackToSend)
                                    {
                                        _outboundQueue.Dequeue();
                                    }
                                }
                                consecutiveAckFailures = 0;
                            }
                        }
                    }
                }
                catch (Exception ex)
                {
                    Log(string.Format("WARN: Network worker outbound ACK step error: {0}", ex.Message));
                }

                // Step B: Poll for new commands from bridge with live telemetry
                try
                {
                    string pollUrlWithParams = PollUrl;
                    lock (_lock)
                    {
                        if (_cachedPlayerValid)
                        {
                            pollUrlWithParams = string.Format(
                                CultureInfo.InvariantCulture,
                                "{0}?px={1:F2}&py={2:F2}&pz={3:F2}&h={4:F1}&handle={5}&groups={6}&peds={7}&god={8}&wanted={9}&fly={10}",
                                PollUrl,
                                _cachedPlayerPos.X,
                                _cachedPlayerPos.Y,
                                _cachedPlayerPos.Z,
                                _cachedPlayerHeading,
                                _cachedPlayerHandle,
                                _groups.Count,
                                _crowdRegistry.Count,
                                _godModeEnabled ? 1 : 0,
                                _neverWantedEnabled ? 1 : 0,
                                _noclipEnabled ? 1 : 0
                            );
                        }
                    }

                    string pollResponse = SendHttpGet(pollUrlWithParams);
                    if (!string.IsNullOrEmpty(pollResponse))
                    {
                        CommandItem parsedCmd = ParseCommandFromJson(pollResponse);
                        if (parsedCmd != null)
                        {
                            Log(string.Format("DIAG: Parsed command from poll: {0} (ReqID: {1})", parsedCmd.Command, parsedCmd.RequestId));
                            int qCount;
                            lock (_lock)
                            {
                                _inboundQueue.Enqueue(parsedCmd);
                                qCount = _inboundQueue.Count;
                            }
                            Log(string.Format("DIAG: Enqueued to _inboundQueue: {0} (ReqID: {1}, QueueLengthAfter: {2})", parsedCmd.Command, parsedCmd.RequestId, qCount));
                        }
                    }
                }
                catch (WebException wex)
                {
                    Log(string.Format("WARN: Network worker poll WebException: {0}", wex.Message));
                    Thread.Sleep(500);
                }
                catch (Exception ex)
                {
                    Log(string.Format("WARN: Network worker poll exception: {0}", ex.Message));
                }

                Thread.Sleep(100);
            }
        }

        private static string SendHttpGet(string url)
        {
            ServicePointManager.DefaultConnectionLimit = 50;
            ServicePointManager.Expect100Continue = false;

            HttpWebRequest request = (HttpWebRequest)WebRequest.Create(url);
            request.Method = "GET";
            request.Timeout = 1500;
            request.ReadWriteTimeout = 1500;
            request.KeepAlive = false;

            using (HttpWebResponse response = (HttpWebResponse)request.GetResponse())
            using (Stream stream = response.GetResponseStream())
            using (StreamReader reader = new StreamReader(stream, Encoding.UTF8))
            {
                return reader.ReadToEnd();
            }
        }

        private static bool SendHttpPost(string url, string jsonBody)
        {
            try
            {
                ServicePointManager.DefaultConnectionLimit = 50;
                ServicePointManager.Expect100Continue = false;

                byte[] bytes = Encoding.UTF8.GetBytes(jsonBody);
                HttpWebRequest request = (HttpWebRequest)WebRequest.Create(url);
                request.Method = "POST";
                request.ContentType = "application/json; charset=utf-8";
                request.ContentLength = bytes.Length;
                request.Timeout = 2000;
                request.ReadWriteTimeout = 2000;
                request.KeepAlive = false;

                using (Stream reqStream = request.GetRequestStream())
                {
                    reqStream.Write(bytes, 0, bytes.Length);
                }

                using (HttpWebResponse response = (HttpWebResponse)request.GetResponse())
                using (Stream respStream = response.GetResponseStream())
                {
                    Log(string.Format("DIAG: SendHttpPost OK (StatusCode: {0})", (int)response.StatusCode));
                    return response.StatusCode == HttpStatusCode.OK;
                }
            }
            catch (WebException wex)
            {
                int code = 0;
                string body = "";
                HttpWebResponse hr = wex.Response as HttpWebResponse;
                if (hr != null)
                {
                    code = (int)hr.StatusCode;
                    try
                    {
                        using (Stream s = hr.GetResponseStream())
                        using (StreamReader r = new StreamReader(s))
                        {
                            body = r.ReadToEnd();
                        }
                    }
                    catch { }
                }
                Log(string.Format("WARN: SendHttpPost WebException (Status: {0}, Error: {1}, Body: {2})", code, wex.Message, body));
                return false;
            }
            catch (Exception ex)
            {
                Log(string.Format("WARN: SendHttpPost Exception: {0}", ex.Message));
                return false;
            }
        }

        private static CommandItem ParseCommandFromJson(string json)
        {
            try
            {
                JavaScriptSerializer serializer = new JavaScriptSerializer();
                Dictionary<string, object> root = serializer.Deserialize<Dictionary<string, object>>(json);
                if (root == null || !root.ContainsKey("has_command") || !(bool)root["has_command"]) return null;
                if (!root.ContainsKey("command") || !(root["command"] is Dictionary<string, object>)) return null;

                Dictionary<string, object> cmdDict = (Dictionary<string, object>)root["command"];
                string reqId = cmdDict.ContainsKey("request_id") ? cmdDict["request_id"] as string : null;
                string cmdName = cmdDict.ContainsKey("command") ? cmdDict["command"] as string : null;

                if (string.IsNullOrEmpty(reqId) || string.IsNullOrEmpty(cmdName)) return null;

                Dictionary<string, object> payloadDict = null;
                if (cmdDict.ContainsKey("payload") && cmdDict["payload"] is Dictionary<string, object>)
                {
                    payloadDict = (Dictionary<string, object>)cmdDict["payload"];
                }

                CommandItem item = new CommandItem();
                item.RequestId = reqId.Trim();
                item.Command = cmdName.Trim();
                item.Payload = payloadDict;
                return item;
            }
            catch (Exception ex)
            {
                Log(string.Format("WARN: ParseCommandFromJson exception: {0}", ex.Message));
                return null;
            }
        }

        #endregion

        #region Logging

        private static readonly object _fileLock = new object();

        private static void Log(string message)
        {
            if (message != null && message.StartsWith("DIAG:") &&
                (message.Contains("GET_TELEMETRY") || message.Contains("SendHttpPost OK")))
            {
                return; // suppress high-frequency telemetry polling noise
            }
            try
            {
                if (!Directory.Exists(LogDirectory))
                {
                    Directory.CreateDirectory(LogDirectory);
                }

                string line = string.Format("[{0:yyyy-MM-dd HH:mm:ss.fff}] {1}", DateTime.UtcNow, message);
                lock (_fileLock)
                {
                    File.AppendAllText(LogFilePath, line + Environment.NewLine, Encoding.UTF8);
                }
            }
            catch { }
        }

        #endregion

        #region Inner Data Classes

        private class ModelCatalogItem
        {
            public string ModelName { get; set; }
            public int Weight { get; set; }
        }

        private class CrowdGroup
        {
            public string GroupId { get; set; }
            public string Name { get; set; }
            public string PrimaryModel { get; set; }
            public List<ModelCatalogItem> Models { get; set; }
            public int TargetCount { get; set; }
            public int SpawnedCount { get; set; }
            public int FailedCount { get; set; }
            public int PendingCount { get; set; }
            public float SpawnRadius { get; set; }
            public float MovementRadius { get; set; }
            public float SpawnRate { get; set; }
            public string Behavior { get; set; }
            public float FollowDistance { get; set; }
            public bool DensityAware { get; set; }
            public float DensityLimit { get; set; }
            public string Status { get; set; }
            public DateTime CreatedAt { get; set; }
            public Vector3 SpawnCenter { get; set; }
            public List<int> MemberHandles { get; set; }
            public int LeaderHandle { get; set; }
            public List<Vector3> PatrolWaypoints { get; set; }

            // Stage 4 Route & Visual Fields
            public Vector3? Origin { get; set; }
            public float OriginRadius { get; set; }
            public Vector3? Destination { get; set; }
            public float DestinationRadius { get; set; }
            public List<Vector3> RouteWaypoints { get; set; }
            public float MoveSpeed { get; set; }
            public string ArrivalBehavior { get; set; }
            public string Color { get; set; }
            public bool VehicleCleanup { get; set; }
            public bool DespawnCheckpointEnabled { get; set; }
            public Vector3? DespawnCheckpoint { get; set; }
            public float DespawnRadius { get; set; }
            public bool ContinuousStream { get; set; }
            public int ExitedCount { get; set; }
            public float VehicleCleanupRadius { get; set; }
            public string VehicleCleanupCenter { get; set; }

            public Dictionary<string, Model> ModelPool { get; set; }
            public Dictionary<string, bool> ModelRequestedPool { get; set; }
            public Dictionary<string, bool> ModelLoadedPool { get; set; }
            public Dictionary<string, DateTime> ModelRequestStartPool { get; set; }

            public DateTime LastSpawnTime { get; set; }
            public DateTime LastBehaviorUpdate { get; set; }
            public int CurrentPatrolIndex { get; set; }
            public int RouteVersion { get; set; }

            public CrowdGroup()
            {
                MemberHandles = new List<int>();
                Models = new List<ModelCatalogItem>();
                PatrolWaypoints = new List<Vector3>();
                RouteWaypoints = new List<Vector3>();
                ModelPool = new Dictionary<string, Model>(StringComparer.OrdinalIgnoreCase);
                ModelRequestedPool = new Dictionary<string, bool>(StringComparer.OrdinalIgnoreCase);
                ModelLoadedPool = new Dictionary<string, bool>(StringComparer.OrdinalIgnoreCase);
                ModelRequestStartPool = new Dictionary<string, DateTime>(StringComparer.OrdinalIgnoreCase);
                LastSpawnTime = DateTime.MinValue;
                LastBehaviorUpdate = DateTime.MinValue;
                LeaderHandle = 0;
                FollowDistance = 3.0f;
                MovementRadius = 30.0f;
                DensityAware = false;
                DensityLimit = 0.2f;
                CurrentPatrolIndex = 0;
                Origin = null;
                OriginRadius = 5.0f;
                Destination = null;
                DestinationRadius = 8.0f;
                MoveSpeed = 1.4f;
                ArrivalBehavior = "WANDER";
                Color = "#38bdf8";
                DespawnCheckpointEnabled = false;
                DespawnCheckpoint = null;
                DespawnRadius = 8.0f;
                ContinuousStream = true;
                ExitedCount = 0;
            }
        }

        private class CrowdPedRecord
        {
            public int Handle { get; set; }
            public string ModelName { get; set; }
            public DateTime CreatedAt { get; set; }
            public string GroupId { get; set; }

            // Stage 4 Navigation Fields
            public int CurrentWaypointIndex { get; set; }
            public bool IsReverseRoute { get; set; }
            public bool HasReachedDestination { get; set; }
            public bool HeadingToDespawn { get; set; }
            public Vector3 DispersedDestination { get; set; }
            public Vector3 DispersedOrigin { get; set; }
            public DateTime LastTaskAssignTime { get; set; }
            public int RouteVersion { get; set; }
        }

        private class CommandItem
        {
            public string RequestId { get; set; }
            public string Command { get; set; }
            public Dictionary<string, object> Payload { get; set; }
        }

        #endregion
    
        #region Ambient Suppression & Entity Purging
        private DateTime _lastAmbientSweep = DateTime.MinValue;

        private void SweepAmbientEntities()
        {
            try
            {
                SyncWorldPropsWithManager();
                Ped playerPed = Game.Player.Character;
                HashSet<int> crowdHandles = new HashSet<int>();
                lock (_lock)
                {
                    foreach (CrowdPedRecord r in _crowdRegistry)
                    {
                        crowdHandles.Add(r.Handle);
                    }
                }

                foreach (Ped p in World.GetAllPeds())
                {
                    if (p != null && p.Exists() && (playerPed == null || p.Handle != playerPed.Handle) && !crowdHandles.Contains(p.Handle))
                    {
                        p.IsPersistent = false;
                        p.Delete();
                    }
                }

                foreach (Vehicle v in World.GetAllVehicles())
                {
                    if (v != null && v.Exists() && (playerPed == null || !playerPed.IsInVehicle(v)))
                    {
                        v.IsPersistent = false;
                        v.Delete();
                    }
                }
            }
            catch { }
        }
        #endregion

}
}
