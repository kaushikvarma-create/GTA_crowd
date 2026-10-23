using System;
using System.IO;
using GTA;
using GTA.UI;

namespace CrowdSim
{
    public class CrowdSimMain : Script
    {
        private bool _isInitialized;
        private static readonly string LogDirectory = @"C:\Users\Teja-Clove\GTA_crowd\logs";
        private static readonly string LogFilePath = Path.Combine(LogDirectory, "crowdsim.log");

        public CrowdSimMain()
        {
            _isInitialized = false;
            Interval = 100;
            Tick += OnTick;
            Log("Script constructor called, waiting for world and player initialization...");
        }

        private static void Log(string message)
        {
            try
            {
                if (!Directory.Exists(LogDirectory))
                {
                    Directory.CreateDirectory(LogDirectory);
                }

                string entry = string.Format("[{0:yyyy-MM-dd HH:mm:ss.fff}] {1}", DateTime.Now, message);
                File.AppendAllText(LogFilePath, entry + Environment.NewLine);
            }
            catch
            {
                // Suppress file I/O errors to prevent interrupting script engine
            }
        }

        private void OnTick(object sender, EventArgs e)
        {
            if (_isInitialized)
            {
                return;
            }

            try
            {
                // Verify player and character existence before triggering notifications
                Player player = Game.Player;
                if (player == null)
                {
                    return;
                }

                Ped playerPed = player.Character;
                if (playerPed == null || !playerPed.Exists())
                {
                    return;
                }

                _isInitialized = true;

                // 1. In-game Ticker notification above the minimap
                Notification.PostTicker("~g~[CrowdSim]~s~ Script loaded successfully!", true, true);

                // 2. Visible center-screen subtitle (3500ms duration)
                Screen.ShowSubtitle("~b~[CrowdSim]~s~ Script loaded successfully!", 3500);

                Log(string.Format("SUCCESS: [CrowdSim] Script loaded successfully! Player handle: {0}", playerPed.Handle));
            }
            catch (Exception ex)
            {
                Log(string.Format("ERROR during initialization: {0}", ex.ToString()));
            }
        }
    }
}
