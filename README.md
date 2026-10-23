# GTA_crowd

Autonomous crowd simulation in Grand Theft Auto V (Legacy build v1.0.3725.0) using ScriptHookVDotNet v3.7.0 for computer vision and trajectory research.

## Project Structure
- `src/CrowdSimMain.cs`: Minimal Stage 1 test script.
- `build.ps1`: Automated build and deployment script.
- `build/`: Local compiled assembly (`CrowdSim.dll`).
- `logs/`: Runtime logs written by the simulation (`crowdsim.log`).

## Building & Deployment
To compile locally:
```powershell
powershell -ExecutionPolicy Bypass -File .\build.ps1
```

To compile and deploy directly to GTA V scripts directory (`D:\Games\Grand Theft Auto V Legacy\scripts\`):
```powershell
powershell -ExecutionPolicy Bypass -File .\build.ps1 -Deploy
```

## Stage Progression
- [x] **Stage 1**: Minimal test script verifying SHVDN v3 API integration and in-game confirmation message.
- [ ] **Stage 2**: Configurable pedestrian spawner with persistent IDs.
- [ ] **Stage 3**: Group assignments and destination-based navigation.
- [ ] **Stage 4**: Ground-truth pedestrian position & timestamp CSV logger.
- [ ] **Stage 5**: External Python live web map with trails.
- [ ] **Stage 6**: Group-level dynamics, arrival detection, and simulation recording.
