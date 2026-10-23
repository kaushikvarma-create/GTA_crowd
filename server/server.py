# -*- coding: utf-8 -*-
"""
GTA V Legacy Crowd Simulation - Stage 4 Python HTTP Bridge
Provides a bi-directional HTTP interface between the browser dashboard and the ScriptHookVDotNet C# script.
Now supports Stage 4: Map-first Interface with Docked Sidebar, Live Telemetry Ingestion, Saved Points, Route Travel, Heatmap, and Ambient Vehicle Cleanup.
"""

import os
import sys
import json
import time
import re
import mimetypes
import threading
from collections import deque
from http.server import HTTPServer, BaseHTTPRequestHandler
import urllib.parse

try:
    from http.server import ThreadingHTTPServer as _BaseHTTPServer
except ImportError:
    from socketserver import ThreadingMixIn
    class _BaseHTTPServer(ThreadingMixIn, HTTPServer):
        daemon_threads = True

HOST = "127.0.0.1"
PORT = 8088
COMMAND_TIMEOUT_SEC = 6.0
MAX_QUEUE_SIZE = 128
MAX_PAYLOAD_BYTES = 256 * 1024  # 256 KB

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
STATIC_DIR = os.path.join(BASE_DIR, "static")
EXPERIMENTS_DIR = os.path.join(os.path.dirname(BASE_DIR), "experiments")
PATHS_DB_FILE = os.path.join(EXPERIMENTS_DIR, "paths_db.json")

def load_paths_db():
    if not os.path.exists(PATHS_DB_FILE):
        return []
    try:
        with open(PATHS_DB_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
            if isinstance(data, list):
                return data
            elif isinstance(data, dict) and "paths" in data:
                return data["paths"]
            return []
    except Exception as ex:
        print(f"[PATHS_DB] Error loading: {ex}")
        return []

def save_paths_db(paths):
    os.makedirs(EXPERIMENTS_DIR, exist_ok=True)
    with open(PATHS_DB_FILE, "w", encoding="utf-8") as f:
        json.dump({"paths": paths}, f, indent=2)
os.makedirs(EXPERIMENTS_DIR, exist_ok=True)

# Supported commands
ALLOWED_COMMANDS = {
    # Stage 3C
    "PING_GAME",
    "SPAWN_PED",
    "CLEAR_PEDS",
    "CREATE_GROUP",
    "GET_GROUPS",
    "GET_GROUP_STATUS",
    "REMOVE_GROUP",
    "CLEAR_ALL_GROUPS",
    "SET_GROUP_LEADER",
    # Stage 4
    "SET_EXPERIMENT",
    "START_EXPERIMENT",
    "PAUSE_EXPERIMENT",
    "RESUME_EXPERIMENT",
    "STOP_EXPERIMENT",
    "RESET_EXPERIMENT",
    "CLEANUP_VEHICLES",
    "GET_TELEMETRY",
    "UPDATE_GROUP",
    "START_GROUP",
    "PAUSE_GROUP"
}

# Supported behaviors
ALLOWED_BEHAVIORS = {
    "INDEPENDENT_WANDER",
    "COHESIVE_WANDER",
    "FOLLOW_LEADER",
    "STATIONARY_GATHERING",
    "PATROL",
    "FOLLOW_PLAYER",
    "ROUTE_TRAVEL"
}

ALLOWED_ARRIVAL_BEHAVIORS = {
    "STOP",
    "WANDER",
    "GATHER",
    "NEXT_WAYPOINT",
    "LOOP_ROUTE",
    "LOOP",
    "PING_PONG",
    "CYCLE",
    "DESPAWN",
    "DESPAWN_AT_DEST"
}

# Pedestrian Model Catalogue Presets
MODEL_PRESETS = {
    "casual": [
        {"model": "a_m_y_hipster_01", "weight": 50},
        {"model": "a_m_y_hipster_02", "weight": 50}
    ],
    "business": [
        {"model": "a_m_m_business_01", "weight": 50},
        {"model": "a_f_y_business_01", "weight": 50}
    ],
    "tourist": [
        {"model": "a_m_m_tourist_01", "weight": 50},
        {"model": "a_f_y_tourist_01", "weight": 50}
    ],
    "construction": [
        {"model": "s_m_y_construct_01", "weight": 100}
    ],
    "security": [
        {"model": "s_m_m_security_01", "weight": 70},
        {"model": "s_m_y_cop_01", "weight": 30}
    ],
    "emergency": [
        {"model": "s_m_m_paramedic_01", "weight": 50},
        {"model": "s_m_y_fireman_01", "weight": 50}
    ]
}

# Thread synchronization
lock = threading.Lock()
command_queue = deque()  # FIFO bounded queue for GTA V poller
pending_waiters = {}     # req_id -> threading.Event()
acknowledgements = {}    # req_id -> response dict
last_game_poll = 0.0
stats = {
    "commands_received": 0,
    "commands_sent": 0,
    "commands_acknowledged": 0,
    "timeouts": 0
}

latest_telemetry = {
    "updated_at": 0.0,
    "full_updated_at": 0.0,
    "player": {
        "valid": False,
        "x": None,
        "y": None,
        "z": None,
        "heading": 0.0
    },
    "experiment": {"name": "Default", "state": "STOPPED", "shape": "RECTANGLE"},
    "groups": [],
    "peds": [],
    "heatmap": {"grid_resolution": 8.0, "cells": []}
}

_request_counter = 0
_last_auto_tele_req = 0.0


class BridgeHandler(BaseHTTPRequestHandler):
    def log_message(self, format, *args):
        msg = format % args
        if "/api/game/poll" not in msg and "/api/status" not in msg and "/api/telemetry" not in msg and "/gtav_map.jpg" not in msg:
            sys.stdout.write(f"[HTTP] {self.address_string()} - {msg}\n")

    def _send_json(self, status_code, data):
        body = json.dumps(data).encode("utf-8")
        self.send_response(status_code)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Methods", "GET, POST, HEAD, OPTIONS")
        self.send_header("Access-Control-Allow-Headers", "Content-Type, Authorization, X-Requested-With")
        self.end_headers()
        self.wfile.write(body)

    def do_OPTIONS(self):
        self.send_response(200)
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Methods", "GET, POST, HEAD, OPTIONS")
        self.send_header("Access-Control-Allow-Headers", "Content-Type, Authorization, X-Requested-With")
        self.send_header("Content-Length", "0")
        self.end_headers()

    def do_HEAD(self):
        self._serve_static(send_body=False)

    def do_GET(self):
        global last_game_poll, _request_counter
        parsed = urllib.parse.urlparse(self.path)
        path = parsed.path
        query = urllib.parse.parse_qs(parsed.query)

        # 1. API: Server and Game Status
        if path == "/api/status":
            with lock:
                data = {
                    "server_time": time.time(),
                    "game_connected": (time.time() - last_game_poll) < 3.5 if last_game_poll > 0 else False,
                    "pending_queue_length": len(command_queue),
                    "seconds_since_last_game_poll": round(time.time() - last_game_poll, 2) if last_game_poll > 0 else None,
                    "stats": dict(stats),
                    "supported_presets": list(MODEL_PRESETS.keys()),
                    "supported_behaviors": list(ALLOWED_BEHAVIORS),
                    "supported_arrival_behaviors": list(ALLOWED_ARRIVAL_BEHAVIORS)
                }
            self._send_json(200, data)
            return

        # 2. API: Fast Telemetry Cache & Active Polling Fallback
        if path == "/api/telemetry":
            now = time.time()
            with lock:
                game_connected = (now - last_game_poll) < 3.5 if last_game_poll > 0 else False

                # Active telemetry fallback: if game is connected and full telemetry is older than 1.0s, queue GET_TELEMETRY
                global _last_auto_tele_req
                if game_connected and (now - latest_telemetry.get("full_updated_at", 0)) > 1.0 and (now - _last_auto_tele_req) > 1.0 and len(command_queue) == 0:
                    _last_auto_tele_req = now
                    _request_counter += 1
                    auto_req_id = f"cmd_{int(now*1000)}_{_request_counter}"
                    command_queue.append({
                        "request_id": auto_req_id,
                        "command": "GET_TELEMETRY",
                        "payload": {},
                        "created_at": now
                    })

                data = {
                    "game_connected": game_connected,
                    "seconds_since_last_game_poll": round(now - last_game_poll, 2) if last_game_poll > 0 else None,
                    "telemetry": latest_telemetry
                }
            self._send_json(200, data)
            return

        # 2b. API: User Paths Database
        if path in ("/api/paths", "/api/paths/list"):
            self._send_json(200, {"paths": load_paths_db()})
            return

        # 3. API: Saved Experiments List
        if path == "/api/experiment/list":
            items = []
            try:
                for fname in os.listdir(EXPERIMENTS_DIR):
                    if fname.endswith(".json"):
                        fpath = os.path.join(EXPERIMENTS_DIR, fname)
                        try:
                            with open(fpath, "r", encoding="utf-8") as f:
                                exp_data = json.load(f)
                            items.append({
                                "filename": fname,
                                "name": exp_data.get("name", os.path.splitext(fname)[0]),
                                "shape": exp_data.get("shape", "RECTANGLE"),
                                "groups_count": len(exp_data.get("groups", [])),
                                "points_count": len(exp_data.get("saved_points", [])),
                                "modified": os.path.getmtime(fpath)
                            })
                        except Exception:
                            items.append({"filename": fname, "name": os.path.splitext(fname)[0]})
            except Exception as ex:
                self._send_json(500, {"error": f"Failed listing experiments: {ex}"})
                return
            self._send_json(200, {"experiments": items})
            return

        # 4. API: Load Experiment
        if path == "/api/experiment/load":
            name = query.get("name", [""])[0].strip()
            if not name:
                self._send_json(400, {"error": "Missing 'name' query parameter"})
                return
            safe_name = re.sub(r'[^a-zA-Z0-9_\-\s]', '', name).strip()
            if not safe_name.endswith(".json"):
                filename = safe_name + ".json"
            else:
                filename = safe_name
            fpath = os.path.join(EXPERIMENTS_DIR, filename)
            if not os.path.isfile(fpath):
                self._send_json(404, {"error": f"Experiment '{filename}' not found"})
                return
            try:
                with open(fpath, "r", encoding="utf-8") as f:
                    exp_data = json.load(f)
                self._send_json(200, {"status": "ok", "experiment": exp_data})
            except Exception as ex:
                self._send_json(500, {"error": f"Failed loading experiment: {ex}"})
            return

        # 5. API: GTA V Game Poller (called periodically by C# script)
        if path == "/api/game/poll":
            cmd_to_send = None
            now = time.time()
            with lock:
                last_game_poll = now

                # Ingest live player coordinates directly from query parameters if provided
                if "px" in query and "py" in query:
                    try:
                        px_val = round(float(query["px"][0]), 2)
                        py_val = round(float(query["py"][0]), 2)
                        pz_val = round(float(query.get("pz", [0.0])[0]), 2)
                        h_val = round(float(query.get("h", [0.0])[0]), 1)
                        handle_val = int(query.get("handle", [-1])[0])

                        latest_telemetry["player"] = {
                            "valid": True,
                            "x": px_val,
                            "y": py_val,
                            "z": pz_val,
                            "heading": h_val,
                            "handle": handle_val
                        }
                        latest_telemetry["updated_at"] = now
                    except (ValueError, IndexError):
                        pass

                while command_queue:
                    candidate = command_queue.popleft()
                    # Skip expired commands
                    if (now - candidate.get("created_at", now)) < COMMAND_TIMEOUT_SEC:
                        cmd_to_send = candidate
                        break

            if cmd_to_send is not None:
                print(f"[BRIDGE] Dispatching command to game: {cmd_to_send['command']} (ReqID: {cmd_to_send['request_id']})")
                self._send_json(200, {"has_command": True, "command": cmd_to_send})
            else:
                self._send_json(200, {"has_command": False})
            return

        # 6. Static Web Dashboard Files
        self._serve_static(send_body=True)

    def _serve_static(self, send_body=True):
        parsed = urllib.parse.urlparse(self.path)
        path = parsed.path

        file_path = None
        if path == "/" or path == "/index.html":
            file_path = os.path.join(STATIC_DIR, "index.html")
        else:
            # Handle both /static/filename.ext and /filename.ext
            if path.startswith("/static/"):
                rel_path = path[len("/static/"):]
            else:
                rel_path = path.lstrip("/")
            safe_rel = os.path.normpath(rel_path).replace("\\", "/")
            candidate = os.path.join(STATIC_DIR, safe_rel)
            if candidate.startswith(STATIC_DIR) and os.path.isfile(candidate):
                file_path = candidate

        if file_path and os.path.isfile(file_path):
            try:
                file_size = os.path.getsize(file_path)
                ext = os.path.splitext(file_path)[1].lower()
                mime_map = {
                    ".html": "text/html; charset=utf-8",
                    ".js": "text/javascript; charset=utf-8",
                    ".css": "text/css; charset=utf-8",
                    ".jpg": "image/jpeg",
                    ".jpeg": "image/jpeg",
                    ".png": "image/png",
                    ".webp": "image/webp",
                    ".svg": "image/svg+xml",
                    ".json": "application/json"
                }
                content_type = mime_map.get(ext, mimetypes.guess_type(file_path)[0] or "application/octet-stream")

                self.send_response(200)
                self.send_header("Content-Type", content_type)
                self.send_header("Content-Length", str(file_size))
                self.send_header("Access-Control-Allow-Origin", "*")
                self.end_headers()

                if send_body:
                    with open(file_path, "rb") as f:
                        while True:
                            chunk = f.read(64 * 1024)
                            if not chunk:
                                break
                            self.wfile.write(chunk)
            except (ConnectionResetError, BrokenPipeError):
                pass
            except Exception as e:
                try:
                    self._send_json(500, {"error": f"Failed reading file: {e}"})
                except Exception:
                    pass
        else:
            self._send_json(404, {"error": "Not Found"})

    def do_POST(self):
        global _request_counter, latest_telemetry
        parsed = urllib.parse.urlparse(self.path)
        path = parsed.path

        content_len = self.headers.get("Content-Length")
        if not content_len:
            self._send_json(411, {"error": "Length Required"})
            return

        try:
            length = int(content_len)
        except ValueError:
            self._send_json(400, {"error": "Invalid Content-Length"})
            return

        if length > MAX_PAYLOAD_BYTES:
            self._send_json(413, {"error": "Payload Too Large (max 256 KB)"})
            return

        try:
            raw_body = self.rfile.read(length)
            body_json = json.loads(raw_body.decode("utf-8")) if raw_body else {}
        except Exception as ex:
            self._send_json(400, {"error": f"Invalid JSON payload: {ex}"})
            return

        # API: Paths Database Save
        if path == "/api/paths/save":
            path_item = body_json.get("path", body_json)
            pid = str(path_item.get("id", f"path_{int(time.time() * 1000)}")).strip()
            name = str(path_item.get("name", "Custom Path")).strip() or "Custom Path"
            
            existing = load_paths_db()
            found = False
            for idx, p in enumerate(existing):
                if str(p.get("id")) == pid:
                    existing[idx] = {
                        "id": pid,
                        "name": name,
                        "origin": path_item.get("origin"),
                        "origin_radius": float(path_item.get("origin_radius", 10.0)),
                        "destination": path_item.get("destination"),
                        "destination_radius": float(path_item.get("destination_radius", 15.0)),
                        "waypoints": path_item.get("waypoints", []),
                        "speed": float(path_item.get("speed", 1.0)),
                        "behavior": str(path_item.get("behavior", "ROUTE_TRAVEL")),
                        "arrival_behavior": str(path_item.get("arrival_behavior", "WANDER")),
                        "color": str(path_item.get("color", "#38bdf8")),
                        "updated_at": time.time()
                    }
                    found = True
                    break
            if not found:
                existing.append({
                    "id": pid,
                    "name": name,
                    "origin": path_item.get("origin"),
                    "origin_radius": float(path_item.get("origin_radius", 10.0)),
                    "destination": path_item.get("destination"),
                    "destination_radius": float(path_item.get("destination_radius", 15.0)),
                    "waypoints": path_item.get("waypoints", []),
                    "speed": float(path_item.get("speed", 1.0)),
                    "behavior": str(path_item.get("behavior", "ROUTE_TRAVEL")),
                    "arrival_behavior": str(path_item.get("arrival_behavior", "WANDER")),
                    "color": str(path_item.get("color", "#38bdf8")),
                    "created_at": time.time()
                })
            save_paths_db(existing)
            self._send_json(200, {"status": "ok", "id": pid, "paths_count": len(existing)})
            return

        # API: Paths Database Delete
        if path == "/api/paths/delete":
            pid = str(body_json.get("id", "")).strip()
            if not pid:
                self._send_json(400, {"error": "Missing 'id' parameter"})
                return
            existing = load_paths_db()
            filtered = [p for p in existing if str(p.get("id")) != pid]
            save_paths_db(filtered)
            self._send_json(200, {"status": "ok", "deleted_id": pid, "paths_count": len(filtered)})
            return

        # API: Save Experiment
        if path == "/api/experiment/save":
            name = body_json.get("name", "").strip()
            exp_data = body_json.get("experiment", body_json)
            if not name:
                name = exp_data.get("name", "experiment").strip()
            if not name:
                self._send_json(400, {"error": "Experiment 'name' is required"})
                return
            safe_name = re.sub(r'[^a-zA-Z0-9_\-\s]', '', name).strip() or "experiment"
            filename = safe_name if safe_name.endswith(".json") else safe_name + ".json"
            fpath = os.path.join(EXPERIMENTS_DIR, filename)
            try:
                with open(fpath, "w", encoding="utf-8") as f:
                    json.dump(exp_data, f, indent=2)
                self._send_json(200, {"status": "ok", "filename": filename, "saved_at": time.time()})
            except Exception as ex:
                self._send_json(500, {"error": f"Failed saving experiment: {ex}"})
            return

        # API: Command from Dashboard
        if path == "/api/command":
            cmd_name = body_json.get("command", "").strip().upper()
            if cmd_name not in ALLOWED_COMMANDS:
                self._send_json(400, {
                    "error": f"Unknown or disallowed command: '{cmd_name}'. Allowed: {sorted(list(ALLOWED_COMMANDS))}"
                })
                return

            payload = body_json.get("payload", {})
            if not isinstance(payload, dict):
                self._send_json(400, {"error": "'payload' must be a JSON object"})
                return

            # Validation per command
            if cmd_name == "SPAWN_PED":
                model = payload.get("model", "a_m_y_hipster_01")
                if not isinstance(model, str) or not model.strip():
                    self._send_json(400, {"error": "'model' must be a non-empty string"})
                    return
                distance = payload.get("distance", 4.0)
                if not isinstance(distance, (int, float)) or isinstance(distance, bool) or not (2.0 <= float(distance) <= 10.0):
                    self._send_json(400, {"error": "'distance' must be a number between 2.0 and 10.0 metres"})
                    return
                behavior = payload.get("behavior", "wander")
                if not isinstance(behavior, str) or behavior.strip().lower() != "wander":
                    self._send_json(400, {"error": "'behavior' must be 'wander'"})
                    return

            elif cmd_name == "CREATE_GROUP":
                name = payload.get("name", "Group_A")
                if not isinstance(name, str) or not name.strip() or len(name.strip()) > 40:
                    self._send_json(400, {"error": "'name' must be a non-empty string with maximum 40 characters"})
                    return

                count = payload.get("count", 50)
                if not isinstance(count, int) or isinstance(count, bool) or not (1 <= count <= 1000):
                    self._send_json(400, {"error": "'count' must be an integer between 1 and 1000"})
                    return

                radius = payload.get("spawn_radius", payload.get("radius", 20.0))
                if not isinstance(radius, (int, float)) or isinstance(radius, bool) or not (1.0 <= float(radius) <= 200.0):
                    self._send_json(400, {"error": "'spawn_radius' must be a number between 1.0 and 200.0 metres"})
                    return
                payload["spawn_radius"] = float(radius)

                spawn_rate = payload.get("spawn_rate", 2.0)
                if not isinstance(spawn_rate, (int, float)) or isinstance(spawn_rate, bool) or not (0.5 <= float(spawn_rate) <= 100.0):
                    self._send_json(400, {"error": "'spawn_rate' must be a number between 0.5 and 100.0 pedestrians/second"})
                    return
                payload["spawn_rate"] = float(spawn_rate)

                behavior = payload.get("behavior", "INDEPENDENT_WANDER").strip().upper()
                if behavior not in ALLOWED_BEHAVIORS:
                    self._send_json(400, {"error": f"'behavior' must be one of {sorted(list(ALLOWED_BEHAVIORS))}"})
                    return
                payload["behavior"] = behavior

                # Stage 4 Route & Destination validation
                if "origin" in payload and payload["origin"]:
                    orig = payload["origin"]
                    if not isinstance(orig, dict) or "x" not in orig or "y" not in orig:
                        self._send_json(400, {"error": "'origin' must be an object with 'x' and 'y' coordinates"})
                        return

                if "destination" in payload and payload["destination"]:
                    dest = payload["destination"]
                    if not isinstance(dest, dict) or "x" not in dest or "y" not in dest:
                        self._send_json(400, {"error": "'destination' must be an object with 'x' and 'y' coordinates"})
                        return
                    dest_rad = payload.get("destination_radius", 15.0)
                    if not isinstance(dest_rad, (int, float)) or isinstance(dest_rad, bool) or not (1.0 <= float(dest_rad) <= 200.0):
                        self._send_json(400, {"error": "'destination_radius' must be between 1.0 and 200.0 metres"})
                        return
                    payload["destination_radius"] = float(dest_rad)

                if "arrival_behavior" in payload:
                    arr = str(payload["arrival_behavior"]).strip().upper()
                    if arr not in ALLOWED_ARRIVAL_BEHAVIORS:
                        self._send_json(400, {"error": f"'arrival_behavior' must be one of {sorted(list(ALLOWED_ARRIVAL_BEHAVIORS))}"})
                        return
                    payload["arrival_behavior"] = arr

                if "move_speed" in payload:
                    spd = payload["move_speed"]
                    if not isinstance(spd, (int, float)) or isinstance(spd, bool) or not (0.5 <= float(spd) <= 4.0):
                        self._send_json(400, {"error": "'move_speed' must be a number between 0.5 and 4.0"})
                        return
                    payload["move_speed"] = float(spd)

                preset_name = payload.get("preset")
                if preset_name is not None:
                    if not isinstance(preset_name, str) or preset_name.strip().lower() not in MODEL_PRESETS:
                        self._send_json(400, {"error": f"'preset' must be one of {sorted(list(MODEL_PRESETS.keys()))}"})
                        return
                    payload["models"] = MODEL_PRESETS[preset_name.strip().lower()]
                    payload["model"] = payload["models"][0]["model"]
                elif "models" in payload and isinstance(payload["models"], list):
                    models_list = payload["models"]
                    if len(models_list) == 0:
                        self._send_json(400, {"error": "'models' array cannot be empty"})
                        return
                    for item in models_list:
                        if not isinstance(item, dict) or "model" not in item:
                            self._send_json(400, {"error": "Each item in 'models' must be an object with a 'model' string and optional 'weight'"})
                            return
                        if not isinstance(item["model"], str) or not item["model"].strip():
                            self._send_json(400, {"error": "'model' in 'models' list must be a non-empty string"})
                            return
                    payload["model"] = models_list[0]["model"]
                else:
                    model = payload.get("model", "a_m_y_hipster_01")
                    if not isinstance(model, str) or not model.strip():
                        self._send_json(400, {"error": "'model' must be a non-empty string"})
                        return
                    payload["model"] = model.strip()

            elif cmd_name == "SET_EXPERIMENT":
                name = payload.get("name", "Experiment_1")
                if not isinstance(name, str) or not name.strip() or len(name.strip()) > 60:
                    self._send_json(400, {"error": "'name' must be a non-empty string with maximum 60 characters"})
                    return
                shape = payload.get("shape", "RECTANGLE").strip().upper()
                if shape not in {"RECTANGLE", "CIRCLE"}:
                    self._send_json(400, {"error": "'shape' must be 'RECTANGLE' or 'CIRCLE'"})
                    return
                center = payload.get("center", {})
                if not isinstance(center, dict) or "x" not in center or "y" not in center:
                    self._send_json(400, {"error": "'center' must be an object with 'x' and 'y' coordinates"})
                    return
                if shape == "RECTANGLE":
                    w = payload.get("width", 200.0)
                    h = payload.get("height", 200.0)
                    if not (isinstance(w, (int, float)) and isinstance(h, (int, float)) and 20.0 <= float(w) <= 2000.0 and 20.0 <= float(h) <= 2000.0):
                        self._send_json(400, {"error": "'width' and 'height' must be numbers between 20.0 and 2000.0 metres"})
                        return
                elif shape == "CIRCLE":
                    r = payload.get("radius", 100.0)
                    if not (isinstance(r, (int, float)) and 10.0 <= float(r) <= 1500.0):
                        self._send_json(400, {"error": "'radius' must be a number between 10.0 and 1500.0 metres"})
                        return

            elif cmd_name in {"GET_GROUP_STATUS", "REMOVE_GROUP", "START_GROUP", "PAUSE_GROUP"}:
                group_id = payload.get("group_id") or payload.get("id")
                if not isinstance(group_id, str) or not group_id.strip():
                    self._send_json(400, {"error": f"'{cmd_name}' requires a non-empty string 'group_id' in payload"})
                    return
                payload["group_id"] = group_id.strip()

            elif cmd_name == "UPDATE_GROUP":
                group_id = payload.get("group_id") or payload.get("id")
                if not isinstance(group_id, str) or not group_id.strip():
                    self._send_json(400, {"error": "'UPDATE_GROUP' requires a non-empty string 'group_id' in payload"})
                    return
                payload["group_id"] = group_id.strip()

                if "count" in payload:
                    try:
                        c = int(payload["count"])
                        if not (1 <= c <= 1000):
                            self._send_json(400, {"error": "'count' must be between 1 and 1000"})
                            return
                        payload["count"] = c
                    except (ValueError, TypeError):
                        self._send_json(400, {"error": "'count' must be a valid integer"})
                        return

                if "spawn_rate" in payload:
                    try:
                        sr = float(payload["spawn_rate"])
                        if not (0.5 <= sr <= 100.0):
                            self._send_json(400, {"error": "'spawn_rate' must be between 0.5 and 100.0"})
                            return
                        payload["spawn_rate"] = sr
                    except (ValueError, TypeError):
                        self._send_json(400, {"error": "'spawn_rate' must be a valid number"})
                        return

            elif cmd_name == "CLEANUP_VEHICLES":
                if "radius" in payload and payload["radius"] is not None:
                    try:
                        r = float(payload["radius"])
                        if not (5.0 <= r <= 500.0):
                            self._send_json(400, {"error": "'radius' must be between 5.0 and 500.0 metres"})
                            return
                        payload["radius"] = r
                    except (ValueError, TypeError):
                        self._send_json(400, {"error": "'radius' must be a valid number"})
                        return
                if "center_x" in payload and payload["center_x"] is not None:
                    try:
                        payload["center_x"] = float(payload["center_x"])
                        payload["center_y"] = float(payload["center_y"])
                    except (ValueError, TypeError, KeyError):
                        self._send_json(400, {"error": "'center_x' and 'center_y' must be valid numbers"})
                        return

            # Generate request ID
            start_time = time.time()
            with lock:
                _request_counter += 1
                req_id = f"cmd_{int(start_time*1000)}_{_request_counter}"
                stats["commands_received"] += 1

                if len(command_queue) >= MAX_QUEUE_SIZE:
                    self._send_json(503, {"error": "Bridge command queue is full. Try again shortly."})
                    return

                event = threading.Event()
                pending_waiters[req_id] = event
                command_queue.append({
                    "request_id": req_id,
                    "command": cmd_name,
                    "payload": payload,
                    "created_at": start_time
                })
                stats["commands_sent"] += 1

            # Await acknowledgement from GTA V game thread
            signaled = event.wait(timeout=COMMAND_TIMEOUT_SEC)
            elapsed = time.time() - start_time

            with lock:
                pending_waiters.pop(req_id, None)
                ack_response = acknowledgements.pop(req_id, None)

            if signaled and ack_response is not None:
                self._send_json(200, {
                    "request_id": req_id,
                    "command": cmd_name,
                    "acknowledged_by_game": True,
                    "latency_sec": round(elapsed, 3),
                    "game_response": ack_response
                })
            else:
                with lock:
                    stats["timeouts"] += 1
                print(f"[BRIDGE] Command TIMEOUT: {cmd_name} (ReqID: {req_id}) after {elapsed:.3f}s")
                self._send_json(504, {
                    "request_id": req_id,
                    "command": cmd_name,
                    "acknowledged_by_game": False,
                    "error": f"Timeout ({COMMAND_TIMEOUT_SEC}s) waiting for GTA V game thread acknowledgment."
                })
            return

        # API: GTA V Game Acknowledgment
        if path == "/api/game/ack":
            req_id = body_json.get("request_id")
            if not req_id:
                self._send_json(400, {"error": "Missing 'request_id' in ack payload"})
                return

            with lock:
                stats["commands_acknowledged"] += 1
                if req_id in pending_waiters:
                    acknowledgements[req_id] = body_json
                    pending_waiters[req_id].set()

                # Ingest player coordinates from ACK
                now = time.time()
                p_data = body_json.get("player") or body_json.get("player_position")
                if isinstance(p_data, dict) and "x" in p_data and "y" in p_data:
                    px_val = round(float(p_data["x"]), 2)
                    py_val = round(float(p_data["y"]), 2)
                    pz_val = round(float(p_data.get("z", 0.0)), 2)
                    h_val = round(float(p_data.get("heading", 0.0)), 1)
                    if px_val != 0.0 or py_val != 0.0:
                        latest_telemetry["player"] = {
                            "valid": True,
                            "x": px_val,
                            "y": py_val,
                            "z": pz_val,
                            "heading": h_val,
                            "handle": body_json.get("player_handle", -1)
                        }
                        latest_telemetry["updated_at"] = now

                has_full = False
                if "experiment" in body_json:
                    latest_telemetry["experiment"] = body_json["experiment"]
                    has_full = True
                if "groups" in body_json:
                    latest_telemetry["groups"] = body_json["groups"]
                    has_full = True
                if "peds" in body_json:
                    latest_telemetry["peds"] = body_json["peds"]
                    has_full = True
                if "heatmap" in body_json:
                    latest_telemetry["heatmap"] = body_json["heatmap"]
                    has_full = True
                if has_full:
                    latest_telemetry["full_updated_at"] = now
                    latest_telemetry["updated_at"] = now

            self._send_json(200, {"status": "ok", "request_id": req_id})
            return

        self._send_json(404, {"error": "Endpoint Not Found"})


def run_server():
    server_address = (HOST, PORT)
    httpd = _BaseHTTPServer(server_address, BridgeHandler)
    httpd.daemon_threads = True
    print(f"[GTA CrowdSim Bridge Stage 4 (Threaded)] Listening on http://{HOST}:{PORT}")
    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        print("\n[GTA CrowdSim Bridge] Shutting down...")
    finally:
        httpd.server_close()


if __name__ == "__main__":
    run_server()
