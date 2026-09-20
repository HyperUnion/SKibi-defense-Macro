--[[
    SKIBI DEFENSE MACRO ENGINE
    Single-file Roblox executor script

    Core:
      - Record / Pause / Play / Stop
      - Save / Load / Delete / Duplicate macros
      - Auto-save + crash recovery
      - Player waypoint capture
      - Semantic tower placement recording
      - Tower IDs + instance remapping
      - Remote call capture / replay
      - Upgrade recording + fallback keyboard execution
      - Raw event capture for abilities / target mode / speed actions
      - Conditions: cash / wave / tower count / ability-ready-ish
      - Auto-upgrade heuristic with DPS + damage + cost
      - Boost-aware stat scanner when the game exposes numeric attributes/values
      - In-match recovery:
            active match already running -> speed x3 -> wait for defeat
            -> click Again -> click Ready -> restart macro
      - Anti-AFK jump only while idle/waiting
      - Monitor / timeline / debug log
      - Rayfield UI loader (repo-first, official fallback)

    IMPORTANT:
      Skibi Defense's internal RemoteEvent/RemoteFunction names and argument
      schemas are not publicly documented in the sources checked for this build.
      The recorder therefore learns actual client -> server calls during Record.
      It is intentionally not hard-coded to imaginary remote names.
]]

----------------------------------------------------------------
-- SERVICES
----------------------------------------------------------------
local Players            = game:GetService("Players")
local ReplicatedStorage   = game:GetService("ReplicatedStorage")
local RunService          = game:GetService("RunService")
local UserInputService    = game:GetService("UserInputService")
local TweenService        = game:GetService("TweenService")
local HttpService         = game:GetService("HttpService")
local PathfindingService  = game:GetService("PathfindingService")
local VirtualInputManager = game:GetService("VirtualInputManager")
local CoreGui             = game:GetService("CoreGui")
local GuiService          = game:GetService("GuiService")
local Workspace           = workspace

local LocalPlayer = Players.LocalPlayer

----------------------------------------------------------------
-- EXECUTOR COMPATIBILITY
----------------------------------------------------------------
local genv = (getgenv and getgenv()) or _G

local Caps = {
    File = type(writefile) == "function"
        and type(readfile) == "function"
        and type(isfile) == "function"
        and type(makefolder) == "function",

    Hook = type(hookmetamethod) == "function"
        and type(getnamecallmethod) == "function"
        and type(newcclosure) == "function",

    Input = VirtualInputManager ~= nil,

    Http = type(game.HttpGet) == "function" or type(request) == "function",

    Rayfield = false,
}

----------------------------------------------------------------
-- CONSTANTS
----------------------------------------------------------------
local APP = "SkibiMacroEngine"
local ROOT_FOLDER = APP
local MACRO_FOLDER = ROOT_FOLDER .. "/Macros"
local BACKUP_FOLDER = ROOT_FOLDER .. "/Backups"
local SETTINGS_FILE = ROOT_FOLDER .. "/settings.json"
local RECOVER_FILE = BACKUP_FOLDER .. "/recovery.json"

local SCRIPT_VERSION = "1.0.0"

local DEFAULT_SETTINGS = {
    AutoSave = true,
    AutoSaveEvents = 5,
    RecoveryEnabled = true,
    RecoverySpeed = 3,
    RecoveryTimeout = 900,
    AutoRestart = true,
    AntiAFK = true,
    AntiAFKInterval = 45,
    MoveRadius = 1.5,
    MoveTimeout = 25,
    MoveRepath = true,
    RemoteCaptureWindow = 1.5,
    PlacementVerifyDistance = 7,
    PlacementRetry = 3,
    PlacementRetryDelay = 0.25,
    AutoUpgrade = false,
    UpgradeMode = "DPS / Cost",
    UpgradeInterval = 0.75,
    CashReserve = 0,
    MaxRawEventsPerSecond = 12,
    Debug = false,
}

local Settings = {}
for k, v in pairs(DEFAULT_SETTINGS) do
    Settings[k] = v
end

----------------------------------------------------------------
-- STATE
----------------------------------------------------------------
local State = {
    Mode = "IDLE",              -- IDLE / RECORD / PAUSED_RECORD / PLAY / PAUSED_PLAY / RECOVERY / STOPPING
    MacroName = "NewMacro",
    Macro = nil,

    EventIndex = 0,
    PlayIndex = 1,
    RecordStart = 0,
    PlayStart = 0,

    LastRemote = nil,
    RemoteSeq = 0,
    PendingInput = nil,
    PendingPlacement = nil,
    PendingUpgrade = nil,
    LastInputAt = 0,
    RawEventBudget = 0,
    RawEventSecond = 0,

    RuntimeTowers = {},         -- id -> {model, name, position, cframe, level}
    ModelToTowerId = {},        -- model -> id
    NextTowerId = 1,

    Waypoints = {},

    Errors = {},
    Logs = {},

    RunningTask = nil,
    StopToken = 0,

    LastAction = "Idle",
    CurrentCondition = "None",

    Recovering = false,
    RecoveryStarted = 0,

    MacroDirty = false,
    AutoSaveCounter = 0,

    SelectedMacro = nil,
}

----------------------------------------------------------------
-- UTILS
----------------------------------------------------------------
local function now()
    return os.clock()
end

local function wallClock()
    return os.time()
end

local function clamp(n, a, b)
    return math.max(a, math.min(b, n))
end

local function round(n, d)
    local p = 10 ^ (d or 2)
    return math.floor(n * p + 0.5) / p
end

local function safeName(text)
    text = tostring(text or "Unnamed")
    text = text:gsub("[%c]", "")
    text = text:gsub("[\\/:*?\"<>|]", "_")
    text = text:gsub("^%s+", ""):gsub("%s+$", "")
    if text == "" then text = "Unnamed" end
    return text
end

local function fmtTime(seconds)
    seconds = math.max(0, tonumber(seconds) or 0)
    local h = math.floor(seconds / 3600)
    local m = math.floor((seconds % 3600) / 60)
    local s = seconds % 60
    if h > 0 then
        return string.format("%02d:%02d:%05.2f", h, m, s)
    end
    return string.format("%02d:%02d.%02d", m, math.floor(s), math.floor((s * 100) % 100))
end

local function log(message)
    message = "[" .. os.date("%H:%M:%S") .. "] " .. tostring(message)
    table.insert(State.Logs, 1, message)
    while #State.Logs > 80 do
        table.remove(State.Logs)
    end
    if Settings.Debug then
        print("[SkibiMacro] " .. message)
    end
end

local function fail(message)
    message = tostring(message)
    table.insert(State.Errors, 1, message)
    while #State.Errors > 30 do
        table.remove(State.Errors)
    end
    log("ERROR: " .. message)
end

local function notify(title, content, duration)
    if _G.__SkibiMacroNotify then
        pcall(_G.__SkibiMacroNotify, title, content, duration or 3)
    end
end

local function isAlive()
    local char = LocalPlayer.Character
    local hum = char and char:FindFirstChildOfClass("Humanoid")
    return hum and hum.Health > 0, hum
end

local function getRoot()
    local char = LocalPlayer.Character
    return char and (char:FindFirstChild("HumanoidRootPart") or char.PrimaryPart)
end

local function getCamera()
    return Workspace.CurrentCamera
end

local function getPlayerPosition()
    local root = getRoot()
    if not root then return nil end
    return root.Position
end

local function getPlayerCFrame()
    local root = getRoot()
    if not root then return nil end
    return root.CFrame
end

----------------------------------------------------------------
-- FILE SYSTEM
----------------------------------------------------------------
local function ensureFolders()
    if not Caps.File then return false end
    pcall(function()
        if not isfolder(ROOT_FOLDER) then makefolder(ROOT_FOLDER) end
        if not isfolder(MACRO_FOLDER) then makefolder(MACRO_FOLDER) end
        if not isfolder(BACKUP_FOLDER) then makefolder(BACKUP_FOLDER) end
    end)
    return true
end

local function fileExists(path)
    return Caps.File and pcall(function() return isfile(path) end) and isfile(path)
end

local function writeJSON(path, data)
    if not Caps.File then return false, "filesystem API unavailable" end
    local ok, encoded = pcall(function()
        return HttpService:JSONEncode(data)
    end)
    if not ok then return false, "JSON encode failed: " .. tostring(encoded) end

    local success, err = pcall(function()
        writefile(path, encoded)
    end)
    if not success then
        return false, tostring(err)
    end
    return true
end

local function readJSON(path)
    if not Caps.File or not fileExists(path) then
        return nil, "file not found"
    end

    local ok, raw = pcall(function()
        return readfile(path)
    end)
    if not ok then return nil, tostring(raw) end

    local ok2, decoded = pcall(function()
        return HttpService:JSONDecode(raw)
    end)
    if not ok2 then return nil, tostring(decoded) end
    return decoded
end

local function macroPath(name)
    return MACRO_FOLDER .. "/" .. safeName(name) .. ".json"
end

local function saveSettings()
    if not Caps.File then return end
    writeJSON(SETTINGS_FILE, Settings)
end

local function loadSettings()
    local data = readJSON(SETTINGS_FILE)
    if type(data) == "table" then
        for k, v in pairs(DEFAULT_SETTINGS) do
            if data[k] ~= nil then
                Settings[k] = data[k]
            else
                Settings[k] = v
            end
        end
    end
end

ensureFolders()
loadSettings()

----------------------------------------------------------------
-- MACRO FORMAT
----------------------------------------------------------------
local function newMacro(name)
    return {
        schema = 2,
        scriptVersion = SCRIPT_VERSION,
        name = safeName(name or "NewMacro"),
        createdAt = wallClock(),
        updatedAt = wallClock(),

        settings = {
            moveRadius = Settings.MoveRadius,
            moveTimeout = Settings.MoveTimeout,
            recoveryEnabled = Settings.RecoveryEnabled,
            recoverySpeed = Settings.RecoverySpeed,
            autoRestart = Settings.AutoRestart,
        },

        metadata = {
            placeId = game.PlaceId,
            gameId = game.GameId,
            map = "Unknown",
            mode = "Unknown",
            creator = "Archkos Studios",
        },

        waypoints = {},
        towerTemplates = {},
        events = {},
    }
end

State.Macro = newMacro(State.MacroName)

local function sanitizeMacro(macro)
    if type(macro) ~= "table" then
        return newMacro("Recovered")
    end
    macro.schema = tonumber(macro.schema) or 2
    macro.scriptVersion = macro.scriptVersion or SCRIPT_VERSION
    macro.name = safeName(macro.name or "Unnamed")
    macro.events = type(macro.events) == "table" and macro.events or {}
    macro.waypoints = type(macro.waypoints) == "table" and macro.waypoints or {}
    macro.towerTemplates = type(macro.towerTemplates) == "table" and macro.towerTemplates or {}
    macro.metadata = type(macro.metadata) == "table" and macro.metadata or {}
    macro.settings = type(macro.settings) == "table" and macro.settings or {}
    return macro
end

local function saveMacro(name, silent)
    if not Caps.File then
        fail("Save Macro failed: executor has no writefile/isfile support.")
        return false
    end

    name = safeName(name or State.Macro.name)
    State.Macro.name = name
    State.Macro.updatedAt = wallClock()

    local ok, err = writeJSON(macroPath(name), State.Macro)
    if not ok then
        fail("Save Macro: " .. tostring(err))
        return false
    end

    State.MacroDirty = false
    State.AutoSaveCounter = 0

    if not silent then
        notify("Macro Saved", name, 2)
    end
    log("Saved macro: " .. name)
    return true
end

local function saveRecovery()
    if not Caps.File or not State.Macro then return end
    if State.Mode ~= "RECORD" and State.Mode ~= "PAUSED_RECORD" then return end

    local payload = {
        savedAt = wallClock(),
        macro = State.Macro,
        mode = State.Mode,
        selectedMacro = State.Macro.name,
    }

    writeJSON(RECOVER_FILE, payload)
end

local function deleteMacro(name)
    if not Caps.File then return false end
    local path = macroPath(name)
    if not fileExists(path) then return false end

    local ok = pcall(function()
        delfile(path)
    end)
    if ok then
        notify("Macro Deleted", safeName(name), 2)
        log("Deleted macro: " .. safeName(name))
    end
    return ok
end

local function duplicateMacro(sourceName, targetName)
    local data = readJSON(macroPath(sourceName))
    if not data then return false end
    data = sanitizeMacro(data)
    data.name = safeName(targetName)
    data.updatedAt = wallClock()
    data.createdAt = data.createdAt or wallClock()
    local ok = writeJSON(macroPath(targetName), data)
    if ok then
        notify("Macro Duplicated", data.name, 2)
    end
    return ok
end

local function listMacros()
    local results = {}
    if not Caps.File or type(listfiles) ~= "function" then
        if State.Macro then table.insert(results, State.Macro.name) end
        return results
    end

    local ok, files = pcall(function()
        return listfiles(MACRO_FOLDER)
    end)
    if not ok or type(files) ~= "table" then
        return results
    end

    for _, path in ipairs(files) do
        local name = tostring(path):match("([^\\/]+)%.json$")
        if name then
            table.insert(results, name)
        end
    end

    table.sort(results)
    if #results == 0 then
        table.insert(results, State.Macro.name)
    end
    return results
end

local function loadMacro(name)
    name = safeName(name)
    local data, err = readJSON(macroPath(name))
    if not data then
        fail("Load Macro: " .. tostring(err))
        return false
    end

    State.Macro = sanitizeMacro(data)
    State.MacroName = State.Macro.name
    State.MacroDirty = false
    State.PlayIndex = 1
    State.EventIndex = #State.Macro.events

    notify("Macro Loaded", State.Macro.name, 2)
    log("Loaded macro: " .. State.Macro.name .. " (" .. tostring(#State.Macro.events) .. " events)")
    return true
end

----------------------------------------------------------------
-- SERIALIZATION FOR REMOTE ARGS
----------------------------------------------------------------
local function relativePath(instance)
    if not instance or typeof(instance) ~= "Instance" then return nil end

    local ok, full = pcall(function()
        return instance:GetFullName()
    end)
    return ok and full or instance.Name
end

local function findByFullName(full)
    if type(full) ~= "string" or full == "" then return nil end

    if full == "Players." .. LocalPlayer.Name then
        return LocalPlayer
    end

    local segments = {}
    for segment in full:gmatch("[^%.]+") do
        table.insert(segments, segment)
    end

    if #segments == 0 then return nil end

    local rootName = segments[1]
    local current

    if rootName == "Workspace" then
        current = Workspace
    elseif rootName == "ReplicatedStorage" then
        current = ReplicatedStorage
    elseif rootName == "Players" then
        current = Players
    elseif rootName == "CoreGui" then
        current = CoreGui
    elseif rootName == "Lighting" then
        current = game:GetService("Lighting")
    elseif rootName == "StarterGui" then
        current = game:GetService("StarterGui")
    else
        current = game:FindFirstChild(rootName)
    end

    if not current then return nil end

    for i = 2, #segments do
        current = current:FindFirstChild(segments[i])
        if not current then return nil end
    end

    return current
end

local function serialize(value, towerResolver, depth)
    depth = depth or 0
    if depth > 8 then
        return {__type = "string", value = "<depth-limit>"}
    end

    local t = typeof(value)

    if t == "nil" then
        return {__type = "nil"}

    elseif t == "boolean" or t == "string" or t == "number" then
        return {__type = t, value = value}

    elseif t == "Vector3" then
        return {
            __type = "Vector3",
            x = value.X, y = value.Y, z = value.Z
        }

    elseif t == "Vector2" then
        return {
            __type = "Vector2",
            x = value.X, y = value.Y
        }

    elseif t == "CFrame" then
        local components = {value:GetComponents()}
        return {
            __type = "CFrame",
            components = components
        }

    elseif t == "Color3" then
        return {
            __type = "Color3",
            r = value.R, g = value.G, b = value.B
        }

    elseif t == "BrickColor" then
        return {
            __type = "BrickColor",
            number = value.Number,
        }

    elseif t == "EnumItem" then
        return {
            __type = "EnumItem",
            enum = tostring(value.EnumType),
            name = value.Name,
        }

    elseif t == "Instance" then
        if value == LocalPlayer then
            return {__type = "LocalPlayer"}
        end

        local towerId = towerResolver and towerResolver(value)
        if towerId then
            return {
                __type = "TowerRef",
                id = towerId,
            }
        end

        return {
            __type = "Instance",
            path = relativePath(value),
        }

    elseif t == "Ray" then
        return {
            __type = "Ray",
            origin = serialize(value.Origin, towerResolver, depth + 1),
            direction = serialize(value.Direction, towerResolver, depth + 1),
        }

    elseif t == "table" then
        -- Preserve numeric array indices. Remote payloads often use positional
        -- arrays, so converting every key to a string silently breaks them.
        local array = true
        local maxIndex = 0
        for k in pairs(value) do
            if type(k) ~= "number" or k < 1 or k % 1 ~= 0 then
                array = false
                break
            end
            maxIndex = math.max(maxIndex, k)
        end

        local out = {}

        if array then
            for i = 1, maxIndex do
                out[i] = serialize(value[i], towerResolver, depth + 1)
            end
        else
            for k, v in pairs(value) do
                local key
                if typeof(k) == "string" or typeof(k) == "number" then
                    key = k
                else
                    key = tostring(k)
                end
                out[key] = serialize(v, towerResolver, depth + 1)
            end
        end

        return {
            __type = "table",
            array = array,
            value = out,
        }
    end

    return {
        __type = "string",
        value = tostring(value),
    }
end

local function deserialize(value, towerLookup)
    if type(value) ~= "table" then return value end

    local tp = value.__type

    if tp == "nil" then
        return nil

    elseif tp == "boolean" or tp == "string" or tp == "number" then
        return value.value

    elseif tp == "Vector3" then
        return Vector3.new(value.x or 0, value.y or 0, value.z or 0)

    elseif tp == "Vector2" then
        return Vector2.new(value.x or 0, value.y or 0)

    elseif tp == "CFrame" then
        if type(value.components) == "table" and #value.components >= 12 then
            return CFrame.new(table.unpack(value.components))
        end
        return CFrame.new()

    elseif tp == "Color3" then
        return Color3.new(value.r or 0, value.g or 0, value.b or 0)

    elseif tp == "BrickColor" then
        return BrickColor.new(value.number or 1)

    elseif tp == "EnumItem" then
        local enumName = tostring(value.enum or ""):gsub("^Enum%.", "")
        local enumType = Enum[enumName]
        if enumType then
            return enumType[value.name]
        end
        return nil

    elseif tp == "LocalPlayer" then
        return LocalPlayer

    elseif tp == "TowerRef" then
        local tower = towerLookup and towerLookup(tonumber(value.id))
        return tower

    elseif tp == "Instance" then
        return findByFullName(value.path)

    elseif tp == "Ray" then
        return Ray.new(
            deserialize(value.origin, towerLookup),
            deserialize(value.direction, towerLookup)
        )

    elseif tp == "table" then
        local out = {}
        for k, v in pairs(value.value or {}) do
            local key = k
            if value.array then
                key = tonumber(k) or k
            end
            out[key] = deserialize(v, towerLookup)
        end
        return out
    end

    return value.value
end

----------------------------------------------------------------
-- TOWER DISCOVERY / IDs
----------------------------------------------------------------
local IGNORE_MODEL_NAMES = {
    Map = true,
    Path = true,
    Camera = true,
    Effects = true,
    Enemies = true,
    Enemy = true,
    Projectiles = true,
    Towers = false,
}

local function modelPivot(model)
    if not model or not model:IsA("Model") then return nil end
    local ok, cf = pcall(function()
        return model:GetPivot()
    end)
    return ok and cf or nil
end

local function looksLikeTower(model)
    if not model or not model:IsA("Model") then return false end

    local name = tostring(model.Name)
    if IGNORE_MODEL_NAMES[name] then return false end

    local attrs = model:GetAttributes()
    for key, value in pairs(attrs) do
        local lower = tostring(key):lower()
        if lower:find("owner") or lower == "level" or lower:find("tower") or lower:find("unit") then
            if value == LocalPlayer or tostring(value) == tostring(LocalPlayer.UserId) or lower == "level" then
                return true
            end
        end
    end

    local owner = model:FindFirstChild("Owner")
    if owner and owner:IsA("ObjectValue") and owner.Value == LocalPlayer then
        return true
    end

    local level = model:FindFirstChild("Level", true)
    if level and (level:IsA("IntValue") or level:IsA("NumberValue")) then
        return true
    end

    -- Many tower models have a humanoid-free Model + central part and are
    -- descendants of a container named Towers/Units.
    local parentName = model.Parent and tostring(model.Parent.Name):lower() or ""
    if parentName:find("tower") or parentName:find("unit") then
        return true
    end

    return false
end

local function distanceTo(a, b)
    if typeof(a) == "Vector3" and typeof(b) == "Vector3" then
        return (a - b).Magnitude
    end
    return math.huge
end

local function assignTowerId(model, explicitId)
    if not model or not model:IsA("Model") then return nil end
    if State.ModelToTowerId[model] then
        return State.ModelToTowerId[model]
    end

    local id = explicitId or State.NextTowerId
    State.NextTowerId = math.max(State.NextTowerId, id + 1)

    local cf = modelPivot(model)
    local entry = {
        model = model,
        id = id,
        name = model.Name,
        position = cf and cf.Position or nil,
        cframe = cf,
        level = nil,
    }

    State.RuntimeTowers[id] = entry
    State.ModelToTowerId[model] = id
    return id
end

local function unregisterDeadTowers()
    for id, entry in pairs(State.RuntimeTowers) do
        if not entry.model or not entry.model.Parent then
            State.RuntimeTowers[id] = nil
        end
    end
end

local function findTowerById(id)
    id = tonumber(id)
    local entry = State.RuntimeTowers[id]
    if entry and entry.model and entry.model.Parent then
        return entry.model
    end
    return nil
end

local function findNearestTower(pos, maxDistance)
    local best, bestDist
    maxDistance = maxDistance or math.huge

    unregisterDeadTowers()

    for id, entry in pairs(State.RuntimeTowers) do
        local model = entry.model
        local cf = modelPivot(model)
        if cf then
            local d = distanceTo(cf.Position, pos)
            if d <= maxDistance and (not bestDist or d < bestDist) then
                best = model
                bestDist = d
            end
        end
    end

    return best, bestDist
end

local function scanNewModels(origin, known)
    local candidates = {}
    for _, obj in ipairs(Workspace:GetDescendants()) do
        if obj:IsA("Model") and not known[obj] and obj.Parent then
            local cf = modelPivot(obj)
            if cf and distanceTo(cf.Position, origin) <= Settings.PlacementVerifyDistance then
                local score = 0
                if looksLikeTower(obj) then score = score + 100 end
                score = score - distanceTo(cf.Position, origin)
                table.insert(candidates, {model = obj, score = score, cf = cf})
            end
        end
    end

    table.sort(candidates, function(a, b)
        return a.score > b.score
    end)

    return candidates
end

local function snapshotModels()
    local map = {}
    for _, obj in ipairs(Workspace:GetDescendants()) do
        if obj:IsA("Model") then
            map[obj] = true
        end
    end
    return map
end

----------------------------------------------------------------
-- MOUSE / WORLD TARGET
----------------------------------------------------------------
local function getMouseScreenPosition()
    local p = UserInputService:GetMouseLocation()
    return p.X, p.Y
end

local function worldFromScreen(x, y)
    local cam = getCamera()
    if not cam then return nil end

    local ray = cam:ViewportPointToRay(x, y)
    local params = RaycastParams.new()
    params.FilterType = Enum.RaycastFilterType.Exclude
    params.FilterDescendantsInstances = {LocalPlayer.Character}

    local hit = Workspace:Raycast(ray.Origin, ray.Direction * 2000, params)
    if hit then
        return hit.Position, hit.Instance
    end
    return nil, nil
end

local function screenFromWorld(position)
    local cam = getCamera()
    if not cam or not position then return nil, nil, false end
    local point, visible = cam:WorldToViewportPoint(position)
    return point.X, point.Y, visible and point.Z > 0
end

local function findTowerUnderMouse()
    local x, y = getMouseScreenPosition()
    local _, hitInstance = worldFromScreen(x, y)
    if not hitInstance then return nil end

    local cursor = hitInstance
    while cursor and cursor ~= Workspace do
        if cursor:IsA("Model") then
            local id = State.ModelToTowerId[cursor]
            if id then return cursor, id end

            local attrId = cursor:GetAttribute("MacroTowerId")
            if attrId and State.RuntimeTowers[attrId] then
                return cursor, attrId
            end
        end
        cursor = cursor.Parent
    end

    local hitPos = hitInstance.Position
    local nearest = findNearestTower(hitPos, 8)
    if nearest then
        return nearest, State.ModelToTowerId[nearest]
    end

    return nil
end

----------------------------------------------------------------
-- INPUT SIMULATION
----------------------------------------------------------------
local function clickGuiButton(button)
    if not button or not button:IsA("GuiButton") then return false end

    local activated = pcall(function()
        button:Activate()
    end)
    if activated then
        return true
    end

    local abs = button.AbsolutePosition
    local size = button.AbsoluteSize
    local x = abs.X + size.X / 2
    local y = abs.Y + size.Y / 2

    if Caps.Input then
        pcall(function()
            VirtualInputManager:SendMouseButtonEvent(x, y, 0, true, game, 0)
            VirtualInputManager:SendMouseButtonEvent(x, y, 0, false, game, 0)
        end)
        return true
    end

    return false
end

local function sendKey(keyCode)
    local ok = false

    if type(keypress) == "function" and type(keyrelease) == "function" then
        local vk = keyCode.Value
        pcall(function()
            keypress(vk)
            task.wait(0.03)
            keyrelease(vk)
        end)
        ok = true
    elseif Caps.Input then
        ok = pcall(function()
            VirtualInputManager:SendKeyEvent(true, keyCode, false, game)
            VirtualInputManager:SendKeyEvent(false, keyCode, false, game)
        end)
    end

    return ok
end

local function clickWorld(position)
    local x, y, visible = screenFromWorld(position)
    if not visible then return false end

    if Caps.Input then
        local ok = pcall(function()
            VirtualInputManager:SendMouseButtonEvent(x, y, 0, true, game, 0)
            task.wait(0.03)
            VirtualInputManager:SendMouseButtonEvent(x, y, 0, false, game, 0)
        end)
        return ok
    end

    return false
end

----------------------------------------------------------------
-- UI SCANNING
----------------------------------------------------------------
local function iterGuiRoots()
    local roots = {}
    local pg = LocalPlayer:FindFirstChildOfClass("PlayerGui")
    if pg then table.insert(roots, pg) end
    pcall(function() table.insert(roots, CoreGui) end)
    return roots
end

local function cleanText(text)
    return tostring(text or ""):lower():gsub("[%c]", " "):gsub("%s+", " "):gsub("^%s+", ""):gsub("%s+$", "")
end

local function buttonText(button)
    if not button then return "" end
    local pieces = {}

    pcall(function()
        if button:IsA("TextButton") or button:IsA("TextLabel") or button:IsA("TextBox") then
            table.insert(pieces, button.Text)
        end
    end)

    for _, child in ipairs(button:GetDescendants()) do
        if child:IsA("TextLabel") or child:IsA("TextButton") then
            table.insert(pieces, child.Text)
        end
    end

    return cleanText(table.concat(pieces, " "))
end

local function findGuiButtonByText(patterns)
    local pats = type(patterns) == "table" and patterns or {patterns}

    for _, root in ipairs(iterGuiRoots()) do
        for _, obj in ipairs(root:GetDescendants()) do
            if obj:IsA("GuiButton") and obj.Visible then
                local text = buttonText(obj)
                for _, pattern in ipairs(pats) do
                    if text:find(cleanText(pattern), 1, true) then
                        return obj, text
                    end
                end
            end
        end
    end

    return nil
end

local function waitForButton(patterns, timeout)
    local started = now()
    while now() - started < (timeout or 15) do
        local button = findGuiButtonByText(patterns)
        if button then return button end
        task.wait(0.15)
    end
    return nil
end

local function clickButtonText(patterns, timeout)
    local button = waitForButton(patterns, timeout)
    if not button then
        fail("Could not find button: " .. table.concat(type(patterns) == "table" and patterns or {patterns}, ", "))
        return false
    end
    return clickGuiButton(button)
end

----------------------------------------------------------------
-- GENERIC UI STATE DETECTION
----------------------------------------------------------------
local function findTextObject(patterns)
    local pats = type(patterns) == "table" and patterns or {patterns}

    for _, root in ipairs(iterGuiRoots()) do
        for _, obj in ipairs(root:GetDescendants()) do
            if obj.Visible and (obj:IsA("TextLabel") or obj:IsA("TextButton")) then
                local text = cleanText(obj.Text)
                for _, p in ipairs(pats) do
                    if text:find(cleanText(p), 1, true) then
                        return obj, text
                    end
                end
            end
        end
    end
    return nil
end

local function getDisplayedNumberByPatterns(patterns)
    local obj = findTextObject(patterns)
    if not obj then return nil end
    local text = cleanText(obj.Text):gsub(",", "")
    local num = text:match("(%-?%d+%.?%d*)")
    return num and tonumber(num) or nil
end

local function getCash()
    local patterns = {
        "$",
        "cash",
        "money",
        "credits",
        "coins",
    }

    for _, root in ipairs(iterGuiRoots()) do
        for _, obj in ipairs(root:GetDescendants()) do
            if obj.Visible and (obj:IsA("TextLabel") or obj:IsA("TextButton")) then
                local text = cleanText(obj.Text)
                if #text > 0 then
                    for _, p in ipairs(patterns) do
                        if text:find(p, 1, true) then
                            local clean = text:gsub(",", "")
                            local n = clean:match("(%d+%.?%d*)")
                            if n then
                                return tonumber(n)
                            end
                        end
                    end
                end
            end
        end
    end

    local attrContainers = {
        LocalPlayer,
        LocalPlayer:FindFirstChild("leaderstats"),
    }

    for _, container in ipairs(attrContainers) do
        if container then
            for _, child in ipairs(container:GetDescendants()) do
                if child:IsA("IntValue") or child:IsA("NumberValue") then
                    local n = child.Name:lower()
                    if n:find("cash") or n:find("money") or n:find("credit") or n:find("coin") then
                        return child.Value
                    end
                end
            end
        end
    end

    return nil
end

local function getWave()
    local patterns = {
        "wave",
        "round",
    }

    for _, root in ipairs(iterGuiRoots()) do
        for _, obj in ipairs(root:GetDescendants()) do
            if obj.Visible and (obj:IsA("TextLabel") or obj:IsA("TextButton")) then
                local text = cleanText(obj.Text)
                for _, p in ipairs(patterns) do
                    if text:find(p, 1, true) then
                        local n = text:match("(%d+)")
                        if n then return tonumber(n) end
                    end
                end
            end
        end
    end

    return nil
end

local function isDefeatVisible()
    local again = findGuiButtonByText({"Again"})
    local defeat = findTextObject({"defeat", "you lost", "loss", "failed"})
    return again ~= nil or defeat ~= nil
end

local function isVictoryVisible()
    return findGuiButtonByText({"Back to Lobby", "Continue", "Victory", "Won"}) ~= nil
end

local function isReadyVisible()
    return findGuiButtonByText({"Ready"}) ~= nil
end

local function isActiveMatch()
    -- Defeat/victory screens are terminal states, not active waves.
    if isDefeatVisible() or isVictoryVisible() then return false end

    local wave = getWave()
    if wave and wave >= 1 then
        return true
    end

    -- Prefer an enemy container with actual children over merely finding a Map.
    -- A lobby can still contain map-like folders, so Map alone is not enough.
    for _, containerName in ipairs({"Enemies", "Enemy", "Mobs", "Units"}) do
        local container = Workspace:FindFirstChild(containerName, true)
        if container then
            local count = 0
            for _, obj in ipairs(container:GetDescendants()) do
                if obj:IsA("Model") or obj:IsA("Humanoid") then
                    count = count + 1
                    if count >= 1 then
                        return true
                    end
                end
            end
        end
    end

    return false
end

----------------------------------------------------------------
-- GAME SPEED
----------------------------------------------------------------
local function setGameSpeed(speed)
    speed = tonumber(speed) or 1
    local targetTexts = {"x" .. tostring(speed), tostring(speed) .. "x"}

    local button = findGuiButtonByText(targetTexts)
    if button then
        local ok = clickGuiButton(button)
        if ok then
            log("Game speed -> x" .. tostring(speed))
            return true
        end
    end

    -- Some interfaces put speed into a text control without a button.
    for _, root in ipairs(iterGuiRoots()) do
        for _, obj in ipairs(root:GetDescendants()) do
            if obj.Visible and obj:IsA("TextButton") then
                local t = cleanText(obj.Text)
                if t:find("speed", 1, true) then
                    pcall(function() obj:Activate() end)
                    task.wait(0.1)
                    local nextButton = findGuiButtonByText(targetTexts)
                    if nextButton then
                        local ok = clickGuiButton(nextButton)
                        if ok then return true end
                    end
                end
            end
        end
    end

    return false
end

----------------------------------------------------------------
-- REMOTE CAPTURE
----------------------------------------------------------------
local function describeRemote(instance)
    if not instance or typeof(instance) ~= "Instance" then
        return nil
    end

    return {
        path = relativePath(instance),
        name = instance.Name,
        className = instance.ClassName,
    }
end

local function currentTowerResolver(instance)
    local id = State.ModelToTowerId[instance]
    if id then return id end

    -- If an argument points to a descendant inside a known tower model,
    -- map it back to the tower.
    local cursor = instance
    while cursor and cursor ~= Workspace do
        if cursor:IsA("Model") and State.ModelToTowerId[cursor] then
            return State.ModelToTowerId[cursor]
        end
        cursor = cursor.Parent
    end

    return nil
end

local function captureRemote(instance, method, args)
    if State.Mode ~= "RECORD" then return end
    if type(checkcaller) == "function" and checkcaller() then return end

    State.RemoteSeq = State.RemoteSeq + 1

    local serializedArgs = {}
    for i, arg in ipairs(args) do
        serializedArgs[i] = serialize(arg, currentTowerResolver)
    end

    State.LastRemote = {
        seq = State.RemoteSeq,
        at = now(),
        remote = describeRemote(instance),
        method = method,
        args = serializedArgs,
    }

    -- Create a rolling raw event only when it looks like a genuine user action.
    if State.PendingInput and (now() - State.PendingInput.at) <= Settings.RemoteCaptureWindow then
        State.PendingInput.lastRemoteSeq = State.RemoteSeq
    end
end

if Caps.Hook and not genv.__SkibiMacroHookInstalled then
    genv.__SkibiMacroHookInstalled = true

    local oldNamecall
    oldNamecall = hookmetamethod(game, "__namecall", newcclosure(function(self, ...)
        local method = getnamecallmethod()

        if not (checkcaller and checkcaller()) then
            if (self:IsA("RemoteEvent") and method == "FireServer")
            or (self:IsA("UnreliableRemoteEvent") and method == "FireServer")
            or (self:IsA("RemoteFunction") and method == "InvokeServer") then
                local args = {...}
                pcall(function()
                    captureRemote(self, method, args)
                end)
            end
        end

        return oldNamecall(self, ...)
    end))
end

----------------------------------------------------------------
-- REMOTE REPLAY
----------------------------------------------------------------
local function resolveRemote(info)
    if not info then return nil end

    local remote = findByFullName(info.path)
    if remote then return remote end

    -- Fallback recursive name search.
    local candidates = {}
    for _, container in ipairs({ReplicatedStorage, Workspace, LocalPlayer}) do
        for _, obj in ipairs(container:GetDescendants()) do
            if obj.Name == info.name
                and (obj:IsA("RemoteEvent") or obj:IsA("UnreliableRemoteEvent") or obj:IsA("RemoteFunction")) then
                table.insert(candidates, obj)
            end
        end
    end

    if #candidates == 1 then
        return candidates[1]
    end

    return candidates[1]
end

local function replayRemote(remoteInfo, method, serializedArgs)
    local remote = resolveRemote(remoteInfo)
    if not remote then
        fail("Remote not found: " .. tostring(remoteInfo and remoteInfo.name))
        return false
    end

    local args = {}
    for i, item in ipairs(serializedArgs or {}) do
        args[i] = deserialize(item, findTowerById)
    end

    local ok, result = pcall(function()
        if method == "FireServer" then
            remote:FireServer(table.unpack(args))
            return true
        elseif method == "InvokeServer" then
            return remote:InvokeServer(table.unpack(args))
        end
        error("Unsupported method " .. tostring(method))
    end)

    if not ok then
        fail("Remote replay failed: " .. tostring(result))
        return false
    end

    return true, result
end

----------------------------------------------------------------
-- EVENT RECORDING
----------------------------------------------------------------
local function recordEvent(eventType, payload, forcedTime)
    if State.Mode ~= "RECORD" then return nil end

    local elapsed = forcedTime or (now() - State.RecordStart)
    local event = {
        t = round(elapsed, 3),
        type = eventType,
        data = payload or {},
    }

    table.insert(State.Macro.events, event)
    State.EventIndex = #State.Macro.events
    State.MacroDirty = true
    State.AutoSaveCounter = State.AutoSaveCounter + 1
    State.LastAction = eventType

    if Settings.AutoSave and State.AutoSaveCounter >= Settings.AutoSaveEvents then
        State.AutoSaveCounter = 0
        saveRecovery()
        if State.Macro.name ~= "NewMacro" then
            saveMacro(State.Macro.name, true)
        end
    end

    return event
end

local function rememberTowerTemplate(id, template)
    State.Macro.towerTemplates[tostring(id)] = template
    State.MacroDirty = true
end

----------------------------------------------------------------
-- RAW EVENT CLASSIFICATION
----------------------------------------------------------------
local function shouldRecordRaw()
    local current = math.floor(now())
    if current ~= State.RawEventSecond then
        State.RawEventSecond = current
        State.RawEventBudget = 0
    end

    if State.RawEventBudget >= Settings.MaxRawEventsPerSecond then
        return false
    end

    State.RawEventBudget = State.RawEventBudget + 1
    return true
end

local function recordRawRemoteIfNeeded(label)
    if State.Mode ~= "RECORD" then return end
    if not State.LastRemote then return end
    if now() - State.LastRemote.at > Settings.RemoteCaptureWindow then return end
    if not shouldRecordRaw() then return end

    local ev = recordEvent("REMOTE_ACTION", {
        label = label or "Raw",
        remote = State.LastRemote.remote,
        method = State.LastRemote.method,
        args = State.LastRemote.args,
    })

    return ev
end

----------------------------------------------------------------
-- PLAYER WAYPOINTS
----------------------------------------------------------------
local function savePlayerPosition(name, addToMacro)
    local pos = getPlayerPosition()
    local cf = getPlayerCFrame()
    if not pos or not cf then
        fail("Player position unavailable.")
        return nil
    end

    name = safeName(name or ("Position_" .. tostring(#State.Macro.waypoints + 1)))

    local wp = {
        name = name,
        x = pos.X,
        y = pos.Y,
        z = pos.Z,
        cframe = {cf:GetComponents()},
        radius = Settings.MoveRadius,
        createdAt = wallClock(),
    }

    State.Waypoints[name] = wp
    State.Macro.waypoints[name] = wp
    State.MacroDirty = true

    if addToMacro then
        recordEvent("WAYPOINT_SAVE", {
            name = name,
            position = {
                x = pos.X,
                y = pos.Y,
                z = pos.Z,
            },
            radius = wp.radius,
        })
    end

    notify("Waypoint Saved", string.format("%s\nX %.2f | Y %.2f | Z %.2f", name, pos.X, pos.Y, pos.Z), 3)
    log("Waypoint saved: " .. name)
    return wp
end

local function getWaypoint(name)
    name = safeName(name)
    return State.Waypoints[name] or State.Macro.waypoints[name]
end

----------------------------------------------------------------
-- MOVEMENT
----------------------------------------------------------------
local function isAtPosition(pos, radius)
    local current = getPlayerPosition()
    if not current then return false end
    return distanceTo(current, pos) <= (radius or Settings.MoveRadius)
end

local function directMoveTo(position, radius, timeout)
    local alive, hum = isAlive()
    if not alive or not hum then
        return false, "player not alive"
    end

    local started = now()
    local lastProgressAt = started
    local lastPos = hum.RootPart and hum.RootPart.Position or position

    hum:MoveTo(position)

    while now() - started < (timeout or Settings.MoveTimeout) do
        if State.Mode == "STOPPING" or State.StopToken > 0 and State.Mode == "IDLE" then
            return false, "stopped"
        end

        if isAtPosition(position, radius) then
            return true
        end

        local current = getPlayerPosition()
        if current and lastPos then
            if (current - lastPos).Magnitude > 0.2 then
                lastProgressAt = now()
                lastPos = current
            elseif now() - lastProgressAt > 2 then
                pcall(function() hum.Jump = true end)
                hum:MoveTo(position)
                lastProgressAt = now()
            end
        end

        task.wait(0.1)
    end

    return isAtPosition(position, radius), "move timeout"
end

local function pathMoveTo(position, radius, timeout)
    if not Settings.MoveRepath then
        return directMoveTo(position, radius, timeout)
    end

    local root = getRoot()
    if not root then return false, "no root" end

    local okPath, path = pcall(function()
        local p = PathfindingService:CreatePath({
            AgentRadius = 2,
            AgentHeight = 5,
            AgentCanJump = true,
            WaypointSpacing = 4,
        })
        p:ComputeAsync(root.Position, position)
        return p
    end)

    if not okPath or not path or path.Status ~= Enum.PathStatus.Success then
        return directMoveTo(position, radius, timeout)
    end

    local waypoints = path:GetWaypoints()
    local started = now()

    for _, waypoint in ipairs(waypoints) do
        if now() - started > (timeout or Settings.MoveTimeout) then
            return false, "path timeout"
        end

        if State.Mode == "STOPPING" then
            return false, "stopped"
        end

        if waypoint.Action == Enum.PathWaypointAction.Jump then
            pcall(function()
                local _, hum = isAlive()
                if hum then hum.Jump = true end
            end)
        end

        local ok = directMoveTo(waypoint.Position, radius, math.min(8, timeout or 25))
        if not ok then
            return false, "waypoint failed"
        end
    end

    return isAtPosition(position, radius)
end

local function moveToWaypoint(name)
    local wp = getWaypoint(name)
    if not wp then
        return false, "waypoint not found: " .. tostring(name)
    end

    local pos = Vector3.new(wp.x, wp.y, wp.z)
    State.LastAction = "MOVE → " .. name
    return pathMoveTo(pos, tonumber(wp.radius) or Settings.MoveRadius, Settings.MoveTimeout)
end

----------------------------------------------------------------
-- TOWER PLACEMENT
----------------------------------------------------------------
local function getTowerNameCandidateNear(origin, snapshot)
    local candidates = scanNewModels(origin, snapshot)
    if #candidates == 0 then
        return nil
    end
    return candidates[1].model
end

local function capturePlacement(origin)
    if State.Mode ~= "RECORD" then return end

    local snapshot = snapshotModels()
    State.PendingPlacement = {
        at = now(),
        origin = origin,
        snapshot = snapshot,
    }

    task.delay(0.25, function()
        if State.Mode ~= "RECORD" then return end
        if not State.PendingPlacement then return end

        local pending = State.PendingPlacement
        if now() - pending.at > 1.5 then
            State.PendingPlacement = nil
            return
        end

        local model = getTowerNameCandidateNear(pending.origin, pending.snapshot)
        if not model then
            return
        end

        local cf = modelPivot(model)
        if not cf then
            State.PendingPlacement = nil
            return
        end

        if not looksLikeTower(model) and distanceTo(cf.Position, pending.origin) > 4 then
            return
        end

        local id = assignTowerId(model)
        local remote = State.LastRemote
        local remotePayload = nil

        if remote and now() - remote.at <= Settings.RemoteCaptureWindow then
            remotePayload = {
                remote = remote.remote,
                method = remote.method,
                args = remote.args,
            }
        end

        local entry = {
            id = id,
            name = model.Name,
            position = {
                x = cf.Position.X,
                y = cf.Position.Y,
                z = cf.Position.Z,
            },
            cframe = {cf:GetComponents()},
            rotation = {cf:ToOrientation()},
            remote = remotePayload,
            retry = Settings.PlacementRetry,
            verifyDistance = Settings.PlacementVerifyDistance,
        }

        rememberTowerTemplate(id, {
            id = id,
            name = entry.name,
            position = entry.position,
            cframe = entry.cframe,
            remote = remotePayload,
        })

        recordEvent("PLACE_TOWER", entry)

        pcall(function()
            model:SetAttribute("MacroTowerId", id)
        end)

        log("Recorded tower #" .. id .. " " .. entry.name)
        notify("Tower Recorded", "#" .. id .. " " .. entry.name, 2)

        State.PendingPlacement = nil
    end)
end

local function findTowerSlotButton(name)
    local target = cleanText(name)

    for _, root in ipairs(iterGuiRoots()) do
        for _, obj in ipairs(root:GetDescendants()) do
            if obj:IsA("GuiButton") and obj.Visible then
                local text = buttonText(obj)
                if text == target or text:find(target, 1, true) then
                    return obj
                end
            end
        end
    end

    return nil
end

local function selectTowerByName(name)
    local button = findTowerSlotButton(name)
    if button then
        return clickGuiButton(button)
    end

    -- Numeric hotkey fallback if the template recorded a slot field.
    return false
end

local function waitForPlacedTower(position, expectedName, timeout)
    local started = now()

    while now() - started < (timeout or 3) do
        local best
        local bestD = math.huge

        for _, obj in ipairs(Workspace:GetDescendants()) do
            if obj:IsA("Model") and obj.Parent then
                local cf = modelPivot(obj)
                if cf then
                    local d = distanceTo(cf.Position, position)
                    if d < bestD and d <= Settings.PlacementVerifyDistance + 2 then
                        if expectedName == nil or cleanText(obj.Name):find(cleanText(expectedName), 1, true) then
                            best = obj
                            bestD = d
                        end
                    end
                end
            end
        end

        if best then
            return best
        end

        task.wait(0.1)
    end

    return nil
end

local function executePlacement(data)
    local pos = Vector3.new(data.position.x, data.position.y, data.position.z)
    local attempts = tonumber(data.retry) or Settings.PlacementRetry

    for attempt = 1, attempts do
        if State.Mode == "STOPPING" then return false end

        local remoteSuccess = false

        if data.remote and data.remote.remote then
            remoteSuccess = replayRemote(
                data.remote.remote,
                data.remote.method,
                data.remote.args
            )
        end

        if not remoteSuccess then
            -- Fallback: select by visible tower name + click world position.
            selectTowerByName(data.name)
            task.wait(0.05)
            remoteSuccess = clickWorld(pos)
        end

        if remoteSuccess then
            local placed = waitForPlacedTower(pos, data.name, 2.5)
            if placed then
                local id = tonumber(data.id)
                assignTowerId(placed, id)
                pcall(function()
                    placed:SetAttribute("MacroTowerId", id)
                end)
                log("Placed #" .. tostring(id) .. " " .. tostring(data.name))
                return true
            end
        end

        task.wait(Settings.PlacementRetryDelay)
    end

    fail("Placement failed: #" .. tostring(data.id) .. " " .. tostring(data.name))
    return false
end

----------------------------------------------------------------
-- STAT SCANNER FOR AUTO-UPGRADE
----------------------------------------------------------------
local NUMERIC_NAMES = {
    damage = {"damage", "dmg", "atk", "attackdamage"},
    cooldown = {"cooldown", "cd", "attackcooldown", "reload", "interval"},
    attackSpeed = {"attackspeed", "speed", "firerate"},
    cost = {"upgradecost", "cost", "price"},
    level = {"level", "lvl"},
    range = {"range"},
    damageBoost = {"damageboost", "dmgboost", "damagebuff", "dmgbuff"},
    speedBoost = {"speedboost", "attackspeedboost", "speedbuff"},
    cooldownMultiplier = {"cooldownmultiplier", "cdmultiplier"},
}

local function normalizedName(s)
    return tostring(s or ""):lower():gsub("[%s_%-%./]", "")
end

local function matchesAlias(name, aliases)
    local n = normalizedName(name)
    for _, alias in ipairs(aliases) do
        local a = normalizedName(alias)
        if n == a or n:find(a, 1, true) then
            return true
        end
    end
    return false
end

local function readNumberField(container, aliases)
    if not container then return nil end

    local attrs = container:GetAttributes()
    for name, value in pairs(attrs) do
        if type(value) == "number" and matchesAlias(name, aliases) then
            return value
        end
    end

    local direct = {}
    for _, obj in ipairs(container:GetDescendants()) do
        if obj:IsA("IntValue") or obj:IsA("NumberValue") then
            if matchesAlias(obj.Name, aliases) then
                table.insert(direct, obj.Value)
            end
        end
    end

    if #direct > 0 then
        return direct[1]
    end

    return nil
end

local function calculateTowerStats(model)
    if not model or not model.Parent then return nil end

    local damage = readNumberField(model, NUMERIC_NAMES.damage)
    local cooldown = readNumberField(model, NUMERIC_NAMES.cooldown)
    local attackSpeed = readNumberField(model, NUMERIC_NAMES.attackSpeed)
    local cost = readNumberField(model, NUMERIC_NAMES.cost)
    local level = readNumberField(model, NUMERIC_NAMES.level)
    local range = readNumberField(model, NUMERIC_NAMES.range)

    if (not cooldown or cooldown <= 0) and attackSpeed and attackSpeed > 0 then
        cooldown = 1 / attackSpeed
    end

    if not damage or not cooldown or cooldown <= 0 then
        return {
            damage = damage,
            cooldown = cooldown,
            dps = nil,
            cost = cost,
            level = level,
            range = range,
        }
    end

    local baseDps = damage / cooldown

    local damageBoost = 0
    local speedBoost = 0
    local cooldownMultiplier = 1

    for _, tower in pairs(State.RuntimeTowers) do
        local other = tower.model
        if other and other.Parent and other ~= model then
            local db = readNumberField(other, NUMERIC_NAMES.damageBoost)
            local sb = readNumberField(other, NUMERIC_NAMES.speedBoost)
            local cm = readNumberField(other, NUMERIC_NAMES.cooldownMultiplier)

            if db then damageBoost = damageBoost + db end
            if sb then speedBoost = speedBoost + sb end
            if cm and cm > 0 then cooldownMultiplier = cooldownMultiplier * cm end
        end
    end

    local effectiveDamage = damage * (1 + damageBoost)
    local effectiveCooldown = cooldown / math.max(1, 1 + speedBoost) * cooldownMultiplier
    local effectiveDps = effectiveDamage / math.max(0.01, effectiveCooldown)

    return {
        damage = damage,
        cooldown = cooldown,
        dps = baseDps,
        effectiveDamage = effectiveDamage,
        effectiveCooldown = effectiveCooldown,
        effectiveDps = effectiveDps,
        cost = cost,
        level = level,
        range = range,
    }
end

local function towerUpgradeScore(model, mode)
    local stats = calculateTowerStats(model)
    if not stats then return -math.huge, nil end

    local id = State.ModelToTowerId[model]
    local template = id and State.Macro.towerTemplates[tostring(id)]
    local learned = nil

    if template and template.upgrades and stats.level ~= nil then
        learned = template.upgrades[tostring(stats.level)]
    end

    local dps = stats.effectiveDps or stats.dps or 0
    local damage = stats.effectiveDamage or stats.damage or 0

    -- Prefer a learned next-level gain when Record has observed one.
    local predictedDpsGain = learned and tonumber(learned.dpsGain) or nil
    local predictedDamageGain = learned and tonumber(learned.damageGain) or nil
    local predictedCost = learned and tonumber(learned.cost) or tonumber(stats.cost)

    if mode == "Damage" then
        return damage + (predictedDamageGain or 0), stats
    elseif mode == "DPS" then
        return dps + (predictedDpsGain or 0), stats
    elseif mode == "DPS / Cost" then
        if predictedDpsGain and predictedCost and predictedCost > 0 then
            return predictedDpsGain / predictedCost, stats
        end
        local cost = math.max(1, predictedCost or 1)
        return dps / cost, stats
    elseif mode == "Lowest Level First" then
        return -(stats.level or 0), stats
    end

    return dps / math.max(1, predictedCost or 1), stats
end

local function getLearnedUpgradeData(id, level)
    local template = State.Macro.towerTemplates[tostring(id)]
    if not template or not template.upgrades then return nil end
    return template.upgrades[tostring(level)]
end

local function chooseAutoUpgradeTower()
    local best, bestScore, bestStats, bestId
    for id, entry in pairs(State.RuntimeTowers) do
        local model = entry.model
        if model and model.Parent then
            local score, stats = towerUpgradeScore(model, Settings.UpgradeMode)
            if score > (bestScore or -math.huge) then
                best = model
                bestScore = score
                bestStats = stats
                bestId = id
            end
        end
    end
    return best, bestId, bestScore, bestStats
end

local function executeUpgrade(id)
    local model = findTowerById(id)
    if not model then
        return false
    end

    local before = calculateTowerStats(model)
    local template = State.Macro.towerTemplates[tostring(id)]

    if template then
        local upgradeData = nil
        if template.upgrades and before and before.level ~= nil then
            upgradeData = template.upgrades[tostring(before.level)]
        end
        upgradeData = upgradeData or template.upgradeRemote

        if upgradeData and upgradeData.remote then
            local ok = replayRemote(
                upgradeData.remote,
                upgradeData.method,
                upgradeData.args
            )
            if ok then return true end
        elseif upgradeData and upgradeData.method and upgradeData.args then
            local ok = replayRemote(
                upgradeData,
                upgradeData.method,
                upgradeData.args
            )
            if ok then return true end
        end
    end

    -- Generic fallback:
    -- select tower and use the game's documented E key upgrade binding.
    local cf = modelPivot(model)
    if cf then
        clickWorld(cf.Position)
        task.wait(0.05)
        return sendKey(Enum.KeyCode.E)
    end

    return false
end

local function autoUpgradeTick()
    if not Settings.AutoUpgrade then return end
    if State.Mode ~= "PLAY" then return end
    if isDefeatVisible() then return end

    local cash = getCash()
    if cash == nil then return end

    local reserve = tonumber(Settings.CashReserve) or 0
    if cash <= reserve then return end

    local tower, id = chooseAutoUpgradeTower()
    if not tower or not id then return end

    local stats = calculateTowerStats(tower)
    if not stats then return end

    local learned = getLearnedUpgradeData(id, stats.level)
    local cost = learned and tonumber(learned.cost) or tonumber(stats.cost)

    if cost and cash - cost < reserve then
        return
    end

    if executeUpgrade(id) then
        State.LastAction = "AUTO UPGRADE #" .. tostring(id)
        log("Auto-upgrade selected #" .. tostring(id) ..
            " | level=" .. tostring(stats.level or "?") ..
            " | DPS=" .. tostring(round(stats.effectiveDps or stats.dps or 0, 2)) ..
            " | cost=" .. tostring(cost or "?"))
        task.wait(Settings.UpgradeInterval)
    end
end

----------------------------------------------------------------
-- INPUT RECORDING
----------------------------------------------------------------
UserInputService.InputBegan:Connect(function(input, gameProcessed)
    if gameProcessed then return end

    State.LastInputAt = now()

    -- Record world click for placement / generic actions.
    if input.UserInputType == Enum.UserInputType.MouseButton1 then
        local x, y = getMouseScreenPosition()
        local pos = worldFromScreen(x, y)

        if State.Mode == "RECORD" then
            -- If the click is on a visible speed button, record a semantic
            -- TIME_SPEED event as well as the underlying remote if one exists.
            local speedButton
            pcall(function()
                local guiObjects = GuiService:GetGuiObjectsAtPosition(x, y)
                for _, gui in ipairs(guiObjects) do
                    if gui:IsA("GuiButton") then
                        local t = cleanText(buttonText(gui))
                        local n = t:match("x(%d+%.?%d*)") or t:match("(%d+%.?%d*)x")
                        if n then
                            speedButton = tonumber(n)
                            break
                        end
                    end
                end
            end)

            if speedButton then
                recordEvent("TIME_SPEED", {speed = speedButton})
            elseif pos then
                capturePlacement(pos)
            end

            State.PendingInput = {
                at = now(),
                kind = speedButton and "SPEED" or "CLICK",
                position = pos,
            }
        end

        return
    end

    if State.Mode ~= "RECORD" then return end

    if input.KeyCode == Enum.KeyCode.E then
        local tower, id = findTowerUnderMouse()
        local beforeStats = tower and calculateTowerStats(tower) or nil
        local cashBefore = getCash()

        State.PendingUpgrade = {
            at = now(),
            tower = tower,
            id = id,
            beforeStats = beforeStats,
            cashBefore = cashBefore,
        }

        -- Give the game enough time to apply the upgrade locally, then learn
        -- the upgrade's cost and stat gain from the actual game state.
        task.delay(0.45, function()
            if State.Mode ~= "RECORD" then return end
            local pending = State.PendingUpgrade
            if not pending or now() - pending.at > 2 then return end

            local remote = State.LastRemote
            if remote and now() - remote.at <= 2 then
                local model = pending.tower
                local afterStats = model and calculateTowerStats(model) or nil
                local cashAfter = getCash()

                local cost
                if pending.cashBefore and cashAfter then
                    local delta = pending.cashBefore - cashAfter
                    if delta > 0 then
                        cost = delta
                    end
                end

                local level = afterStats and afterStats.level or nil
                local fromLevel = pending.beforeStats and pending.beforeStats.level or nil

                local dpsGain
                local damageGain
                if pending.beforeStats and afterStats then
                    if pending.beforeStats.effectiveDps and afterStats.effectiveDps then
                        dpsGain = afterStats.effectiveDps - pending.beforeStats.effectiveDps
                    elseif pending.beforeStats.dps and afterStats.dps then
                        dpsGain = afterStats.dps - pending.beforeStats.dps
                    end

                    if pending.beforeStats.effectiveDamage and afterStats.effectiveDamage then
                        damageGain = afterStats.effectiveDamage - pending.beforeStats.effectiveDamage
                    elseif pending.beforeStats.damage and afterStats.damage then
                        damageGain = afterStats.damage - pending.beforeStats.damage
                    end
                end

                local remoteData = {
                    remote = remote.remote,
                    method = remote.method,
                    args = remote.args,
                }

                local data = {
                    id = pending.id,
                    level = level,
                    fromLevel = fromLevel,
                    cost = cost,
                    dpsGain = dpsGain,
                    damageGain = damageGain,
                    remote = remoteData,
                }

                local template = State.Macro.towerTemplates[tostring(pending.id)]
                if template then
                    template.upgradeRemote = remoteData
                    template.upgrades = template.upgrades or {}

                    local key = tostring(fromLevel or level or "unknown")
                    template.upgrades[key] = {
                        remote = remoteData,
                        toLevel = level,
                        cost = cost,
                        dpsGain = dpsGain,
                        damageGain = damageGain,
                    }
                end

                recordEvent("UPGRADE_TOWER", data)
                log("Recorded upgrade for tower #" .. tostring(pending.id) ..
                    " | cost=" .. tostring(cost or "?") ..
                    " | DPS gain=" .. tostring(round(dpsGain or 0, 2)))
                State.PendingUpgrade = nil
            end
        end)

    elseif input.KeyCode == Enum.KeyCode.Q
        task.delay(0.15, function()
            recordRawRemoteIfNeeded("Target Mode")
        end)

    elseif input.KeyCode == Enum.KeyCode.R
        task.delay(0.15, function()
            recordRawRemoteIfNeeded("Rotate")
        end)

    elseif input.KeyCode == Enum.KeyCode.X
        task.delay(0.15, function()
            recordRawRemoteIfNeeded("Sell")
        end)

    elseif input.KeyCode == Enum.KeyCode.Z
        task.delay(0.15, function()
            recordRawRemoteIfNeeded("Pause / Unpause")
        end)

    else
        -- Any other input that leads to a remote call shortly afterwards
        -- becomes a generic gameplay event. This covers abilities and speed
        -- controls without pretending we know their private remote names.
        task.delay(0.12, function()
            recordRawRemoteIfNeeded("Input " .. tostring(input.KeyCode))
        end)
    end
end)

----------------------------------------------------------------
-- RECORD CONTROL
----------------------------------------------------------------
local function startRecording()
    if State.Mode == "PLAY" or State.Mode == "PAUSED_PLAY" or State.Mode == "RECOVERY" then
        fail("Cannot Record while Play/Recovery is active.")
        return false
    end

    if State.Mode == "RECORD" then return true end

    State.StopToken = 0
    State.Mode = "RECORD"
    State.RecordStart = now()
    State.EventIndex = #State.Macro.events
    State.PendingPlacement = nil
    State.PendingUpgrade = nil
    State.LastRemote = nil
    State.LastAction = "RECORDING"

    notify("Recorder", "Recording started", 2)
    log("Recording started.")
    saveRecovery()

    return true
end

local function pauseRecording()
    if State.Mode ~= "RECORD" then return false end
    State.Mode = "PAUSED_RECORD"
    State.LastAction = "PAUSED RECORD"
    saveRecovery()
    log("Recording paused.")
    return true
end

local function resumeRecording()
    if State.Mode ~= "PAUSED_RECORD" then return false end

    -- Preserve elapsed macro time excluding the pause duration.
    State.RecordStart = now() - (State.Macro.events[#State.Macro.events] and State.Macro.events[#State.Macro.events].t or 0)
    State.Mode = "RECORD"
    State.LastAction = "RECORDING"
    log("Recording resumed.")
    return true
end

local function stopEverything()
    State.StopToken = State.StopToken + 1
    State.Mode = "STOPPING"
    State.RunningTask = nil
    State.PendingPlacement = nil
    State.PendingUpgrade = nil
    State.Recovering = false
    State.LastAction = "STOPPING"

    task.wait()

    State.Mode = "IDLE"
    State.LastAction = "Idle"
    log("Stopped.")
end

local function startPlay(fromBeginning)
    if State.Mode == "RECORD" or State.Mode == "PAUSED_RECORD" then
        fail("Stop recording before Play.")
        return false
    end

    if not State.Macro or #State.Macro.events == 0 then
        fail("Macro contains no events.")
        return false
    end

    State.StopToken = 0
    State.Mode = "PLAY"
    State.PlayStart = now()

    if fromBeginning ~= false then
        State.PlayIndex = 1
        State.RuntimeTowers = {}
        State.ModelToTowerId = {}
        State.NextTowerId = 1
    end

    State.LastAction = "PLAYING"
    notify("Macro", "Playback started: " .. State.Macro.name, 2)
    log("Playback started from event #" .. tostring(State.PlayIndex))

    return true
end

local function pausePlay()
    if State.Mode ~= "PLAY" then return false end
    State.Mode = "PAUSED_PLAY"
    State.LastAction = "PAUSED PLAY"
    log("Playback paused.")
    return true
end

local function resumePlay()
    if State.Mode ~= "PAUSED_PLAY" then return false end
    State.Mode = "PLAY"
    State.LastAction = "PLAYING"
    log("Playback resumed.")
    return true
end

----------------------------------------------------------------
-- CONDITIONS / EVENT EXECUTOR
----------------------------------------------------------------
local function waitUntil(condition, timeout)
    local started = now()
    State.CurrentCondition = tostring(condition.kind or "Unknown")

    while now() - started < (timeout or 60) do
        if State.Mode == "STOPPING" then
            State.CurrentCondition = "Stopped"
            return false
        end

        if condition.kind == "CASH" then
            local cash = getCash()
            if cash and cash >= (condition.value or 0) then
                State.CurrentCondition = "Met"
                return true
            end

        elseif condition.kind == "WAVE" then
            local wave = getWave()
            if wave and wave >= (condition.value or 0) then
                State.CurrentCondition = "Met"
                return true
            end

        elseif condition.kind == "TOWER_EXISTS" then
            local towerName = cleanText(condition.name)
            for _, entry in pairs(State.RuntimeTowers) do
                if entry.model and entry.model.Parent and cleanText(entry.name):find(towerName, 1, true) then
                    State.CurrentCondition = "Met"
                    return true
                end
            end

        elseif condition.kind == "MATCH_ACTIVE" then
            if isActiveMatch() then
                State.CurrentCondition = "Met"
                return true
            end

        elseif condition.kind == "ABILITY_READY" then
            -- Best-effort generic readiness check:
            -- look for an on-screen ability button without "cooldown".
            local ready = false
            for _, root in ipairs(iterGuiRoots()) do
                for _, obj in ipairs(root:GetDescendants()) do
                    if obj:IsA("GuiButton") and obj.Visible then
                        local text = cleanText(buttonText(obj))
                        if text:find(condition.name and cleanText(condition.name) or "ability", 1, true)
                            and not text:find("cooldown", 1, true) then
                            ready = true
                            break
                        end
                    end
                end
                if ready then break end
            end

            if ready then
                State.CurrentCondition = "Met"
                return true
            end
        end

        task.wait(0.1)
    end

    State.CurrentCondition = "Timeout"
    return false
end

local function executeEvent(event)
    local kind = event.type
    local data = event.data or {}

    State.LastAction = kind

    if kind == "WAYPOINT_SAVE" then
        -- Saving is already done during record; during playback this is a no-op.
        return true

    elseif kind == "MOVE_TO" then
        if data.waypoint then
            local ok, err = moveToWaypoint(data.waypoint)
            if not ok then fail("MOVE_TO " .. tostring(err)) end
            return ok
        end

        if data.position then
            local pos = Vector3.new(data.position.x, data.position.y, data.position.z)
            local ok, err = pathMoveTo(pos, data.radius or Settings.MoveRadius, Settings.MoveTimeout)
            if not ok then fail("MOVE_TO " .. tostring(err)) end
            return ok
        end

        return false

    elseif kind == "PLACE_TOWER" then
        return executePlacement(data)

    elseif kind == "UPGRADE_TOWER" then
        local id = tonumber(data.id)
        if not id then return false end

        local template = State.Macro.towerTemplates[tostring(id)]
        if template and not template.upgradeRemote and data.remote then
            template.upgradeRemote = data.remote
        end

        local ok = executeUpgrade(id)

        if not ok then
            fail("Upgrade failed: tower #" .. tostring(id))
        end

        return ok

    elseif kind == "WAIT" then
        task.wait(tonumber(data.duration) or 0)
        return true

    elseif kind == "WAIT_CASH" then
        return waitUntil({kind = "CASH", value = tonumber(data.value) or 0}, tonumber(data.timeout) or 120)

    elseif kind == "WAIT_WAVE" then
        return waitUntil({kind = "WAVE", value = tonumber(data.value) or 1}, tonumber(data.timeout) or 300)

    elseif kind == "WAIT_MATCH" then
        return waitUntil({kind = "MATCH_ACTIVE"}, tonumber(data.timeout) or 120)

    elseif kind == "TIME_SPEED" then
        return setGameSpeed(tonumber(data.speed) or 1)

    elseif kind == "REMOTE_ACTION" then
        return replayRemote(data.remote, data.method, data.args)

    elseif kind == "ABILITY" then
        if data.remote then
            return replayRemote(data.remote.remote, data.remote.method, data.remote.args)
        end
        if data.key then
            return sendKey(Enum.KeyCode[data.key] or Enum.KeyCode.F)
        end
        return false

    elseif kind == "TARGET_MODE" or kind == "ROTATE" or kind == "SELL" then
        if data.remote then
            return replayRemote(data.remote.remote, data.remote.method, data.remote.args)
        end
        return true
    end

    return true
end

----------------------------------------------------------------
-- RECOVERY
----------------------------------------------------------------
local function recoverActiveMatch()
    if not Settings.RecoveryEnabled then return false end

    -- A defeat screen is explicitly recoverable even though it is not an
    -- "active match" according to isActiveMatch().
    local onDefeat = isDefeatVisible()
    local onVictory = isVictoryVisible()

    if not onDefeat and not onVictory and not isActiveMatch() then
        return false
    end

    State.Mode = "RECOVERY"
    State.Recovering = true
    State.RecoveryStarted = now()
    State.LastAction = "RECOVERY: ACTIVE MATCH"
    notify("Recovery", "Đã vào giữa trận → tăng tốc và chờ thua.", 3)
    log("Recovery: active match detected.")

    setGameSpeed(Settings.RecoverySpeed)

    while now() - State.RecoveryStarted < Settings.RecoveryTimeout do
        if State.Mode == "STOPPING" then
            return false
        end

        if isDefeatVisible() then
            break
        end

        if isVictoryVisible() then
            break
        end

        task.wait(0.5)
    end

    if now() - State.RecoveryStarted >= Settings.RecoveryTimeout then
        fail("Recovery timeout.")
        State.Mode = "IDLE"
        State.Recovering = false
        return false
    end

    if isDefeatVisible() then
        State.LastAction = "RECOVERY: DEFEAT → AGAIN"
        log("Recovery: defeat detected.")

        local again = waitForButton({"Again"}, 10)
        if again then
            clickGuiButton(again)
        else
            fail("Recovery could not find Again.")
            State.Mode = "IDLE"
            State.Recovering = false
            return false
        end

        local ready = waitForButton({"Ready"}, 15)
        if ready then
            task.wait(0.25)
            clickGuiButton(ready)
            log("Recovery: Ready clicked.")
        else
            fail("Recovery could not find Ready.")
            State.Mode = "IDLE"
            State.Recovering = false
            return false
        end

        -- Wait until the new match actually starts.
        local matchWaitStarted = now()
        while now() - matchWaitStarted < 30 do
            if isActiveMatch() then
                break
            end
            task.wait(0.25)
        end

        State.Recovering = false

        if isActiveMatch() then
            log("Recovery complete.")
            if Settings.AutoRestart then
                State.Mode = "PLAY"
                State.PlayIndex = 1
                State.PlayStart = now()
                State.LastAction = "PLAY: RESTARTED"
                return true
            end
        end
    elseif isVictoryVisible() then
        -- A victory screen is not a failed run. Return to lobby/ready path
        -- only if auto-restart is explicitly enabled.
        State.LastAction = "RECOVERY: VICTORY"
        log("Recovery saw a victory screen.")
        if Settings.AutoRestart then
            local back = waitForButton({"Back to Lobby"}, 10)
            if back then clickGuiButton(back) end

            local ready = waitForButton({"Ready"}, 20)
            if ready then
                clickGuiButton(ready)
                task.wait(1)
                State.Recovering = false
                State.Mode = "PLAY"
                State.PlayIndex = 1
                State.PlayStart = now()
                return true
            end
        end
    end

    State.Mode = "IDLE"
    State.Recovering = false
    return false
end

----------------------------------------------------------------
-- MACRO PLAY LOOP
----------------------------------------------------------------
task.spawn(function()
    while true do
        task.wait(0.05)

        if State.Mode == "PLAY" then
            if isDefeatVisible() then
                recoverActiveMatch()
            elseif isVictoryVisible() then
                recoverActiveMatch()
            elseif State.PlayIndex > #State.Macro.events then
                if Settings.AutoRestart then
                    State.LastAction = "MACRO COMPLETE"
                    log("Macro complete.")
                    task.wait(1)

                    local again = findGuiButtonByText({"Again", "Ready"})
                    if again then
                        clickGuiButton(again)
                        task.wait(1)
                    end

                    local ready = waitForButton({"Ready"}, 20)
                    if ready then
                        clickGuiButton(ready)
                        task.wait(1)
                        State.PlayIndex = 1
                        State.PlayStart = now()
                        State.LastAction = "PLAY: LOOP"
                    else
                        State.Mode = "IDLE"
                    end
                else
                    State.Mode = "IDLE"
                end
            else
                local event = State.Macro.events[State.PlayIndex]
                local elapsed = now() - State.PlayStart
                local delay = math.max(0, (tonumber(event.t) or 0) - elapsed)

                if delay > 0 then
                    task.wait(math.min(delay, 0.2))
                else
                    local token = State.StopToken
                    local ok = pcall(function()
                        executeEvent(event)
                    end)

                    if not ok then
                        fail("Unhandled event error at #" .. tostring(State.PlayIndex))
                    end

                    if token == State.StopToken and State.Mode == "PLAY" then
                        State.PlayIndex = State.PlayIndex + 1
                    end
                end
            end

            -- Auto-upgrade runs independently from timeline events.
            pcall(autoUpgradeTick)
        elseif State.Mode == "PAUSED_PLAY" or State.Mode == "IDLE" or State.Mode == "RECORD" or State.Mode == "PAUSED_RECORD" then
            -- nothing
        end
    end
end)

----------------------------------------------------------------
-- MONITOR LOOP
----------------------------------------------------------------
task.spawn(function()
    local lastAFK = now()
    while true do
        task.wait(0.5)

        unregisterDeadTowers()

        if Settings.AntiAFK
            and (State.Mode == "IDLE" or State.Mode == "PAUSED_PLAY" or State.Mode == "RECOVERY")
            and now() - lastAFK >= Settings.AntiAFKInterval then

            local _, hum = isAlive()
            if hum then
                pcall(function() hum.Jump = true end)
                lastAFK = now()
                log("Anti-AFK jump.")
            end
        end

        -- Detect a macro that was started while already inside a match.
        if State.Mode == "IDLE" and Settings.RecoveryEnabled then
            if isActiveMatch() and not isDefeatVisible() and not isVictoryVisible() then
                -- Deliberately do not auto-recover merely from being idle.
                -- Recovery is triggered by PLAY so the script doesn't hijack
                -- a normal manual match.
            end
        end
    end
end)

----------------------------------------------------------------
-- STARTUP BEHAVIOR
----------------------------------------------------------------
local function -- Recovery is intentionally not auto-triggered on script load. PLAY invokes it when needed.
    if not Settings.RecoveryEnabled then return end
    if not State.Macro or #State.Macro.events == 0 then return end

    if isDefeatVisible() then
        task.spawn(function()
            recoverActiveMatch()
        end)
        return
    end

    if isActiveMatch() then
        -- Do not start macro in the middle of a match.
        task.spawn(function()
            recoverActiveMatch()
        end)
    end
end

----------------------------------------------------------------
-- RAYFIELD UI LOADER
----------------------------------------------------------------
local function loadRayfield()
    local urls = {
        -- First try the user's chosen collection.
        "https://raw.githubusercontent.com/ro0ti/Roblox-Scripting-UI/main/Rayfield%20Lib/source.lua",
        "https://raw.githubusercontent.com/ro0ti/Roblox-Scripting-UI/main/Rayfield%20Lib/main.lua",

        -- Fallback to the official Rayfield source if the collection's
        -- file name changes.
        "https://sirius.menu/rayfield",
    }

    local lastError = nil
    for _, url in ipairs(urls) do
        local ok, result = pcall(function()
            return loadstring(game:HttpGet(url))()
        end)

        if ok and result then
            Caps.Rayfield = true
            return result
        end

        lastError = result
    end

    error("Could not load Rayfield: " .. tostring(lastError))
end

local Rayfield = loadRayfield()

_G.__SkibiMacroNotify = function(title, content, duration)
    pcall(function()
        Rayfield:Notify({
            Title = tostring(title),
            Content = tostring(content),
            Duration = duration or 3,
        })
    end)
end

----------------------------------------------------------------
-- UI
----------------------------------------------------------------
local Window = Rayfield:CreateWindow({
    Name = "Skibi Macro Engine",
    Icon = 0,
    LoadingTitle = "Skibi Macro Engine",
    LoadingSubtitle = "Recorder • Recovery • Auto Upgrade",
    Theme = "Default",
    DisableRayfieldPrompts = false,
    DisableBuildWarnings = false,

    ConfigurationSaving = {
        Enabled = true,
        FolderName = "SkibiMacroUI",
        FileName = "settings",
    }
})

local HomeTab = Window:CreateTab("Home", 4483362458)
local RecorderTab = Window:CreateTab("Recorder", 4483362458)
local MacroTab = Window:CreateTab("Macros", 4483362458)
local TimelineTab = Window:CreateTab("Timeline", 4483362458)
local AutoTab = Window:CreateTab("Auto Farm", 4483362458)
local MonitorTab = Window:CreateTab("Monitor", 4483362458)
local SettingsTab = Window:CreateTab("Settings", 4483362458)

----------------------------------------------------------------
-- UI HELPERS
----------------------------------------------------------------
local function uiUpdate()
    -- Intentionally lightweight. Rayfield updates the visible values through
    -- recreated paragraphs rather than hammering a callback every frame.
end

local function refreshMacroParagraph()
    if not MacroTab then return end
    -- function kept for compatibility with older Rayfield builds
end

----------------------------------------------------------------
-- HOME
----------------------------------------------------------------
HomeTab:CreateSection("Macro Control")

HomeTab:CreateButton({
    Name = "RECORD",
    Callback = function()
        if State.Mode == "PAUSED_RECORD" then
            resumeRecording()
        else
            startRecording()
        end
    end,
})

HomeTab:CreateButton({
    Name = "PAUSE",
    Callback = function()
        if State.Mode == "RECORD" then
            pauseRecording()
        elseif State.Mode == "PLAY" then
            pausePlay()
        end
    end,
})

HomeTab:CreateButton({
    Name = "PLAY",
    Callback = function()
        if State.Mode == "PAUSED_PLAY" then
            resumePlay()
        else
            -- Correct behavior requested by the design:
            -- if already in a running match, recover first instead of trying
            -- to inject half a macro into a live wave.
            if Settings.RecoveryEnabled and isActiveMatch() and not isDefeatVisible() and not isVictoryVisible() then
                task.spawn(function()
                    local recovered = recoverActiveMatch()
                    if recovered then
                        State.PlayIndex = 1
                        State.PlayStart = now()
                    end
                end)
            else
                startPlay(true)
            end
        end
    end,
})

HomeTab:CreateButton({
    Name = "STOP",
    Callback = function()
        stopEverything()
    end,
})

HomeTab:CreateParagraph({
    Title = "Status",
    Content = "Mode: IDLE\nMacro: " .. State.Macro.name,
})

----------------------------------------------------------------
-- RECORDER
----------------------------------------------------------------
RecorderTab:CreateSection("Player Waypoints")

local PositionName = "FarmSpot"

RecorderTab:CreateInput({
    Name = "Waypoint Name",
    CurrentValue = PositionName,
    PlaceholderText = "FarmSpot",
    RemoveTextAfterFocusLost = false,
    Flag = "WaypointName",
    Callback = function(value)
        PositionName = safeName(value)
    end,
})

RecorderTab:CreateButton({
    Name = "SAVE PLAYER POSITION",
    Callback = function()
        savePlayerPosition(PositionName, State.Mode == "RECORD")
    end,
})

RecorderTab:CreateButton({
    Name = "ADD MOVE TO CURRENT POSITION",
    Callback = function()
        local pos = getPlayerPosition()
        if not pos then return end

        local name = PositionName
        if not getWaypoint(name) then
            savePlayerPosition(name, false)
        end

        if State.Mode == "RECORD" then
            recordEvent("MOVE_TO", {
                waypoint = name,
            })
        else
            fail("ADD MOVE requires RECORD mode.")
        end
    end,
})

RecorderTab:CreateButton({
    Name = "SAVE TIMELINE TO DISK",
    Callback = function()
        saveMacro(State.Macro.name)
    end,
})

RecorderTab:CreateSection("Recorder Info")

RecorderTab:CreateParagraph({
    Title = "Semantic recording",
    Content = "Tower placement is recorded as Name + XYZ + CFrame + Tower ID + captured remote. E upgrades are tracked separately. Other user actions that trigger a remote become REMOTE_ACTION events.",
})

----------------------------------------------------------------
-- MACRO MANAGER
----------------------------------------------------------------
MacroTab:CreateSection("Current Macro")

local MacroNameInput = State.Macro.name

MacroTab:CreateInput({
    Name = "Macro Name",
    CurrentValue = State.Macro.name,
    PlaceholderText = "Chapter9_NM",
    RemoveTextAfterFocusLost = false,
    Flag = "MacroName",
    Callback = function(value)
        MacroNameInput = safeName(value)
    end,
})

MacroTab:CreateButton({
    Name = "NEW MACRO",
    Callback = function()
        if State.Mode == "RECORD" or State.Mode == "PLAY" then
            fail("Stop current operation before creating a new macro.")
            return
        end

        State.Macro = newMacro(MacroNameInput ~= "" and MacroNameInput or "NewMacro")
        State.MacroName = State.Macro.name
        State.MacroDirty = false
        State.PlayIndex = 1
        State.EventIndex = 0
        State.RuntimeTowers = {}
        State.ModelToTowerId = {}
        State.NextTowerId = 1

        notify("Macro", "Created " .. State.Macro.name, 2)
    end,
})

MacroTab:CreateButton({
    Name = "SAVE",
    Callback = function()
        saveMacro(MacroNameInput ~= "" and MacroNameInput or State.Macro.name)
    end,
})

MacroTab:CreateButton({
    Name = "SAVE AS",
    Callback = function()
        local target = safeName(MacroNameInput)
        if target == "" then target = "Macro_Copy" end
        State.Macro.name = target
        saveMacro(target)
    end,
})

local macroDropdown
local function refreshMacroDropdown()
    if not macroDropdown then return end
    pcall(function()
        macroDropdown:Refresh(listMacros())
    end)
end

macroDropdown = MacroTab:CreateDropdown({
    Name = "Load Macro",
    Options = listMacros(),
    CurrentOption = State.Macro.name,
    MultipleOptions = false,
    Flag = "LoadMacro",
    Callback = function(option)
        local name
        if type(option) == "table" then
            name = option[1]
        else
            name = option
        end
        State.SelectedMacro = name
    end,
})

MacroTab:CreateButton({
    Name = "LOAD SELECTED",
    Callback = function()
        local name = State.SelectedMacro or MacroNameInput or State.Macro.name
        if loadMacro(name) then
            MacroNameInput = State.Macro.name
            refreshMacroDropdown()
        end
    end,
})

MacroTab:CreateButton({
    Name = "DELETE SELECTED",
    Callback = function()
        local name = State.SelectedMacro or MacroNameInput
        if name and name ~= "" then
            deleteMacro(name)
            refreshMacroDropdown()
        end
    end,
})

MacroTab:CreateButton({
    Name = "DUPLICATE SELECTED",
    Callback = function()
        local source = State.SelectedMacro or State.Macro.name
        local target = safeName(MacroNameInput .. "_copy")
        duplicateMacro(source, target)
        refreshMacroDropdown()
    end,
})

MacroTab:CreateButton({
    Name = "LOAD RECOVERED RECORD",
    Callback = function()
        local payload = readJSON(RECOVER_FILE)
        if payload and payload.macro then
            State.Macro = sanitizeMacro(payload.macro)
            State.MacroName = State.Macro.name
            State.MacroDirty = true
            State.PlayIndex = 1
            notify("Recovered", State.Macro.name .. " restored", 3)
        else
            fail("No recovery file.")
        end
    end,
})

----------------------------------------------------------------
-- TIMELINE
----------------------------------------------------------------
TimelineTab:CreateSection("Timeline")

local TimelineParagraph = TimelineTab:CreateParagraph({
    Title = "Events",
    Content = "No events yet.",
})

local function updateTimeline()
    local events = State.Macro and State.Macro.events or {}
    local lines = {}

    local startIdx = math.max(1, #events - 27)
    for i = startIdx, #events do
        local e = events[i]
        local suffix = ""

        if e.type == "PLACE_TOWER" then
            suffix = string.format(" #%s %s", tostring(e.data.id), tostring(e.data.name))
        elseif e.type == "UPGRADE_TOWER" then
            suffix = string.format(" #%s", tostring(e.data.id))
        elseif e.type == "MOVE_TO" then
            suffix = " → " .. tostring(e.data.waypoint or "XYZ")
        elseif e.type == "TIME_SPEED" then
            suffix = " x" .. tostring(e.data.speed)
        elseif e.type == "REMOTE_ACTION" then
            suffix = " [" .. tostring(e.data.label or "Raw") .. "]"
        end

        table.insert(lines,
            string.format("#%d  %s  %s%s",
                i,
                fmtTime(e.t),
                tostring(e.type),
                suffix
            )
        )
    end

    if #lines == 0 then
        table.insert(lines, "No events yet.")
    end

    pcall(function()
        TimelineParagraph:Set({
            Title = "Events (" .. tostring(#events) .. ")",
            Content = table.concat(lines, "\n"),
        })
    end)
end

TimelineTab:CreateButton({
    Name = "REFRESH TIMELINE",
    Callback = updateTimeline,
})

TimelineTab:CreateButton({
    Name = "REMOVE LAST EVENT",
    Callback = function()
        if State.Mode == "RECORD" then
            fail("Pause/stop recording before editing the timeline.")
            return
        end

        local n = #State.Macro.events
        if n > 0 then
            table.remove(State.Macro.events, n)
            State.EventIndex = #State.Macro.events
            State.MacroDirty = true
            updateTimeline()
        end
    end,
})

TimelineTab:CreateButton({
    Name = "CLEAR TIMELINE",
    Callback = function()
        if State.Mode == "RECORD" or State.Mode == "PLAY" then
            fail("Stop Record/Play before clearing.")
            return
        end

        State.Macro.events = {}
        State.EventIndex = 0
        State.PlayIndex = 1
        State.MacroDirty = true
        updateTimeline()
    end,
})

----------------------------------------------------------------
-- AUTO FARM
----------------------------------------------------------------
AutoTab:CreateSection("Auto Upgrade")

AutoTab:CreateToggle({
    Name = "Auto Upgrade",
    CurrentValue = Settings.AutoUpgrade,
    Flag = "AutoUpgrade",
    Callback = function(value)
        Settings.AutoUpgrade = value
        saveSettings()
    end,
})

AutoTab:CreateDropdown({
    Name = "Upgrade Mode",
    Options = {"Damage", "DPS", "DPS / Cost", "Lowest Level First"},
    CurrentOption = Settings.UpgradeMode,
    Flag = "UpgradeMode",
    Callback = function(value)
        local v = value
        if type(value) == "table" then v = value[1] end
        Settings.UpgradeMode = tostring(v)
        saveSettings()
    end,
})

AutoTab:CreateSlider({
    Name = "Cash Reserve",
    Range = {0, 100000},
    Increment = 100,
    Suffix = "$",
    CurrentValue = Settings.CashReserve,
    Flag = "CashReserve",
    Callback = function(value)
        Settings.CashReserve = tonumber(value) or 0
        saveSettings()
    end,
})

AutoTab:CreateSlider({
    Name = "Upgrade Check Interval",
    Range = {0.25, 5},
    Increment = 0.25,
    Suffix = "s",
    CurrentValue = Settings.UpgradeInterval,
    Flag = "UpgradeInterval",
    Callback = function(value)
        Settings.UpgradeInterval = tonumber(value) or 0.75
        saveSettings()
    end,
})

AutoTab:CreateParagraph({
    Title = "Stat Engine",
    Content = "Reads exposed Damage / Cooldown / AttackSpeed / Cost / Level / Range fields and sums exposed damage/speed boosts. When the game hides stats, the engine falls back to runtime DPS heuristics and the recorded E-upgrade route.",
})

----------------------------------------------------------------
-- MONITOR
----------------------------------------------------------------
MonitorTab:CreateSection("Live Monitor")

local MonitorParagraph = MonitorTab:CreateParagraph({
    Title = "Monitor",
    Content = "Loading...",
})

local ErrorParagraph = MonitorTab:CreateParagraph({
    Title = "Errors",
    Content = "None",
})

local function updateMonitor()
    local cash = getCash()
    local wave = getWave()

    local towerCount = 0
    for _, entry in pairs(State.RuntimeTowers) do
        if entry.model and entry.model.Parent then
            towerCount = towerCount + 1
        end
    end

    local nextEvent = State.Macro.events[State.PlayIndex]
    local nextText = nextEvent
        and (tostring(nextEvent.type) .. " @" .. fmtTime(nextEvent.t))
        or "None"

    local monitor = string.format(
        "Mode: %s\nMacro: %s\nEvents: %d / %d\nWave: %s\nCash: %s\nTowers: %d\nNext: %s\nCondition: %s\nAction: %s",
        State.Mode,
        tostring(State.Macro.name),
        math.min(State.PlayIndex, #State.Macro.events),
        #State.Macro.events,
        tostring(wave or "--"),
        tostring(cash or "--"),
        towerCount,
        nextText,
        tostring(State.CurrentCondition),
        tostring(State.LastAction)
    )

    pcall(function()
        MonitorParagraph:Set({
            Title = "Monitor",
            Content = monitor,
        })
    end)

    pcall(function()
        ErrorParagraph:Set({
            Title = "Errors (" .. tostring(#State.Errors) .. ")",
            Content = #State.Errors > 0 and table.concat(State.Errors, "\n") or "None",
        })
    end)

    updateTimeline()
end

task.spawn(function()
    while true do
        task.wait(1)
        pcall(updateMonitor)
    end
end)

----------------------------------------------------------------
-- SETTINGS
----------------------------------------------------------------
SettingsTab:CreateSection("Recovery")

SettingsTab:CreateToggle({
    Name = "Recovery Enabled",
    CurrentValue = Settings.RecoveryEnabled,
    Flag = "RecoveryEnabled",
    Callback = function(value)
        Settings.RecoveryEnabled = value
        saveSettings()
    end,
})

SettingsTab:CreateSlider({
    Name = "Recovery Speed",
    Range = {1, 4},
    Increment = 1,
    Suffix = "x",
    CurrentValue = Settings.RecoverySpeed,
    Flag = "RecoverySpeed",
    Callback = function(value)
        Settings.RecoverySpeed = tonumber(value) or 3
        saveSettings()
    end,
})

SettingsTab:CreateSlider({
    Name = "Recovery Timeout",
    Range = {60, 1800},
    Increment = 30,
    Suffix = "s",
    CurrentValue = Settings.RecoveryTimeout,
    Flag = "RecoveryTimeout",
    Callback = function(value)
        Settings.RecoveryTimeout = tonumber(value) or 900
        saveSettings()
    end,
})

SettingsTab:CreateToggle({
    Name = "Auto Restart",
    CurrentValue = Settings.AutoRestart,
    Flag = "AutoRestart",
    Callback = function(value)
        Settings.AutoRestart = value
        saveSettings()
    end,
})

SettingsTab:CreateSection("Movement / Anti-AFK")

SettingsTab:CreateToggle({
    Name = "Anti-AFK Jump",
    CurrentValue = Settings.AntiAFK,
    Flag = "AntiAFK",
    Callback = function(value)
        Settings.AntiAFK = value
        saveSettings()
    end,
})

SettingsTab:CreateSlider({
    Name = "Arrival Radius",
    Range = {0.5, 5},
    Increment = 0.25,
    Suffix = " studs",
    CurrentValue = Settings.MoveRadius,
    Flag = "MoveRadius",
    Callback = function(value)
        Settings.MoveRadius = tonumber(value) or 1.5
        saveSettings()
    end,
})

SettingsTab:CreateSlider({
    Name = "Move Timeout",
    Range = {5, 120},
    Increment = 5,
    Suffix = "s",
    CurrentValue = Settings.MoveTimeout,
    Flag = "MoveTimeout",
    Callback = function(value)
        Settings.MoveTimeout = tonumber(value) or 25
        saveSettings()
    end,
})

SettingsTab:CreateSection("Recording")

SettingsTab:CreateToggle({
    Name = "Auto Save",
    CurrentValue = Settings.AutoSave,
    Flag = "AutoSave",
    Callback = function(value)
        Settings.AutoSave = value
        saveSettings()
    end,
})

SettingsTab:CreateSlider({
    Name = "Auto Save Events",
    Range = {1, 25},
    Increment = 1,
    Suffix = " events",
    CurrentValue = Settings.AutoSaveEvents,
    Flag = "AutoSaveEvents",
    Callback = function(value)
        Settings.AutoSaveEvents = tonumber(value) or 5
        saveSettings()
    end,
})

SettingsTab:CreateToggle({
    Name = "Debug Log",
    CurrentValue = Settings.Debug,
    Flag = "Debug",
    Callback = function(value)
        Settings.Debug = value
        saveSettings()
    end,
})

SettingsTab:CreateParagraph({
    Title = "Compatibility",
    Content =
        "Filesystem: " .. tostring(Caps.File) ..
        "\nRemote hook: " .. tostring(Caps.Hook) ..
        "\nVirtual input: " .. tostring(Caps.Input) ..
        "\nRayfield: " .. tostring(Caps.Rayfield),
})

----------------------------------------------------------------
-- FINAL INITIALIZATION
----------------------------------------------------------------
Rayfield:Notify({
    Title = "Skibi Macro Engine",
    Content =
        "Loaded v" .. SCRIPT_VERSION ..
        "\nRecord semantic placement + upgrade events; Play uses learned remote calls with input fallback.",
    Duration = 6,
})

log("Loaded v" .. SCRIPT_VERSION)
log("Filesystem=" .. tostring(Caps.File) .. " Hook=" .. tostring(Caps.Hook) .. " Input=" .. tostring(Caps.Input))

-- Load the current macro if a file exists and the name matches.
if Caps.File and fileExists(macroPath(State.Macro.name)) then
    pcall(function()
        loadMacro(State.Macro.name)
    end)
end

-- Recover an unfinished record only when explicitly requested from the UI.
-- For PLAY, automatically recover an active match because the user asked for
-- the "go insane, x3, lose, Again -> Ready -> restart" behavior.
-- Recovery is intentionally not auto-triggered on script load. PLAY invokes it when needed.
