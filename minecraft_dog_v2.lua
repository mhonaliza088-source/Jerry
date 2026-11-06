--[[
  MINECRAFT DOG v2  (client-side LocalScript, Delta / mobile friendly)
  - chest w/ 20 bones, tameable dog, Minecraft trees
  - free block building with planks (place anywhere)
  - break any map part into voxels, craft beds (5 voxels) and chests (8 planks)
  - day/night cycle + the "dog steals your bed" night story
  Re-executing cleans up the old version (and restores broken map parts).
]]

local Players = game:GetService("Players")
local RunService = game:GetService("RunService")
local UIS = game:GetService("UserInputService")
local TweenService = game:GetService("TweenService")
local Debris = game:GetService("Debris")
local Lighting = game:GetService("Lighting")
local lp = Players.LocalPlayer

------------------------------------------------------------------ CONFIG
local CONFIG = {
	ChestDistance = 30,
	BonesInChest = 20,
	TameChance = 0.4,
	Reach = 16,
	PlaceReach = 35,
	BreakReach = 26,
	BlockSize = 4,          -- plank block size (studs)
	DogMinRadius = 70,
	DogMaxRadius = 150,
	TreeCount = 45,
	TreeMinRadius = 35,
	TreeMaxRadius = 250,
	TreeHits = 3,
	LogsPerTree = {3, 5},
	PlanksPerLog = 4,
	BedVoxels = 5,          -- voxels (broken map parts) needed for a bed
	ChestPlanks = 8,        -- planks needed for a chest
	TreeRespawn = 30,
	DayLength = 360,        -- seconds for a full 24h day
	StartClock = 8,
	SleepFrom = 17,         -- you can sleep from 17:00 until 06:00
	SleepAnytime = false,   -- true = ignore the night rule (for testing)
	SleepSeconds = 5,
	WakeApproach = 12,      -- how close you must get to the digging dog
}

local C = Color3.fromRGB
local WHITE, BLACK = Color3.new(1, 1, 1), Color3.new(0, 0, 0)
local genv = (getgenv and getgenv()) or _G

------------------------------------------------------------------ CLEANUP
if genv.__MCDogCleanup then pcall(genv.__MCDogCleanup) end

local alive = true
local conns = {}
local brokenParts = {}
local origClock = Lighting.ClockTime
local function connect(sig, fn)
	local c = sig:Connect(fn)
	conns[#conns + 1] = c
	return c
end

local oldWorld = workspace:FindFirstChild("MCDogWorld")
if oldWorld then oldWorld:Destroy() end
local oldGhost = workspace:FindFirstChild("MCDogGhost")
if oldGhost then oldGhost:Destroy() end
local world = Instance.new("Folder")
world.Name = "MCDogWorld"
world.Parent = workspace

local function guiParent()
	local ok, res = pcall(function() return gethui() end)
	if ok and res then return res end
	return lp:WaitForChild("PlayerGui")
end
pcall(function() local a = lp.PlayerGui:FindFirstChild("MCDogGui") if a then a:Destroy() end end)
pcall(function() local a = gethui():FindFirstChild("MCDogGui") if a then a:Destroy() end end)

------------------------------------------------------------------ HELPERS
local function new(class, props, parent)
	local i = Instance.new(class)
	for k, v in pairs(props) do i[k] = v end
	if parent then i.Parent = parent end
	return i
end

local function border(inst, th, col)
	return new("UIStroke", {Thickness = th, Color = col or BLACK, ApplyStrokeMode = Enum.ApplyStrokeMode.Border}, inst)
end

local function mk(parent, name, size, cf, color, mat, collide)
	local p = Instance.new("Part")
	p.Name = name
	p.Size = size
	p.CFrame = cf
	p.Color = color
	p.Material = mat or Enum.Material.SmoothPlastic
	p.Anchored = true
	p.CanCollide = collide and true or false
	p.TopSurface = Enum.SurfaceType.Smooth
	p.BottomSurface = Enum.SurfaceType.Smooth
	p.Parent = parent
	return p
end

local function getHRP()
	local c = lp.Character
	return c and c:FindFirstChild("HumanoidRootPart")
end
local function getCam() return workspace.CurrentCamera end

local function rp(excludeWorld)
	local p = RaycastParams.new()
	p.FilterType = Enum.RaycastFilterType.Exclude
	local list = {}
	if excludeWorld then list[#list + 1] = world end
	for _, pl in ipairs(Players:GetPlayers()) do
		if pl.Character then list[#list + 1] = pl.Character end
	end
	p.FilterDescendantsInstances = list
	return p
end

local function groundAt(x, z, fromY, anySlope)
	local res = workspace:Raycast(Vector3.new(x, fromY, z), Vector3.new(0, -700, 0), rp(true))
	if not res then return nil end
	if res.Instance:IsA("Terrain") and res.Material == Enum.Material.Water then return nil end
	if not res.Instance.CanCollide then return nil end
	if not anySlope and res.Normal.Y < 0.75 then return nil end
	return res.Position
end

local function findSpot(minR, maxR, tries)
	local hrp = getHRP()
	if not hrp then return nil end
	local base = hrp.Position
	for _ = 1, (tries or 40) do
		local a = math.random() * math.pi * 2
		local r = minR + math.random() * (maxR - minR)
		local pos = groundAt(base.X + math.cos(a) * r, base.Z + math.sin(a) * r, base.Y + 150)
		if pos then return pos end
	end
	return nil
end

local function flatDist(a, b)
	return Vector3.new(a.X - b.X, 0, a.Z - b.Z).Magnitude
end

local function posOf(inst)
	if inst:IsA("Model") then return inst.PrimaryPart and inst.PrimaryPart.Position end
	return inst.Position
end

------------------------------------------------------------------ STATE
local inv = {bone = 0, log = 0, plank = 0, voxel = 0, bed = 0, chest = 0}
local ORDER = {"bone", "log", "plank", "voxel", "bed", "chest"}
local NAMES = {bone = "Bone", log = "Oak Log", plank = "Oak Planks", voxel = "Voxel", bed = "Bed", chest = "Chest"}
local PLACEABLE = {plank = true, bed = true, chest = true}
local selected = nil
local breakMode = false

local theDog = nil
local dogByModel, chestByModel = {}, {}
local placedChests = {}
local dogBed = nil
local currentChest = nil
local chestOpen = false
local story = {phase = 0, day = 1, sleeping = false}
local clock = CONFIG.StartClock
local clockPaused = false
local drops = {}

local gui = new("ScreenGui", {
	Name = "MCDogGui", ResetOnSpawn = false, IgnoreGuiInset = true,
	ZIndexBehavior = Enum.ZIndexBehavior.Sibling, DisplayOrder = 50,
}, guiParent())

local ghost = new("Part", {
	Name = "MCDogGhost", Anchored = true, CanCollide = false, CanQuery = false, CanTouch = false,
	Material = Enum.Material.Neon, Transparency = 1, Size = Vector3.new(1, 1, 1), Color = C(60, 255, 100),
}, workspace)

genv.__MCDogCleanup = function()
	alive = false
	for _, c in ipairs(conns) do pcall(function() c:Disconnect() end) end
	for _, r in ipairs(brokenParts) do
		pcall(function()
			r.part.Transparency = r.t
			r.part.CanCollide = r.c
			r.part.CanQuery = r.q
		end)
	end
	pcall(function() Lighting.ClockTime = origClock end)
	pcall(function() ghost:Destroy() end)
	pcall(function() world:Destroy() end)
	pcall(function() gui:Destroy() end)
end

------------------------------------------------------------------ ICONS
local function makeIcon(parent, kind)
	local holder = new("Frame", {
		BackgroundTransparency = 1, AnchorPoint = Vector2.new(.5, .5),
		Position = UDim2.fromScale(.5, .5), Size = UDim2.fromOffset(30, 30),
	}, parent)
	local function box(w, h, x, y, col, parentF, strokeCol)
		local f = new("Frame", {
			BackgroundColor3 = col, BorderSizePixel = 0, AnchorPoint = Vector2.new(.5, .5),
			Position = UDim2.new(.5, x, .5, y), Size = UDim2.fromOffset(w, h),
		}, parentF or holder)
		if strokeCol then border(f, 2, strokeCol) end
		return f
	end
	if kind == "bone" then
		local rot = new("Frame", {
			BackgroundTransparency = 1, AnchorPoint = Vector2.new(.5, .5),
			Position = UDim2.fromScale(.5, .5), Size = UDim2.fromOffset(30, 14), Rotation = -45,
		}, holder)
		local bone = C(236, 236, 224)
		box(22, 6, 0, 0, bone, rot)
		for _, sx in ipairs({-1, 1}) do
			for _, sy in ipairs({-1, 1}) do
				local k = box(8, 8, sx * 11, sy * 3, bone, rot)
				new("UICorner", {CornerRadius = UDim.new(1, 0)}, k)
			end
		end
	elseif kind == "log" then
		local o = box(26, 26, 0, 0, C(104, 82, 50), nil, C(60, 45, 25))
		box(14, 14, 0, 0, C(158, 128, 80), o)
	elseif kind == "plank" then
		local o = box(28, 18, 0, 0, C(181, 143, 87), nil, C(110, 80, 40))
		new("Frame", {BackgroundColor3 = C(130, 98, 55), BorderSizePixel = 0,
			Position = UDim2.fromOffset(0, 8), Size = UDim2.new(1, 0, 0, 2)}, o)
	elseif kind == "voxel" then
		local o = box(22, 22, 0, 0, C(110, 160, 215), nil, C(40, 70, 110))
		box(10, 10, -3, -3, C(160, 205, 240), o)
	elseif kind == "bed" then
		box(28, 6, 0, 7, C(150, 105, 55), nil, C(90, 60, 30))
		box(28, 12, 0, -2, C(245, 245, 245), nil, C(150, 150, 150))
		box(9, 6, -8, -4, C(255, 255, 255), nil, C(180, 180, 180))
	elseif kind == "chest" then
		local o = box(26, 22, 0, 0, C(176, 124, 52), nil, C(52, 36, 20))
		box(26, 3, 0, -3, C(52, 36, 20), o)
		box(4, 7, 0, -3, C(205, 205, 205), o)
	end
	return holder
end

local function renderItem(slot, kind, count)
	local old = slot:FindFirstChild("Item")
	if old then old:Destroy() end
	if not kind or not count or count <= 0 then return end
	local h = new("Frame", {Name = "Item", BackgroundTransparency = 1, Size = UDim2.fromScale(1, 1)}, slot)
	makeIcon(h, kind)
	new("TextLabel", {
		BackgroundTransparency = 1, AnchorPoint = Vector2.new(1, 1),
		Position = UDim2.new(1, -2, 1, -1), Size = UDim2.fromOffset(34, 14),
		Text = tostring(count), TextColor3 = WHITE, TextStrokeTransparency = 0,
		Font = Enum.Font.GothamBold, TextSize = 13, TextXAlignment = Enum.TextXAlignment.Right,
	}, h)
end

------------------------------------------------------------------ HUD
local toastLbl = new("TextLabel", {
	AnchorPoint = Vector2.new(.5, 0), Position = UDim2.new(.5, 0, 0, 40),
	Size = UDim2.fromOffset(420, 28), BackgroundColor3 = BLACK, BackgroundTransparency = 1,
	TextTransparency = 1, Text = "", TextColor3 = WHITE, Font = Enum.Font.GothamBold, TextSize = 14,
}, gui)
new("UICorner", {CornerRadius = UDim.new(0, 8)}, toastLbl)
local toastTok = 0
local function toast(msg, col)
	toastTok = toastTok + 1
	local my = toastTok
	toastLbl.Text = msg
	toastLbl.TextColor3 = col or WHITE
	toastLbl.TextTransparency = 0
	toastLbl.BackgroundTransparency = 0.4
	task.delay(3, function()
		if alive and toastTok == my then
			TweenService:Create(toastLbl, TweenInfo.new(.4), {TextTransparency = 1, BackgroundTransparency = 1}):Play()
		end
	end)
end

local clockLbl = new("TextLabel", {
	AnchorPoint = Vector2.new(.5, 0), Position = UDim2.new(.5, 0, 0, 8), Size = UDim2.fromOffset(170, 24),
	BackgroundColor3 = BLACK, BackgroundTransparency = 0.5, TextColor3 = WHITE,
	Font = Enum.Font.GothamBold, TextSize = 14, Text = "",
}, gui)
new("UICorner", {CornerRadius = UDim.new(0, 8)}, clockLbl)

local cross = new("Frame", {
	Name = "Crosshair", AnchorPoint = Vector2.new(.5, .5), Position = UDim2.fromScale(.5, .5),
	Size = UDim2.fromOffset(26, 26), BackgroundTransparency = 1,
}, gui)
local crossBars = {}
for _, sz in ipairs({Vector2.new(24, 3), Vector2.new(3, 24)}) do
	local f = new("Frame", {
		AnchorPoint = Vector2.new(.5, .5), Position = UDim2.fromScale(.5, .5),
		Size = UDim2.fromOffset(sz.X, sz.Y), BackgroundColor3 = WHITE, BorderSizePixel = 0,
	}, cross)
	border(f, 1, BLACK)
	crossBars[#crossBars + 1] = f
end

local promptLbl = new("TextLabel", {
	AnchorPoint = Vector2.new(.5, 0), Position = UDim2.new(.5, 0, .5, 26),
	Size = UDim2.fromOffset(300, 24), BackgroundTransparency = 1, Text = "",
	TextColor3 = WHITE, TextStrokeTransparency = 0, Font = Enum.Font.GothamBold, TextSize = 15,
}, gui)

local function bigButton(text, pos, size, color)
	local b = new("TextButton", {
		AnchorPoint = Vector2.new(1, .5), Position = pos, Size = UDim2.fromOffset(size, size),
		BackgroundColor3 = color, Text = text, TextColor3 = WHITE, Font = Enum.Font.GothamBlack,
		TextSize = 14, AutoButtonColor = true, BorderSizePixel = 0,
	}, gui)
	new("UICorner", {CornerRadius = UDim.new(1, 0)}, b)
	border(b, 3, BLACK)
	return b
end
local useBtn = bigButton("USE", UDim2.new(1, -18, .45, 0), 84, C(40, 150, 60))
local breakBtn = bigButton("BREAK", UDim2.new(1, -112, .45, 0), 64, C(120, 60, 60))
local craftBtn = bigButton("CRAFT", UDim2.new(1, -25, .45, 100), 70, C(160, 110, 40))

local function setBreak(on)
	breakMode = on
	breakBtn.BackgroundColor3 = on and C(220, 50, 50) or C(120, 60, 60)
	breakBtn.Text = on and "BREAK ON" or "BREAK"
end
connect(breakBtn.Activated, function()
	setBreak(not breakMode)
	if breakMode then selected = nil end
	if _G.__mcRefresh then _G.__mcRefresh() end
end)

-- hotbar
local hud = new("Frame", {
	AnchorPoint = Vector2.new(.5, 1), Position = UDim2.new(.5, 0, 1, -8),
	Size = UDim2.fromOffset(330, 52), BackgroundTransparency = 1,
}, gui)
new("UIListLayout", {
	FillDirection = Enum.FillDirection.Horizontal, HorizontalAlignment = Enum.HorizontalAlignment.Center,
	VerticalAlignment = Enum.VerticalAlignment.Center, Padding = UDim.new(0, 4),
}, hud)
local hudSlots, hudStroke = {}, {}
for _, k in ipairs(ORDER) do
	local s = new("TextButton", {
		Name = k, Size = UDim2.fromOffset(48, 48), BackgroundColor3 = C(60, 60, 60),
		BackgroundTransparency = .2, Text = "", AutoButtonColor = false, BorderSizePixel = 0, Visible = false,
	}, hud)
	hudStroke[k] = border(s, 2, C(20, 20, 20))
	hudSlots[k] = s
end

-- sleep fade
local fade = new("Frame", {
	Size = UDim2.fromScale(1, 1), BackgroundColor3 = BLACK, BackgroundTransparency = 1,
	BorderSizePixel = 0, ZIndex = 100, Active = false,
}, gui)
local fadeTxt = new("TextLabel", {
	AnchorPoint = Vector2.new(.5, .5), Position = UDim2.fromScale(.5, .5), Size = UDim2.fromOffset(300, 40),
	BackgroundTransparency = 1, TextTransparency = 1, Text = "Zzz...", TextColor3 = WHITE,
	Font = Enum.Font.GothamBold, TextSize = 28, ZIndex = 101,
}, gui)

------------------------------------------------------------------ PANELS
local function makeClose(parent, fn)
	local b = new("TextButton", {
		AnchorPoint = Vector2.new(1, 0), Position = UDim2.new(1, -6, 0, 6), Size = UDim2.fromOffset(34, 34),
		BackgroundColor3 = C(190, 40, 40), Text = "X", TextColor3 = WHITE, Font = Enum.Font.GothamBlack,
		TextSize = 18, BorderSizePixel = 0,
	}, parent)
	new("UICorner", {CornerRadius = UDim.new(0, 8)}, b)
	border(b, 2, BLACK)
	connect(b.Activated, fn)
	return b
end

local function panelBase(name, w, h)
	local f = new("Frame", {
		Name = name, AnchorPoint = Vector2.new(.5, .5), Position = UDim2.fromScale(.5, .5),
		Size = UDim2.fromOffset(w, h), BackgroundColor3 = C(198, 198, 198), BorderSizePixel = 0, Visible = false,
	}, gui)
	border(f, 3, C(30, 30, 30))
	return f, new("UIScale", {}, f)
end

local function fit(sc, w, h)
	local vs = getCam().ViewportSize
	sc.Scale = math.max(0.4, math.min(1, (vs.X - 20) / w, (vs.Y - 20) / h))
end

local function label(parent, text, pos, size, ts)
	return new("TextLabel", {
		BackgroundTransparency = 1, Position = pos, Size = size, Text = text,
		TextColor3 = C(64, 64, 64), Font = Enum.Font.GothamBold, TextSize = ts or 15,
		TextXAlignment = Enum.TextXAlignment.Left,
	}, parent)
end

-- chest GUI (9x6 chest + inventory + hotbar)
local chestGui, chestScale = panelBase("Chest", 352, 442)
label(chestGui, "Large Chest", UDim2.fromOffset(14, 8), UDim2.fromOffset(200, 22), 15)
label(chestGui, "Inventory", UDim2.fromOffset(14, 254), UDim2.fromOffset(200, 22), 15)

local function makeSlot(parent, x, y)
	local s = new("TextButton", {
		Position = UDim2.fromOffset(x, y), Size = UDim2.fromOffset(36, 36),
		BackgroundColor3 = C(139, 139, 139), Text = "", AutoButtonColor = false, BorderSizePixel = 0,
	}, parent)
	border(s, 2, C(70, 70, 70))
	return s
end
local chestSlots, invSlots = {}, {}
for i = 1, 54 do
	local col, row = (i - 1) % 9, math.floor((i - 1) / 9)
	chestSlots[i] = makeSlot(chestGui, 14 + col * 36, 34 + row * 36)
end
for i = 1, 27 do
	local col, row = (i - 1) % 9, math.floor((i - 1) / 9)
	invSlots[i] = makeSlot(chestGui, 14 + col * 36, 276 + row * 36)
end
for i = 1, 9 do invSlots[27 + i] = makeSlot(chestGui, 14 + (i - 1) * 36, 392) end

local function refreshAll()
	if selected and inv[selected] <= 0 then selected = nil end
	for _, k in ipairs(ORDER) do
		local s = hudSlots[k]
		s.Visible = inv[k] > 0
		renderItem(s, k, inv[k])
		hudStroke[k].Color = (selected == k) and WHITE or C(20, 20, 20)
		hudStroke[k].Thickness = (selected == k) and 3 or 2
	end
	for _, s in ipairs(invSlots) do renderItem(s) end
	local idx = 1
	for _, k in ipairs(ORDER) do
		if inv[k] > 0 and invSlots[idx] then
			renderItem(invSlots[idx], k, inv[k])
			idx = idx + 1
		end
	end
	local cd = currentChest and currentChest.data or {}
	for i, s in ipairs(chestSlots) do
		local d = cd[i]
		renderItem(s, d and d.kind, d and d.count)
	end
end
_G.__mcRefresh = refreshAll

for _, k in ipairs(ORDER) do
	connect(hudSlots[k].Activated, function()
		if selected == k then selected = nil else selected = k end
		if selected then setBreak(false) end
		refreshAll()
	end)
end

for i, s in ipairs(chestSlots) do
	connect(s.Activated, function()
		local d = currentChest and currentChest.data[i]
		if not d then return end
		inv[d.kind] = inv[d.kind] + d.count
		currentChest.data[i] = nil
		if d.kind == "bone" then selected = "bone"; setBreak(false) end
		toast("+" .. d.count .. " " .. NAMES[d.kind], C(120, 255, 120))
		refreshAll()
	end)
end

-- dog command panel
local dogPanel, dogScale = panelBase("DogPanel", 260, 190)
label(dogPanel, "Dog Commands", UDim2.fromOffset(14, 12), UDim2.fromOffset(180, 24), 17)
local cmds = {{"Follow Me", "follow"}, {"Sit", "sit"}, {"Spin", "spin"}, {"Stay", "stay"}}
local commandDog
for i, c in ipairs(cmds) do
	local col, row = (i - 1) % 2, math.floor((i - 1) / 2)
	local b = new("TextButton", {
		Position = UDim2.fromOffset(12 + col * 124, 52 + row * 64), Size = UDim2.fromOffset(112, 54),
		BackgroundColor3 = C(70, 130, 200), Text = c[1], TextColor3 = WHITE,
		Font = Enum.Font.GothamBold, TextSize = 18, BorderSizePixel = 0,
	}, dogPanel)
	new("UICorner", {CornerRadius = UDim.new(0, 10)}, b)
	border(b, 2, BLACK)
	connect(b.Activated, function()
		if theDog then commandDog(theDog, c[2]) end
	end)
end

-- craft panel
local craftPanel, craftScale = panelBase("CraftPanel", 300, 276)
label(craftPanel, "Crafting", UDim2.fromOffset(14, 12), UDim2.fromOffset(180, 24), 17)
local craftInfo = label(craftPanel, "", UDim2.fromOffset(14, 40), UDim2.fromOffset(270, 20), 13)
local function recipeBtn(text, y, col)
	local b = new("TextButton", {
		Position = UDim2.fromOffset(14, y), Size = UDim2.fromOffset(272, 56), BackgroundColor3 = col,
		Text = text, TextColor3 = WHITE, Font = Enum.Font.GothamBold, TextSize = 16, BorderSizePixel = 0,
	}, craftPanel)
	new("UICorner", {CornerRadius = UDim.new(0, 10)}, b)
	border(b, 2, BLACK)
	return b
end
local planksBtn = recipeBtn("Oak Planks x" .. CONFIG.PlanksPerLog .. "   (1 Log)", 66, C(181, 143, 87))
local bedBtn = recipeBtn("Bed   (" .. CONFIG.BedVoxels .. " Voxels)", 130, C(150, 90, 90))
local chestBtn = recipeBtn("Chest   (" .. CONFIG.ChestPlanks .. " Planks)", 194, C(120, 85, 45))

local function refreshCraft()
	craftInfo.Text = "Logs: " .. inv.log .. "   Planks: " .. inv.plank .. "   Voxels: " .. inv.voxel
end
local function closePanels()
	dogPanel.Visible = false
	craftPanel.Visible = false
end
local closeChest
makeClose(dogPanel, function() dogPanel.Visible = false end)
makeClose(craftPanel, function() craftPanel.Visible = false end)
makeClose(chestGui, function() closeChest() end)

------------------------------------------------------------------ CHESTS
local function setLid(ch, angle)
	ch.angle = angle
	local hinge = Vector3.new(0, 1.7, 1.5)
	for _, e in ipairs(ch.lid) do
		e.part.CFrame = ch.origin * CFrame.new(hinge) * CFrame.Angles(angle, 0, 0) * CFrame.new(-hinge) * e.rel
	end
end

local function animateLid(ch, to)
	ch.tok = (ch.tok or 0) + 1
	local my = ch.tok
	local from = ch.angle
	task.spawn(function()
		local t0 = tick()
		while alive and ch.tok == my do
			local a = math.min((tick() - t0) / 0.35, 1)
			setLid(ch, from + (to - from) * (a * a * (3 - 2 * a)))
			if a >= 1 then break end
			RunService.Heartbeat:Wait()
		end
	end)
end

local function buildChest(origin, labelText)
	local m = Instance.new("Model")
	m.Name = "MCChest"
	m:SetAttribute("Kind", "Chest")
	local WOOD, WOOD2, DARK, IRON = C(176, 124, 52), C(191, 140, 64), C(52, 36, 20), C(205, 205, 205)
	local ch = {model = m, origin = origin, lid = {}, angle = 0, data = {}}
	local function add(name, size, rel, color, mat, isLid)
		local p = mk(m, name, size, origin * rel, color, mat or Enum.Material.WoodPlanks, true)
		if isLid then ch.lid[#ch.lid + 1] = {part = p, rel = rel} end
		return p
	end
	local base = add("Base", Vector3.new(3, 1.7, 3), CFrame.new(0, 0.85, 0), WOOD)
	add("BottomTrim", Vector3.new(3.1, 0.25, 3.1), CFrame.new(0, 0.125, 0), DARK)
	add("BaseTopTrim", Vector3.new(3.1, 0.2, 3.1), CFrame.new(0, 1.6, 0), DARK)
	for _, sx in ipairs({-1, 1}) do
		for _, sz in ipairs({-1, 1}) do
			add("Post", Vector3.new(0.28, 1.7, 0.28), CFrame.new(sx * 1.5, 0.85, sz * 1.5), DARK)
			add("LidPost", Vector3.new(0.28, 1.1, 0.28), CFrame.new(sx * 1.5, 2.25, sz * 1.5), DARK, nil, true)
		end
	end
	add("Lid", Vector3.new(3, 1.1, 3), CFrame.new(0, 2.25, 0), WOOD2, nil, true)
	add("LidTopTrim", Vector3.new(3.1, 0.2, 3.1), CFrame.new(0, 2.75, 0), DARK, nil, true)
	add("Latch", Vector3.new(0.45, 0.9, 0.18), CFrame.new(0, 1.75, -1.55), IRON, Enum.Material.Metal, true)
	m.PrimaryPart = base
	m.Parent = world
	chestByModel[m] = ch
	if labelText then
		local bb = new("BillboardGui", {
			Size = UDim2.fromOffset(120, 26), StudsOffset = Vector3.new(0, 4.5, 0),
			AlwaysOnTop = true, MaxDistance = 300, Adornee = base,
		}, base)
		new("TextLabel", {
			Size = UDim2.fromScale(1, 1), BackgroundTransparency = 1, Text = labelText, TextColor3 = C(255, 220, 90),
			TextStrokeTransparency = 0, Font = Enum.Font.GothamBold, TextScaled = true,
		}, bb)
	end
	return ch
end

local function openChest(ch)
	if chestOpen then return end
	if ch.locked then toast("Something is inside! Careful...", C(255, 170, 60)) return end
	chestOpen = true
	currentChest = ch
	closePanels()
	fit(chestScale, 352, 442)
	refreshAll()
	chestGui.Visible = true
	animateLid(ch, math.rad(100))
end

closeChest = function()
	if not chestOpen then return end
	chestOpen = false
	chestGui.Visible = false
	if currentChest then animateLid(currentChest, 0) end
end

------------------------------------------------------------------ TREES
local function buildTree(pos)
	local m = Instance.new("Model")
	m.Name = "MCTree"
	m:SetAttribute("Kind", "Tree")
	m:SetAttribute("Hits", CONFIG.TreeHits)
	local o = CFrame.new(pos) * CFrame.Angles(0, math.rad(math.random(0, 3) * 90), 0)
	local trunk = mk(m, "Trunk", Vector3.new(2, 12, 2), o * CFrame.new(0, 6, 0), C(104, 82, 50), Enum.Material.Wood, true)
	local function leaf(sx, sy, sz, x, y, z)
		local g = math.random(-8, 8)
		mk(m, "Leaves", Vector3.new(sx, sy, sz), o * CFrame.new(x, y, z), C(40 + g, 108 + g * 2, 30 + g), Enum.Material.Grass, false)
	end
	leaf(14, 3, 14, 0, 7.5, 0)
	leaf(10, 3, 10, 0, 10.5, 0)
	leaf(6, 3, 6, 0, 13.5, 0)
	leaf(2, 2, 2, -1.5, 15.5, 0)
	leaf(2, 2, 2, 1.5, 15.5, 0)
	m.PrimaryPart = trunk
	m.Parent = world
	return m
end

local function spawnTree()
	local pos = findSpot(CONFIG.TreeMinRadius, CONFIG.TreeMaxRadius, 30)
	if pos then buildTree(pos) end
end

local treeCd = {}
local function chopTree(m)
	if treeCd[m] and tick() - treeCd[m] < 0.3 then return end
	treeCd[m] = tick()
	local hits = (m:GetAttribute("Hits") or 1) - 1
	m:SetAttribute("Hits", hits)
	if hits > 0 then
		toast("Chopping... " .. hits .. " more", C(230, 200, 140))
		task.spawn(function()
			local base = m:GetPivot()
			for i = 1, 8 do
				if not m.Parent then return end
				m:PivotTo(base * CFrame.Angles(0, 0, math.rad((i % 2 == 0 and 3 or -3) * (1 - i / 8))))
				task.wait(0.03)
			end
			if m.Parent then m:PivotTo(base) end
		end)
		return
	end
	m:SetAttribute("Kind", nil)
	for _, p in ipairs(m:GetChildren()) do
		if p:IsA("BasePart") then
			p.CanCollide = false
			TweenService:Create(p, TweenInfo.new(0.5), {Transparency = 1, Position = p.Position - Vector3.new(0, 2, 0)}):Play()
		end
	end
	Debris:AddItem(m, 0.7)
	local n = math.random(CONFIG.LogsPerTree[1], CONFIG.LogsPerTree[2])
	inv.log = inv.log + n
	refreshAll()
	toast("+" .. n .. " Oak Log", C(120, 255, 120))
	task.delay(CONFIG.TreeRespawn, function()
		if alive then spawnTree() end
	end)
end

------------------------------------------------------------------ BED + BLOOD
local beds = {}
local bedByModel = {}

local function buildBed(origin)
	local m = Instance.new("Model")
	m.Name = "MCBed"
	m:SetAttribute("Kind", "Bed")
	local WOODC = C(150, 105, 55)
	local function add(name, size, rel, color, mat)
		return mk(m, name, size, origin * rel, color, mat or Enum.Material.WoodPlanks, true)
	end
	for _, sx in ipairs({-1, 1}) do
		for _, sz in ipairs({-1, 1}) do
			add("Leg", Vector3.new(0.5, 1, 0.5), CFrame.new(sx * 1.55, 0.5, sz * 3.15), WOODC, Enum.Material.Wood)
		end
	end
	local frame = add("Frame", Vector3.new(3.7, 0.5, 7.0), CFrame.new(0, 1.25, 0), C(162, 118, 60))
	add("Mattress", Vector3.new(3.5, 0.8, 6.8), CFrame.new(0, 1.9, 0), C(240, 240, 240), Enum.Material.Fabric)
	add("Pillow", Vector3.new(2.9, 0.35, 1.5), CFrame.new(0, 2.475, 2.5), C(252, 252, 252), Enum.Material.Fabric)
	add("Fold", Vector3.new(3.52, 0.82, 0.35), CFrame.new(0, 1.9, 0.5), C(198, 200, 206), Enum.Material.Fabric)
	m.PrimaryPart = frame
	m.Parent = world
	local look = origin.LookVector
	local bed = {
		model = m, origin = origin,
		layPos = (origin * CFrame.new(0, 2.3, -0.4)).Position,
		approach = (origin * CFrame.new(0, 0, -6.5)).Position,
		dogYaw = math.atan2(look.X, look.Z), -- dog faces the pillow end (+Z)
	}
	beds[#beds + 1] = bed
	bedByModel[m] = bed
	return bed
end

local function addBlood(bed)
	local spots = {
		{0, 0, 4.0}, {-0.8, 2.2, 2.4}, {1.0, -2.0, 2.0}, {0.2, -3.5, 1.2},
		{2.3, 0.6, 1.0}, {-2.2, -1.0, 0.9}, {0.4, 3.9, 1.1},
	}
	for i, s in ipairs(spots) do
		local p = mk(bed.model, "Blood", Vector3.new(0.06, s[3], s[3]),
			bed.origin * CFrame.new(s[1], 0.04 + i * 0.004, s[2]) * CFrame.Angles(0, 0, math.pi / 2),
			C(125 + i * 3, 0, 0), Enum.Material.SmoothPlastic, false)
		p.Shape = Enum.PartType.Cylinder
		p.CanQuery = false
	end
end

------------------------------------------------------------------ DOG
local GROUP_PIVOT = {
	Head = Vector3.new(0, 0.3, -0.95), Tail = Vector3.new(0, 0.3, 0.9),
	FL = Vector3.new(-0.4, -0.5, -0.65), FR = Vector3.new(0.4, -0.5, -0.65),
	BL = Vector3.new(-0.4, -0.5, 0.65), BR = Vector3.new(0.4, -0.5, 0.65),
}
local FUR, FUR2, LEG = C(205, 205, 205), C(225, 225, 225), C(188, 188, 188)
local DOG_PARTS = {
	{"Body", Vector3.new(1.2, 1.2, 1.8), CFrame.new(0, 0, 0), FUR, "Body"},
	{"Mane", Vector3.new(1.4, 1.3, 1.1), CFrame.new(0, 0.02, -0.5), FUR2, "Body"},
	{"Collar", Vector3.new(1.5, 1.4, 0.26), CFrame.new(0, 0.02, -0.78), C(205, 25, 25), "Body"},
	{"Head", Vector3.new(1.2, 1.2, 0.8), CFrame.new(0, 0.3, -1.3), FUR2, "Head"},
	{"Snout", Vector3.new(0.6, 0.5, 0.6), CFrame.new(0, 0.1, -2.0), C(196, 174, 150), "Head"},
	{"Nose", Vector3.new(0.32, 0.2, 0.1), CFrame.new(0, 0.28, -2.32), C(30, 30, 30), "Head"},
	{"EyeL", Vector3.new(0.18, 0.18, 0.06), CFrame.new(-0.32, 0.45, -1.72), C(30, 30, 30), "Head"},
	{"EyeR", Vector3.new(0.18, 0.18, 0.06), CFrame.new(0.32, 0.45, -1.72), C(30, 30, 30), "Head"},
	{"PupilL", Vector3.new(0.12, 0.12, 0.07), CFrame.new(-0.32, 0.45, -1.76), C(0, 0, 0), "Head"},
	{"PupilR", Vector3.new(0.12, 0.12, 0.07), CFrame.new(0.32, 0.45, -1.76), C(0, 0, 0), "Head"},
	{"EarL", Vector3.new(0.36, 0.4, 0.2), CFrame.new(-0.42, 1.1, -1.15), C(170, 170, 170), "Head"},
	{"EarR", Vector3.new(0.36, 0.4, 0.2), CFrame.new(0.42, 1.1, -1.15), C(170, 170, 170), "Head"},
	{"Tail", Vector3.new(0.4, 0.4, 1.4), CFrame.new(0, 0.3, 1.6), FUR, "Tail"},
	{"LegFL", Vector3.new(0.4, 1.6, 0.4), CFrame.new(-0.4, -1.3, -0.65), LEG, "FL"},
	{"LegFR", Vector3.new(0.4, 1.6, 0.4), CFrame.new(0.4, -1.3, -0.65), LEG, "FR"},
	{"LegBL", Vector3.new(0.4, 1.6, 0.4), CFrame.new(-0.4, -1.3, 0.65), LEG, "BL"},
	{"LegBR", Vector3.new(0.4, 1.6, 0.4), CFrame.new(0.4, -1.3, 0.65), LEG, "BR"},
	{"Hitbox", Vector3.new(2.4, 3.3, 4.2), CFrame.new(0, -0.4, -0.3), WHITE, "Body"},
}

local function createDog(groundPos)
	local m = Instance.new("Model")
	m.Name = "MCDog"
	m:SetAttribute("Kind", "Dog")
	local dog = {
		model = m, parts = {}, named = {}, entries = {}, pos = groundPos, home = groundPos,
		yaw = math.rad(math.random(0, 359)), targetYaw = 0, tamed = false, mode = "wander",
		state = "normal", stateT = 0,
		sit = 0, lay = 0, rear = 0, peeA = 0, arm = 0, phase = 0, amp = 0, speed = 0,
		headYaw = 0, phi = 0, thinking = false, waitT = 2, chasing = false, creepy = false, defiant = false,
	}
	dog.targetYaw = dog.yaw
	for _, d in ipairs(DOG_PARTS) do
		local p = mk(m, d[1], d[2], CFrame.new(), d[4], Enum.Material.SmoothPlastic, false)
		if d[1] == "Hitbox" or d[1] == "Collar" or d[1] == "PupilL" or d[1] == "PupilR" then p.Transparency = 1 end
		local entry = {inst = p, base = d[3], group = d[5]}
		dog.named[d[1]] = p
		dog.entries[d[1]] = entry
		dog.parts[#dog.parts + 1] = entry
	end
	dog.pupils = {{entry = dog.entries.PupilL, x = -1}, {entry = dog.entries.PupilR, x = 1}}
	m.PrimaryPart = dog.named.Hitbox
	m.Parent = world

	local hit, head = dog.named.Hitbox, dog.named.Head
	local bb = new("BillboardGui", {
		Size = UDim2.fromOffset(140, 26), StudsOffset = Vector3.new(0, 3.2, 0),
		AlwaysOnTop = true, MaxDistance = 300, Adornee = hit,
	}, hit)
	dog.label = new("TextLabel", {
		Size = UDim2.fromScale(1, 1), BackgroundTransparency = 1, Text = "Wild Dog", TextColor3 = WHITE,
		TextStrokeTransparency = 0, Font = Enum.Font.GothamBold, TextScaled = true,
	}, bb)
	local qb = new("BillboardGui", {
		Size = UDim2.fromOffset(46, 46), StudsOffset = Vector3.new(0, 1.9, 0),
		AlwaysOnTop = true, Enabled = false, Adornee = head,
	}, head)
	new("TextLabel", {
		Size = UDim2.fromScale(1, 1), BackgroundTransparency = 1, Text = "?", TextColor3 = C(255, 0, 0),
		TextStrokeColor3 = WHITE, TextStrokeTransparency = 0, Font = Enum.Font.GothamBlack, TextScaled = true,
	}, qb)
	dog.qBB = qb
	dogByModel[m] = dog
	return dog
end

local function setCreepy(dog)
	if dog.creepy then return end
	dog.creepy = true
	for _, n in ipairs({"EyeL", "EyeR"}) do
		dog.named[n].Size = Vector3.new(0.42, 0.42, 0.06)
		dog.named[n].Color = WHITE
	end
	dog.named.PupilL.Transparency = 0
	dog.named.PupilR.Transparency = 0
end

local function setState(dog, s)
	dog.state = s
	dog.stateT = 0
	if s == "climb" then dog.climbFrom = dog.pos end
	if s == "pee" then dog.emitAcc = 0 end
	if s == "close" then dog.lidShut = false end
end

local function faceToward(dog, tp)
	dog.targetYaw = math.atan2(-(tp.X - dog.pos.X), -(tp.Z - dog.pos.Z))
end

local function walkToward(dog, tgt, speed, dt)
	local d = Vector3.new(tgt.X - dog.pos.X, 0, tgt.Z - dog.pos.Z)
	local dist = d.Magnitude
	if dist < 0.6 then return true end
	local dir = d / dist
	dog.pos = dog.pos + dir * math.min(speed * dt, dist)
	dog.targetYaw = math.atan2(-dir.X, -dir.Z)
	dog.speed = speed
	return false
end

local function spawnDrop(from, to)
	local p = Instance.new("Part")
	p.Shape = Enum.PartType.Ball
	p.Size = Vector3.new(.3, .3, .3)
	p.Color = C(240, 215, 40)
	p.Material = Enum.Material.Neon
	p.Anchored, p.CanCollide, p.CanQuery, p.CanTouch = true, false, false, false
	p.CFrame = CFrame.new(from)
	p.Parent = world
	drops[#drops + 1] = {p = p, from = from, to = to, t0 = tick(), dur = 0.55 + math.random() * 0.15, arc = 2 + math.random()}
end

local function addPuddle(ch)
	local p = mk(world, "Puddle", Vector3.new(0.06, 3, 3),
		ch.origin * CFrame.new(0, 0.06, -2.6) * CFrame.Angles(0, 0, math.pi / 2), C(225, 200, 40), Enum.Material.SmoothPlastic, false)
	p.Shape = Enum.PartType.Cylinder
	p.CanQuery = false
	p.Transparency = 0.15
end

local function enterClimb(dog)
	setState(dog, "climb")
	if not dog.defiant then
		dog.defiant = true
		setCreepy(dog)
		if dogBed then addBlood(dogBed) end
		dog.thinking = false
		dog.qBB.Enabled = false
		toast("The dog jumped into your bed... and he won't come out.", C(255, 120, 120))
	end
end

local function onDogInBed()
	if story.phase == 1 then
		story.phase = 2
		for _, ch in ipairs(placedChests) do ch.locked = false end
		toast("The dog is back in bed, staring at you. You can sleep now.", C(255, 200, 120))
	end
end

local function updateDog(dog, dt)
	local hrp = getHRP()
	dog.speed = 0
	dog.stateT = dog.stateT + dt
	local st = dog.state
	local bed = dogBed

	if st == "normal" then
		if dog.thinking then
			-- stands still, arm raised
		elseif not dog.tamed then
			dog.waitT = dog.waitT - dt
			if dog.moveTarget then
				if walkToward(dog, dog.moveTarget, 4, dt) then
					dog.moveTarget = nil
					dog.waitT = 2 + math.random() * 4
				end
			elseif dog.waitT <= 0 then
				local a, r = math.random() * math.pi * 2, 5 + math.random() * 20
				dog.moveTarget = dog.home + Vector3.new(math.cos(a) * r, 0, math.sin(a) * r)
			end
		elseif dog.mode == "follow" and hrp then
			local tp = hrp.Position
			local d = flatDist(tp, dog.pos)
			if d > 90 then
				dog.pos = Vector3.new(tp.X + 4, tp.Y - 3, tp.Z + 4)
			elseif d > (dog.chasing and 4.5 or 8) then
				dog.chasing = true
				walkToward(dog, tp, d > 20 and 16 or 9, dt)
			else
				dog.chasing = false
				faceToward(dog, tp)
			end
		elseif dog.mode == "spin" then
			dog.yaw = dog.yaw + 7 * dt
			dog.targetYaw = dog.yaw
		end
	elseif st == "toBed" or st == "returning" then
		if bed then
			if walkToward(dog, bed.approach, st == "toBed" and 14 or 10, dt) then enterClimb(dog) end
		else
			dog.state = "normal"
		end
	elseif st == "climb" then
		if bed then
			local u = math.min(dog.stateT / 0.9, 1)
			dog.pos = dog.climbFrom:Lerp(bed.layPos, u) + Vector3.new(0, math.sin(u * math.pi) * 1.4, 0)
			dog.targetYaw = bed.dogYaw
			if u >= 1 then
				setState(dog, "inBed")
				onDogInBed()
			end
		end
	elseif st == "inBed" then
		if bed then
			dog.pos = bed.layPos
			dog.targetYaw = bed.dogYaw
		end
	elseif st == "dig" then
		if hrp and dog.stateT > 2.5 and flatDist(hrp.Position, dog.pos) < CONFIG.WakeApproach then
			setState(dog, "close")
		end
	elseif st == "close" then
		if hrp then faceToward(dog, hrp.Position) end
		if dog.stateT > 0.3 and not dog.lidShut then
			dog.lidShut = true
			animateLid(dog.dugChest, 0)
		end
		if dog.stateT > 1.2 then setState(dog, "stare") end
	elseif st == "stare" then
		if hrp then faceToward(dog, hrp.Position) end
		if dog.stateT > 1.8 then setState(dog, "lift") end
	elseif st == "lift" then
		if hrp then faceToward(dog, hrp.Position) end
		if dog.stateT > 1.0 then setState(dog, "pee") end
	elseif st == "pee" then
		if hrp then faceToward(dog, hrp.Position) end
		dog.emitAcc = dog.emitAcc + dt
		while dog.emitAcc > 0.04 do
			dog.emitAcc = dog.emitAcc - 0.04
			local tip = (dog.named.LegBR.CFrame * CFrame.new(0, -0.7, 0)).Position
			local target = (dog.dugChest.origin * CFrame.new((math.random() - .5) * 1.2, 2.2, (math.random() - .5) * 1.2)).Position
			spawnDrop(tip, target)
		end
		if dog.stateT > 3 then
			addPuddle(dog.dugChest)
			setState(dog, "lower")
		end
	elseif st == "lower" then
		if hrp then faceToward(dog, hrp.Position) end
		if dog.stateT > 0.8 then setState(dog, "returning") end
	end

	-- smooth turning
	local diff = (dog.targetYaw - dog.yaw + math.pi) % (2 * math.pi) - math.pi
	dog.yaw = dog.yaw + diff * math.min(1, dt * 8)

	-- ground
	if st ~= "climb" and st ~= "inBed" then
		local gy = groundAt(dog.pos.X, dog.pos.Z, dog.pos.Y + 8, true)
		if gy then
			dog.pos = Vector3.new(dog.pos.X, dog.pos.Y + (gy.Y - dog.pos.Y) * math.min(1, dt * 12), dog.pos.Z)
		end
	end

	-- animation targets
	local k = math.min(1, dt * 5)
	local sitT = (st == "normal" and dog.mode == "sit") and 1 or 0
	local rearT = (st == "dig") and 1 or 0
	local layT = (st == "inBed" or (st == "climb" and dog.stateT > 0.45)) and 1 or 0
	local peeT = (st == "lift" or st == "pee") and 1 or 0
	dog.sit = dog.sit + (sitT - dog.sit) * k
	dog.rear = dog.rear + (rearT - dog.rear) * k
	dog.lay = dog.lay + (layT - dog.lay) * k
	dog.peeA = dog.peeA + (peeT - dog.peeA) * math.min(1, dt * 6)
	dog.arm = dog.arm + (((st == "normal" and dog.thinking) and 1 or 0) - dog.arm) * math.min(1, dt * 8)
	dog.amp = dog.amp + ((dog.speed > 0 and 1 or 0) - dog.amp) * math.min(1, dt * 10)
	dog.phase = dog.phase + dt * (dog.speed > 0 and dog.speed * 1.1 or 0)

	-- head / eyes tracking the player
	local headT = 0
	dog.phi = 0
	if hrp then
		local tmp = CFrame.new(dog.pos) * CFrame.Angles(0, dog.yaw, 0)
		local lpnt = tmp:PointToObjectSpace(hrp.Position)
		dog.phi = math.clamp(math.atan2(-lpnt.X, -lpnt.Z), -1.2, 1.2)
		if dog.creepy then
			if st == "inBed" then
				headT = dog.phi * 0.25
			elseif st == "close" or st == "stare" or st == "lift" or st == "pee" or st == "lower" then
				headT = dog.phi
			end
		end
	end
	dog.headYaw = dog.headYaw + (headT - dog.headYaw) * math.min(1, dt * 6)
	if dog.creepy then
		local res = dog.phi - dog.headYaw
		local ox = -math.clamp(res * 1.2, -1, 1) * 0.12
		for _, pu in ipairs(dog.pupils) do
			pu.entry.base = CFrame.new(pu.x * 0.32 + ox, 0.45, -1.76)
		end
	end

	-- pose
	local t = tick()
	local sit, lay, rear, armA, peeA = dog.sit, dog.lay, dog.rear, dog.arm, dog.peeA
	local ang = CFrame.Angles
	local sw = math.sin(dog.phase) * 0.75 * dog.amp
	local digS = math.sin(t * 9)
	local baseFront = -math.rad(35) * sit + math.rad(80) * lay
	local raise = math.rad(145) + math.rad(8) * math.sin(t * 12)

	local fl = (baseFront + sw) * (1 - rear) + (math.rad(15) - math.rad(28) * digS) * rear
	local fr = (((baseFront - sw) * (1 - armA) + raise * armA)) * (1 - rear) + (math.rad(15) + math.rad(28) * digS) * rear
	local backBase = math.rad(55) * sit + math.rad(80) * lay
	local bl = (backBase - sw * (1 - sit)) * (1 - rear) - math.rad(45) * rear
	local br = (backBase + sw * (1 - sit)) * (1 - rear) - math.rad(45) * rear

	local wag = math.sin(t * (dog.tamed and 10 or 3)) * (dog.tamed and 0.45 or 0.12)
	if st == "dig" then wag = math.sin(t * 14) * 0.5 end
	local tailBase = (dog.tamed and -0.5 or 0.7) + 0.3 * sit + 0.6 * lay
	local headPitch = -math.rad(30) * sit - math.rad(60) * rear - 0.12 * lay + math.sin(t * 9) * 0.08 * rear

	local poses = {
		Head = ang(headPitch, dog.headYaw, math.rad(15) * armA),
		Tail = ang(tailBase, 0, 0) * ang(0, wag, 0),
		FL = ang(fl, 0, 0),
		FR = ang(fr, 0, 0),
		BL = ang(bl, 0, 0),
		BR = ang(br + math.rad(15) * peeA, 0, math.rad(80) * peeA),
	}

	local pitch = math.rad(35) * sit + math.rad(45) * rear
	local h = 2.1 + (1.0 - 2.1) * sit + (0.75 - 2.1) * lay + (2.41 - 2.1) * rear
	local bob = math.abs(math.sin(dog.phase)) * 0.06 * dog.amp
	local rootCF = CFrame.new(dog.pos + Vector3.new(0, h + bob, 0)) * ang(0, dog.yaw, 0) * ang(pitch, 0, 0)

	for _, p in ipairs(dog.parts) do
		local pose = poses[p.group]
		if pose then
			local pv = GROUP_PIVOT[p.group]
			p.inst.CFrame = rootCF * CFrame.new(pv) * pose * CFrame.new(-pv) * p.base
		else
			p.inst.CFrame = rootCF * p.base
		end
	end
end

local function floatText(pos, txt, col)
	local p = mk(world, "FX", Vector3.new(.2, .2, .2), CFrame.new(pos), WHITE, nil, false)
	p.Transparency = 1
	local bb = new("BillboardGui", {
		Size = UDim2.fromOffset(40, 40), StudsOffset = Vector3.new((math.random() - .5) * 2.5, 0, 0),
		AlwaysOnTop = true, Adornee = p,
	}, p)
	local l = new("TextLabel", {
		Size = UDim2.fromScale(1, 1), BackgroundTransparency = 1, Text = txt, TextColor3 = col,
		TextScaled = true, Font = Enum.Font.GothamBold, TextStrokeTransparency = 0.5,
	}, bb)
	TweenService:Create(bb, TweenInfo.new(1.2), {StudsOffset = bb.StudsOffset + Vector3.new(0, 4, 0)}):Play()
	TweenService:Create(l, TweenInfo.new(1.2), {TextTransparency = 1, TextStrokeTransparency = 1}):Play()
	Debris:AddItem(p, 1.4)
end

local STATUS = {follow = "Following you!", sit = "Sitting.", spin = "Spinning!", stay = "Staying here."}
commandDog = function(dog, mode)
	if dog.defiant then
		toast("The dog won't move. He just stares at you...", C(255, 140, 140))
		return
	end
	dog.cmdTok = (dog.cmdTok or 0) + 1
	local my = dog.cmdTok
	dog.thinking = true
	dog.qBB.Enabled = true
	task.delay(2, function()
		if not alive or dog.cmdTok ~= my then return end
		dog.thinking = false
		dog.qBB.Enabled = false
		dog.mode = mode
		dog.chasing = false
		toast("Dog: " .. STATUS[mode], C(150, 210, 255))
	end)
end

local function checkSteal()
	local d = theDog
	if dogBed and d and d.tamed and d.state == "normal" and not d.defiant then
		d.thinking = false
		d.qBB.Enabled = false
		setState(d, "toBed")
		toast("The dog is eyeing your bed...", C(255, 200, 120))
	end
end

local function tryTame(dog)
	if inv.bone <= 0 then toast("You need a bone! Open the chest.", C(255, 170, 60)) return end
	if selected ~= "bone" then toast("Tap the Bone in your hotbar to hold it.", C(255, 170, 60)) return end
	inv.bone = inv.bone - 1
	if inv.bone <= 0 then selected = nil end
	refreshAll()
	local head = dog.named.Head.Position + Vector3.new(0, 1.5, 0)
	if math.random() < CONFIG.TameChance then
		dog.tamed = true
		dog.mode = "follow"
		dog.moveTarget = nil
		dog.named.Collar.Transparency = 0
		dog.label.Text = "Your Dog"
		dog.label.TextColor3 = C(120, 255, 120)
		theDog = dog
		for _ = 1, 7 do floatText(head, "\u{2665}", C(255, 70, 90)) end
		toast("You tamed the dog!", C(120, 255, 120))
		checkSteal()
	else
		for _ = 1, 3 do floatText(head, "...", C(200, 200, 200)) end
		toast("The dog ate the bone but isn't tame yet. Try again!", C(255, 200, 100))
	end
end

local function startDogEvent()
	local ch, dog = placedChests[1], theDog
	if not ch or not dog then return end
	ch.locked = true
	dog.dugChest = ch
	local o = ch.origin
	local p = (o * CFrame.new(0, 0, -3.2)).Position
	dog.pos = Vector3.new(p.X, o.Position.Y, p.Z)
	local dir = -o.LookVector
	dog.yaw = math.atan2(-dir.X, -dir.Z)
	dog.targetYaw = dog.yaw
	dog.sit, dog.lay, dog.rear = 0, 0, 0
	setState(dog, "dig")
	animateLid(ch, math.rad(100))
end

------------------------------------------------------------------ BREAK / PLACE
local function burst(pos, color, n)
	for _ = 1, n do
		local p = Instance.new("Part")
		p.Size = Vector3.new(0.8, 0.8, 0.8)
		p.Color = color
		p.Material = Enum.Material.SmoothPlastic
		p.CanTouch = false
		p.CFrame = CFrame.new(pos + Vector3.new((math.random() - .5) * 2, (math.random() - .5) * 2, (math.random() - .5) * 2))
		p.AssemblyLinearVelocity = Vector3.new((math.random() - .5) * 24, 10 + math.random() * 12, (math.random() - .5) * 24)
		p.Parent = world
		Debris:AddItem(p, 1.4)
	end
end

local function breakGamePart(res)
	local part = res.Instance
	if not part:IsA("BasePart") or part:IsA("Terrain") then return end
	local hrp = getHRP()
	if hrp and (hrp.Position - res.Position).Magnitude > CONFIG.BreakReach then toast("Too far to break!", C(255, 170, 60)) return end
	if part.Size.Magnitude > 150 then toast("That part is too big to break.", C(255, 170, 60)) return end
	local mdl = part:FindFirstAncestorOfClass("Model")
	if mdl and mdl:FindFirstChildOfClass("Humanoid") then return end
	brokenParts[#brokenParts + 1] = {part = part, t = part.Transparency, c = part.CanCollide, q = part.CanQuery}
	local col = part.Color
	part.Transparency = 1
	part.CanCollide = false
	part.CanQuery = false
	burst(res.Position, col, 8)
	inv.voxel = inv.voxel + 1
	refreshAll()
	toast("+1 Voxel", C(140, 190, 255))
end

local function breakPlank(p)
	local hrp = getHRP()
	if hrp and (hrp.Position - p.Position).Magnitude > CONFIG.BreakReach then toast("Too far to break!", C(255, 170, 60)) return end
	burst(p.Position, p.Color, 8)
	p:Destroy()
	inv.plank = inv.plank + 1
	refreshAll()
end

local BLOCK = CONFIG.BlockSize
local function snap(v) return math.floor(v / BLOCK + 0.5) * BLOCK end

local function playerYaw90()
	local hrp = getHRP()
	local l = hrp.CFrame.LookVector
	local yaw = math.atan2(-l.X, -l.Z)
	return math.floor(yaw / (math.pi / 2) + 0.5) * (math.pi / 2)
end

local function overlapFree(cf, size)
	local op = OverlapParams.new()
	op.FilterType = Enum.RaycastFilterType.Include
	local list = {world}
	if lp.Character then list[2] = lp.Character end
	op.FilterDescendantsInstances = list
	local parts = workspace:GetPartBoundsInBox(cf, size - Vector3.new(0.4, 0.4, 0.4), op)
	for _, p in ipairs(parts) do
		if p.CanCollide then return false end
	end
	return true
end

local function computePlacement(kind, res)
	local hrp = getHRP()
	if not res or not hrp then return nil end
	local inst, n = res.Instance, res.Normal
	local info = {kind = kind}
	if kind == "plank" then
		local pos
		if inst:GetAttribute("Kind") == "Plank" then
			local ax
			if math.abs(n.X) >= math.abs(n.Y) and math.abs(n.X) >= math.abs(n.Z) then
				ax = Vector3.new(math.sign(n.X), 0, 0)
			elseif math.abs(n.Y) >= math.abs(n.Z) then
				ax = Vector3.new(0, math.sign(n.Y), 0)
			else
				ax = Vector3.new(0, 0, math.sign(n.Z))
			end
			pos = inst.Position + ax * BLOCK
		else
			local p = res.Position + n * (BLOCK / 2)
			if n.Y > 0.5 then
				pos = Vector3.new(snap(p.X), res.Position.Y + BLOCK / 2, snap(p.Z))
			else
				pos = Vector3.new(snap(p.X), snap(p.Y), snap(p.Z))
			end
		end
		info.cf = CFrame.new(pos)
		info.gcf = info.cf
		info.size = Vector3.new(BLOCK, BLOCK, BLOCK)
		info.pos = pos
	elseif kind == "bed" then
		info.cf = CFrame.new(res.Position) * CFrame.Angles(0, playerYaw90(), 0)
		info.gcf = info.cf * CFrame.new(0, 1.35, 0)
		info.size = Vector3.new(3.7, 2.7, 7.0)
		info.pos = res.Position
		if n.Y < 0.5 then info.bad = "Place it on the floor." end
	else -- chest
		local flat = Vector3.new(hrp.Position.X, res.Position.Y, hrp.Position.Z)
		if (flat - res.Position).Magnitude > 0.5 then
			info.cf = CFrame.lookAt(res.Position, flat)
		else
			info.cf = CFrame.new(res.Position)
		end
		info.gcf = info.cf * CFrame.new(0, 1.5, 0)
		info.size = Vector3.new(3.1, 3, 3.1)
		info.pos = res.Position
		if n.Y < 0.5 then info.bad = "Place it on the floor." end
	end
	if not info.bad and flatDist(hrp.Position, info.pos) > CONFIG.PlaceReach then info.bad = "Too far away." end
	if not info.bad and not overlapFree(info.gcf, info.size) then info.bad = "Something is in the way." end
	return info
end

local function doPlace(info)
	if not info then return end
	if info.bad then toast(info.bad, C(255, 170, 60)) return end
	local kind = info.kind
	if inv[kind] <= 0 then return end
	if kind == "plank" then
		local g = math.random(-5, 5)
		local p = mk(world, "Plank", Vector3.new(BLOCK, BLOCK, BLOCK), info.cf, C(181 + g, 143 + g, 87 + g), Enum.Material.WoodPlanks, true)
		p:SetAttribute("Kind", "Plank")
	elseif kind == "bed" then
		local bed = buildBed(info.cf)
		if not dogBed then
			dogBed = bed
			checkSteal()
		end
	else
		local ch = buildChest(info.cf, nil)
		placedChests[#placedChests + 1] = ch
	end
	inv[kind] = inv[kind] - 1
	refreshAll()
end

------------------------------------------------------------------ INTERACTION
local function findKind(inst)
	while inst and inst ~= workspace do
		if inst:GetAttribute("Kind") then return inst end
		inst = inst.Parent
	end
	return nil
end

local function inReach(m)
	local hrp = getHRP()
	local pos = posOf(m)
	if not hrp or not pos then return false end
	local kind = m:GetAttribute("Kind")
	local reach = CONFIG.Reach + ((kind == "Tree") and 5 or 0) + ((kind == "Bed") and 3 or 0)
	return flatDist(hrp.Position, pos) <= reach
end

local function isNight()
	return clock >= CONFIG.SleepFrom or clock < 6
end

local function fadeTo(a, dur)
	TweenService:Create(fade, TweenInfo.new(dur), {BackgroundTransparency = a}):Play()
	TweenService:Create(fadeTxt, TweenInfo.new(dur), {TextTransparency = 1 - a}):Play()
	task.wait(dur)
end

local function trySleep(bed)
	if story.sleeping then return end
	if bed == dogBed then
		toast("The dog is in this bed. He's staring at you...", C(255, 140, 140))
		return
	end
	if story.phase == 1 then
		toast("You can't sleep... you hear rustling near your chest.", C(255, 170, 60))
		return
	end
	local miss = {}
	if #placedChests == 0 then miss[#miss + 1] = "a placed chest" end
	if not (theDog and theDog.tamed) then miss[#miss + 1] = "a tamed dog" end
	if #miss > 0 then
		toast("You can't sleep yet. Missing: " .. table.concat(miss, ", "), C(255, 170, 60))
		return
	end
	if not (CONFIG.SleepAnytime or isNight()) then
		toast("You can only sleep at night (after " .. CONFIG.SleepFrom .. ":00).", C(255, 170, 60))
		return
	end
	story.sleeping = true
	closePanels()
	task.spawn(function()
		local hrp = getHRP()
		if hrp then hrp.Anchored = true end
		fadeTo(0, 0.8)
		task.wait(CONFIG.SleepSeconds)
		local wasPhase = story.phase
		if wasPhase == 0 then
			clock = 0
			clockPaused = true
		else
			clock = 6
			clockPaused = false
			story.day = story.day + 1
			story.phase = 3
		end
		Lighting.ClockTime = clock
		hrp = getHRP()
		if hrp then
			hrp.CFrame = bed.origin * CFrame.new(3.6, 3.5, 0)
			hrp.AssemblyLinearVelocity = Vector3.zero
			hrp.Anchored = false
		end
		fadeTo(1, 1)
		story.sleeping = false
		if wasPhase == 0 then
			story.phase = 1
			startDogEvent()
			toast("You wake up in the middle of the night... something is rustling.", C(255, 200, 120))
		else
			toast("Good morning! Day " .. story.day .. " begins.", C(255, 240, 150))
		end
	end)
end

local lastAct = 0
local function interact(m)
	if not m or not m.Parent or story.sleeping then return end
	local kind = m:GetAttribute("Kind")
	if not kind or kind == "Plank" then return end
	if tick() - lastAct < 0.2 then return end
	lastAct = tick()
	if not inReach(m) then toast("Get closer!", C(255, 170, 60)) return end
	if kind == "Chest" then
		local ch = chestByModel[m]
		if ch then openChest(ch) end
	elseif kind == "Dog" then
		local d = dogByModel[m]
		if not d then return end
		if d.tamed then
			closePanels()
			fit(dogScale, 260, 190)
			dogPanel.Visible = true
		else
			tryTame(d)
		end
	elseif kind == "Tree" then
		chopTree(m)
	elseif kind == "Bed" then
		local b = bedByModel[m]
		if b then trySleep(b) end
	end
end

local function nearestInteractive()
	local hrp = getHRP()
	if not hrp then return nil end
	local best, bd = nil, 1e9
	for _, m in ipairs(world:GetChildren()) do
		if m:IsA("Model") and m:GetAttribute("Kind") and m.PrimaryPart then
			local d = flatDist(hrp.Position, m.PrimaryPart.Position)
			if d < bd then best, bd = m, d end
		end
	end
	return best
end

local function handleAction(ray)
	if story.sleeping then return end
	local res = workspace:Raycast(ray.Origin, ray.Direction.Unit * 200, rp(false))
	if selected and PLACEABLE[selected] then
		doPlace(computePlacement(selected, res))
		return
	end
	local target = res and findKind(res.Instance)
	if breakMode then
		if target and target:GetAttribute("Kind") == "Plank" then breakPlank(target) return end
		if target then interact(target) return end
		if res then breakGamePart(res) end
		return
	end
	if target then interact(target) end
end

local lastTarget = nil
local function promptFor(m)
	local k = m:GetAttribute("Kind")
	if k == "Chest" then return "Open Chest" end
	if k == "Tree" then return "Chop Tree" end
	if k == "Plank" then return "Plank (turn on BREAK to remove)" end
	if k == "Bed" then
		if bedByModel[m] == dogBed and theDog and theDog.defiant then return "Dog's Bed" end
		return "Sleep"
	end
	if k == "Dog" then
		local d = dogByModel[m]
		if d and d.tamed then return "Command Dog" end
		if selected == "bone" then return "Tame Dog (use Bone)" end
		return "Wild Dog - hold a Bone"
	end
	return ""
end

local function updatePrompt()
	local cam = getCam()
	local vs = cam.ViewportSize
	local ray = cam:ViewportPointToRay(vs.X / 2, vs.Y / 2)
	local res = workspace:Raycast(ray.Origin, ray.Direction.Unit * 120, rp(false))
	local t = res and findKind(res.Instance) or nil
	lastTarget = t

	-- placement ghost
	if selected and PLACEABLE[selected] then
		local info = computePlacement(selected, res)
		if info then
			ghost.Size = info.size
			ghost.CFrame = info.gcf
			ghost.Color = info.bad and C(255, 70, 70) or C(60, 255, 100)
			ghost.Transparency = 0.65
			promptLbl.Text = info.bad or ("Place " .. NAMES[selected])
			promptLbl.TextColor3 = info.bad and C(255, 170, 60) or C(120, 255, 120)
		else
			ghost.Transparency = 1
			promptLbl.Text = ""
		end
		return
	end
	ghost.Transparency = 1

	if breakMode then
		promptLbl.Text = "BREAK mode: aim and tap USE"
		promptLbl.TextColor3 = C(255, 120, 120)
		return
	end

	local hrp = getHRP()
	local pos = t and posOf(t)
	if t and hrp and pos and flatDist(hrp.Position, pos) < 60 then
		local ok = inReach(t)
		promptLbl.Text = promptFor(t) .. (ok and "" or "  (get closer)")
		promptLbl.TextColor3 = ok and C(120, 255, 120) or C(255, 170, 60)
		for _, b in ipairs(crossBars) do b.BackgroundColor3 = ok and C(120, 255, 120) or WHITE end
	else
		promptLbl.Text = ""
		for _, b in ipairs(crossBars) do b.BackgroundColor3 = WHITE end
	end
end

connect(useBtn.Activated, function()
	if story.sleeping then return end
	local cam = getCam()
	local vs = cam.ViewportSize
	if (selected and PLACEABLE[selected]) or breakMode then
		handleAction(cam:ViewportPointToRay(vs.X / 2, vs.Y / 2))
		return
	end
	local t = lastTarget
	if t and t:GetAttribute("Kind") == "Plank" then t = nil end
	if not t or not inReach(t) then t = nearestInteractive() end
	if t then interact(t) else toast("Nothing to use here.", C(255, 170, 60)) end
end)

local function tapAt(x, y)
	if story.sleeping then return end
	local cam = getCam()
	if (selected and PLACEABLE[selected]) or breakMode then
		handleAction(cam:ViewportPointToRay(x, y))
		return
	end
	for _, ray in ipairs({cam:ViewportPointToRay(x, y), cam:ScreenPointToRay(x, y)}) do
		local res = workspace:Raycast(ray.Origin, ray.Direction.Unit * 150, rp(false))
		local t = res and findKind(res.Instance)
		if t then interact(t) return end
	end
end

connect(UIS.TouchTap, function(positions, processed)
	if processed then return end
	local p = positions[1]
	if p then tapAt(p.X, p.Y) end
end)
connect(UIS.InputBegan, function(input, processed)
	if processed then return end
	if input.UserInputType == Enum.UserInputType.MouseButton1 then
		local loc = UIS:GetMouseLocation()
		tapAt(loc.X, loc.Y)
	end
end)

-- crafting
connect(craftBtn.Activated, function()
	if craftPanel.Visible then craftPanel.Visible = false return end
	closePanels()
	refreshCraft()
	fit(craftScale, 300, 276)
	craftPanel.Visible = true
end)
connect(planksBtn.Activated, function()
	if inv.log < 1 then toast("You need 1 log.", C(255, 170, 60)) return end
	inv.log = inv.log - 1
	inv.plank = inv.plank + CONFIG.PlanksPerLog
	refreshAll()
	refreshCraft()
end)
connect(bedBtn.Activated, function()
	if inv.voxel < CONFIG.BedVoxels then
		toast("Need " .. CONFIG.BedVoxels .. " voxels. Turn on BREAK and break map parts.", C(255, 170, 60))
		return
	end
	inv.voxel = inv.voxel - CONFIG.BedVoxels
	inv.bed = inv.bed + 1
	refreshAll()
	refreshCraft()
	toast("Crafted a Bed! Select it in the hotbar to place it.", C(120, 255, 120))
end)
connect(chestBtn.Activated, function()
	if inv.plank < CONFIG.ChestPlanks then
		toast("Need " .. CONFIG.ChestPlanks .. " planks.", C(255, 170, 60))
		return
	end
	inv.plank = inv.plank - CONFIG.ChestPlanks
	inv.chest = inv.chest + 1
	refreshAll()
	refreshCraft()
	toast("Crafted a Chest! Select it in the hotbar to place it.", C(120, 255, 120))
end)

------------------------------------------------------------------ MAIN LOOP
connect(RunService.RenderStepped, function(dt)
	if not alive then return end

	if not clockPaused then clock = (clock + dt * 24 / CONFIG.DayLength) % 24 end
	Lighting.ClockTime = clock
	clockLbl.Text = string.format("Day %d   %02d:%02d", story.day, math.floor(clock), math.floor((clock % 1) * 60))

	for _, d in pairs(dogByModel) do updateDog(d, dt) end

	for i = #drops, 1, -1 do
		local d = drops[i]
		local u = (tick() - d.t0) / d.dur
		if u >= 1 or not d.p.Parent then
			d.p:Destroy()
			table.remove(drops, i)
		else
			d.p.Position = d.from:Lerp(d.to, u) + Vector3.new(0, 4 * u * (1 - u) * d.arc, 0)
		end
	end

	updatePrompt()

	if chestOpen and currentChest then
		local hrp = getHRP()
		if hrp and flatDist(hrp.Position, currentChest.origin.Position) > 35 then closeChest() end
	end
end)

------------------------------------------------------------------ SPAWN EVERYTHING
Lighting.ClockTime = clock
refreshAll()
refreshCraft()

task.spawn(function()
	local hrp = getHRP()
	while alive and not hrp do
		task.wait(0.5)
		hrp = getHRP()
	end
	if not alive then return end

	local look = Vector3.new(hrp.CFrame.LookVector.X, 0, hrp.CFrame.LookVector.Z)
	if look.Magnitude < 0.01 then look = Vector3.new(0, 0, -1) end
	local cp = hrp.Position + look.Unit * CONFIG.ChestDistance
	local cg = groundAt(cp.X, cp.Z, hrp.Position.Y + 100, true) or Vector3.new(cp.X, hrp.Position.Y - 3, cp.Z)
	local startChest = buildChest(CFrame.lookAt(cg, Vector3.new(hrp.Position.X, cg.Y, hrp.Position.Z)), "Chest")
	startChest.data[1] = {kind = "bone", count = CONFIG.BonesInChest}

	local dp = findSpot(CONFIG.DogMinRadius, CONFIG.DogMaxRadius, 60)
		or findSpot(20, 60, 40)
		or (hrp.Position + Vector3.new(20, -3, 20))
	createDog(dp)

	toast("A chest appeared 30 studs ahead!", C(255, 220, 90))

	for i = 1, CONFIG.TreeCount do
		if not alive then return end
		spawnTree()
		if i % 5 == 0 then task.wait() end
	end
end)
