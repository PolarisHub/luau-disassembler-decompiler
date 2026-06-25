local Cases = {}

function Cases.servicesAndRequires(root)
	local ReplicatedStorage = game:GetService("ReplicatedStorage")
	local Players = game:GetService("Players")
	local Modules = ReplicatedStorage:WaitForChild("Modules")
	local Config = require(Modules:WaitForChild("Config"))
	local player = Players.LocalPlayer

	if player and player.Character then
		return Config.forCharacter(player.Character, root)
	end

	return Config.default
end

function Cases.signatureInput(canvas, template, remote)
	local UserInputService = game:GetService("UserInputService")
	local signing = false
	local lastPosition = nil
	local strokes = {}

	local function addStroke(input)
		local position = input.Position
		local stroke = template:Clone()
		stroke.Position = UDim2.fromOffset(position.X, position.Y)
		stroke.Parent = canvas
		table.insert(strokes, stroke)
		lastPosition = position
	end

	canvas.InputBegan:Connect(function(input)
		if input.UserInputType ~= Enum.UserInputType.MouseButton1 then
			return
		end

		signing = true
		addStroke(input)
	end)

	canvas.InputEnded:Connect(function(input)
		if input.UserInputType == Enum.UserInputType.MouseButton1 then
			signing = false
			remote:FireServer("Signed", #strokes)
		end
	end)

	UserInputService.InputChanged:Connect(function(input)
		if signing and lastPosition and input.UserInputType == Enum.UserInputType.MouseMovement then
			addStroke(input)
		end
	end)

	return strokes
end

function Cases.buttonLoopCapture(buttons, events)
	local selected = nil

	for _, button in buttons:GetChildren() do
		if button:IsA("GuiButton") then
			button.MouseButton1Click:Connect(function()
				selected = button.Name
				if button.Name == "Reset" then
					events.Reset:Fire()
				else
					events.Select:Fire(button.Name)
				end
			end)
		end
	end

	return function()
		return selected
	end
end

function Cases.bodyPartCloneWeld(character, sourceModel)
	local bodyParts = {
		Head = true,
		Torso = true,
		["Left Arm"] = true,
		["Right Arm"] = true,
		["Left Leg"] = true,
		["Right Leg"] = true,
	}
	local created = {}

	for _, sourcePart in sourceModel:GetChildren() do
		local visiblePart = character.VisibleParts:WaitForChild(sourcePart.Name)
		if bodyParts[sourcePart.Name] then
			visiblePart = character:WaitForChild(sourcePart.Name)
		end

		for _, child in sourcePart:GetChildren() do
			if child ~= sourcePart.PrimaryPart and (child:IsA("Model") or child:IsA("BasePart")) then
				local clone = child:Clone()
				local part = clone

				if clone:IsA("Model") then
					part = clone.PrimaryPart
				end

				if part and part:IsA("BasePart") then
					part.Anchored = false
					part.CanCollide = false
					part.Massless = true

					local offset = sourcePart.PrimaryPart.CFrame:ToObjectSpace(part.CFrame)
					part.CFrame = visiblePart.CFrame * offset

					local weld = Instance.new("Weld")
					weld.Part0 = visiblePart
					weld.Part1 = part
					weld.C0 = CFrame.new()
					weld.C1 = part.CFrame:ToObjectSpace(visiblePart.CFrame)
					weld.Name = part.Name
					weld.Parent = visiblePart

					local transparency = character:GetAttribute("Transparency") or 1
					part.Transparency = transparency
					clone.Parent = character.VisibleParts

					local light = part:FindFirstChildWhichIsA("Light", true)
					if light then
						light:SetAttribute("OriginalBrightness", light.Brightness)
						light.Brightness = light.Brightness * (1 - transparency)
					end

					table.insert(created, part)
				end
			end
		end
	end

	return created
end

function Cases.motorOrWeld(instance, parent, container, useMotor)
	local primaryPart = instance.PrimaryPart or instance:FindFirstChild("Middle")
	instance.Parent = container

	if useMotor and primaryPart then
		local motor = Instance.new("Motor6D")
		motor.Parent = parent
		motor.Part0 = parent
		motor.Part1 = primaryPart
		return motor
	end

	for _, child in pairs(instance:GetChildren()) do
		if child:IsA("BasePart") or child:IsA("UnionOperation") or child:IsA("MeshPart") then
			local origin = CFrame.new(primaryPart.Position)
			local weld = Instance.new("Weld")
			weld.Part0 = primaryPart
			weld.Part1 = child
			weld.C0 = primaryPart.CFrame:Inverse() * origin
			weld.C1 = child.CFrame:Inverse() * origin
			weld.Parent = primaryPart
		end
	end

	local rootWeld = Instance.new("Weld")
	rootWeld.Part0 = parent
	rootWeld.Part1 = primaryPart
	rootWeld.C0 = CFrame.new()
	rootWeld.Parent = parent
	return rootWeld
end

function Cases.evidenceConfig(scriptObject, evidenceTypes, runService)
	local module = {
		Name = scriptObject.Name,
		Evidence = {
			evidenceTypes.GhostOrb,
			evidenceTypes.Handprints,
			evidenceTypes.FreezingTemperatures,
		},
	}

	if runService:IsClient() then
		return module
	end

	module.EffectivenessRange = 100
	module.InteractionRange = 20
	module.HuntProbability = 15
	module.AbilityProbability = 0
	module.GhostEvents = {}
	module.Abilities = {}
	module.Flags = {
		GlassBreakCoefficient = 1.5,
	}

	return module
end

function Cases.remoteEventRouter(events, handlers)
	local connections = {}

	for name, remote in pairs(events) do
		local handler = handlers[name]
		if handler then
			connections[name] = remote.OnServerEvent:Connect(function(player, ...)
				return handler(player, ...)
			end)
		end
	end

	return function()
		for _, connection in pairs(connections) do
			connection:Disconnect()
		end
	end
end

function Cases.backpackBinder(players, callback)
	local bindings = {}

	local function bindPlayer(player)
		local backpack = player:FindFirstChildOfClass("Backpack")
		if not backpack then
			return
		end

		bindings[player] = backpack.ChildAdded:Connect(function(tool)
			if tool:IsA("Tool") then
				callback(player, tool)
			end
		end)
	end

	players.PlayerAdded:Connect(bindPlayer)
	players.PlayerRemoving:Connect(function(player)
		local connection = bindings[player]
		if connection then
			connection:Disconnect()
			bindings[player] = nil
		end
	end)

	for _, player in players:GetPlayers() do
		bindPlayer(player)
	end
end

function Cases.tweenSequence(tweenService, object, goals)
	local tweens = {}

	for index, goal in ipairs(goals) do
		local info = TweenInfo.new(goal.Duration or 0.25, goal.Style or Enum.EasingStyle.Quad)
		local tween = tweenService:Create(object, info, goal.Properties)
		tweens[index] = tween
	end

	for _, tween in ipairs(tweens) do
		tween:Play()
		tween.Completed:Wait()
	end

	return tweens
end

function Cases.collectionFilter(collection, predicate)
	local result = {}

	for _, item in ipairs(collection) do
		if predicate(item) then
			table.insert(result, item)
		end
	end

	return result
end

function Cases.raycastResult(workspaceService, origin, direction, ignore)
	local params = RaycastParams.new()
	params.FilterType = Enum.RaycastFilterType.Exclude
	params.FilterDescendantsInstances = ignore

	local result = workspaceService:Raycast(origin, direction, params)
	if not result then
		return nil, nil
	end

	return result.Instance, result.Position
end

function Cases.dataStoreRetry(dataStore, key, value)
	local tries = 0
	local saved = false
	local lastError = nil

	repeat
		tries += 1
		local ok, err = pcall(function()
			dataStore:SetAsync(key, value)
		end)
		saved = ok
		lastError = err
		if not saved then
			task.wait(tries * 0.5)
		end
	until saved or tries >= 3

	return saved, lastError
end

function Cases.humanoidState(character)
	local humanoid = character:FindFirstChildOfClass("Humanoid")
	if not humanoid then
		return "Missing"
	end

	if humanoid.Health <= 0 then
		return "Dead"
	elseif humanoid.Sit then
		return "Sitting"
	elseif humanoid.MoveDirection.Magnitude > 0 then
		return "Moving"
	end

	return "Idle"
end

function Cases.inventorySlots(items)
	local slots = {}

	for _, item in ipairs(items) do
		local rarity = item.Rarity or "Common"
		slots[item.Id] = {
			name = item.Name,
			count = item.Count or 1,
			rare = rarity ~= "Common",
		}
	end

	return slots
end

function Cases.callbackChain(source, middleware)
	return function(payload)
		local current = payload

		for _, callback in ipairs(middleware) do
			current = callback(current)
			if current == nil then
				return nil
			end
		end

		return source:Fire(current)
	end
end

function Cases.tableMergeConfig(defaults, overrides)
	local config = {}

	for key, value in pairs(defaults) do
		config[key] = value
	end

	for key, value in pairs(overrides or {}) do
		config[key] = value
	end

	config.Enabled = config.Enabled ~= false
	config.Timeout = math.clamp(config.Timeout or 10, 1, 60)

	return config
end

function Cases.questRewards(types)
	local byId = {}

	for _, questType in ipairs(types) do
		byId[questType.id] = questType
	end

	return function(id, target)
		local questType = byId[id]
		if not questType then
			return 50
		end

		local reward = questType.reward(target) * 0.5
		return math.clamp(math.floor((reward / 50) + 0.5) * 50, 50, 250)
	end
end

function Cases.guardReturns(player, round)
	if not player then
		return false, "missing player"
	end

	if not (round and round.Active) then
		return false, "round inactive"
	end

	local character = player.Character
	if not (character and character.Parent) then
		return false, "missing character"
	end

	return true, character
end

function Cases.shortCircuitOptions(options)
	local icon = (options and options.icon) or "rbxassetid://0"
	local label = (options and options.label) or "Unknown"
	local visible = options == nil or options.visible ~= false
	return icon, label, visible
end

function Cases.metatableMethods()
	local class = {}
	class.__index = class

	function class.new(name)
		local self = setmetatable({}, class)
		self.Name = name
		self.Count = 0
		return self
	end

	function class:Add(amount)
		self.Count += amount
		return self.Count
	end

	return class
end

function Cases.genericPairsIpairs(dictionary, list)
	local output = {}

	for key, value in pairs(dictionary) do
		output[key] = tostring(value)
	end

	for index, value in ipairs(list) do
		output[index] = value * 2
	end

	return output
end

function Cases.cframeMath(root, target)
	local offset = root.CFrame:ToObjectSpace(target.CFrame)
	local flat = Vector3.new(offset.Position.X, 0, offset.Position.Z)
	local angle = math.deg(math.atan2(flat.X, flat.Z))
	return offset, angle
end

function Cases.attributeSignal(instance)
	local listeners = {}

	local function updateTransparency()
		local transparency = instance:GetAttribute("Transparency") or 0
		for _, part in ipairs(instance:GetDescendants()) do
			if part:IsA("BasePart") then
				part.Transparency = transparency
			end
		end
	end

	listeners.transparency = instance:GetAttributeChangedSignal("Transparency"):Connect(updateTransparency)
	updateTransparency()
	return listeners
end

function Cases.schedulerLoop(queue)
	local running = true

	task.spawn(function()
		while running do
			local job = table.remove(queue, 1)
			if job then
				job()
			else
				task.wait(0.1)
			end
		end
	end)

	return function()
		running = false
	end
end

function Cases.dateTimeGui(label, useSystemTime)
	local now = if useSystemTime then DateTime.now() else DateTime.fromUnixTimestamp(0)
	local date = now:FormatLocalTime("LL", "en-us")
	local time = now:FormatLocalTime("LT", "en-us")
	label.Text = date .. " " .. time
	return label.Text
end

return Cases
