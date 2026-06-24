-- Roblox idioms, to exercise name-derivation heuristics on stripped bytecode.
local Players = game:GetService("Players")
local replicated = game:GetService("ReplicatedStorage")
local mod = require(game.ReplicatedStorage.MyModule)
local fn = require(game.ReplicatedStorage.MyModule).doThing
local part = Instance.new("Part")
local character = Players.LocalPlayer.Character
local childCount = #workspace:GetChildren()
return Players, replicated, mod, fn, part, character, childCount
