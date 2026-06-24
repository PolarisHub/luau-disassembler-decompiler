-- Exercises context-based naming: pcall tuples, field-sink, nil-check booleans,
-- Roblox method/field nouns. Compiled stripped (-g0) so names must be synthesized.
local function process(player, base, bonus)
	local ok, value = pcall(function()
		return player:GetAttribute("Coins")
	end)
	local total = base + bonus
	player.Character.Humanoid.Health = total
	local hasChar = player.Character ~= nil
	return ok, value, hasChar
end
return process
