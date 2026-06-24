-- Sibling closures created with NEWCLOSURE in the same parent, each capturing a
-- different upvalue, plus a chained capture (an inner closure reading an outer
-- closure's upvalue). Exercises mapping NEWCLOSURE's D operand through the parent's
-- child-proto list and resolving upvalue names across two levels.
local function counters(name)
	local hits = 0
	local function bump()
		hits = hits + 1
		local function describe()
			return name .. ": " .. hits
		end
		return describe()
	end
	local function reset()
		hits = 0
		return hits
	end
	return bump, reset
end

return counters
