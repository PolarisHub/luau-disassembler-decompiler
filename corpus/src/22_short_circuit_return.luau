local fallback = "rbxassetid://77554898933730"
local byId = {
    known = {
        icon = "rbxassetid://123",
    },
}

return function(id)
    local entry = byId[id]
    return (entry and entry.icon) or fallback
end
