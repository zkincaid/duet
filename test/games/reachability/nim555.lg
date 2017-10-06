vars: x, y, z
init: x = 5 && y = 5 && z = 5
safe:
    (0 <= x' && x' <= x - 1 && y' = y && z' = z)
    || (x' = x && 0 <= y' && y' <= y - 1 && z' = z)
    || (x' = x && y' = y && 0 <= z' && z' <= z - 1)
reach:
    (0 <= x' && x' <= x - 1 && y' = y && z' = z)
    || (x' = x && 0 <= y' && y' <= y - 1 && z' = z)
    || (x' = x && y' = y && 0 <= z' && z' <= z - 1)
