vars: isOn, curr
init: isOn = 0 && 208/10 <= curr && curr <= 235/10
safe: 20 <= curr && curr <= 25 && curr' = curr
reach: isOn' = isOn
    && ((isOn = 1 && curr' = curr + 1 - (1/10 * (curr - 19)))
        || (!(isOn = 1) && curr' = curr - (1/10 * (curr - 19))))
