-- /Three/Riemann.lean - 1-3-6-9-12 keeps it on balancer
def Clock := Fin 720
def onCritical (c : Clock) : Bool := c.val % 60 == 0
def balanced (c : Clock) : Bool := c.val % 3 == 0
theorem critical_balanced (c : Clock) : onCritical c = true -> balanced c = true := by simp [onCritical, balanced] at *; omega
theorem closes : 720 % 3 = 0 := rfl
