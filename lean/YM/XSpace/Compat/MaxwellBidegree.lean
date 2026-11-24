import YM.Next.MAXWELL.Algebra

/-! Restored ancestral bidegree on the existing free Maxwell slots. -/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
variable {G : Gauge}

def bwt (v : Slot G) : ℕ × ℕ := (scaleW v,1)

end YM.Maxwell.Free
end
