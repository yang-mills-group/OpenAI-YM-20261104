import Mathlib.Analysis.Complex.Basic

namespace YM.MS.Hem.Mell
def toll (z:ℂ)(ℓ:ℕ): ℂ:= -(2:ℂ)*z*ℓ
def vamp (z:ℂ)(h ℓ:ℕ): ℂ:= -(h:ℂ)+toll z ℓ
end YM.MS.Hem.Mell
