import YangMills.FreeFields

/-! Types shared by the all-orders statement and the numerical perturbative
reference. The reference used by the challenge is fixed in MSMatchingTarget. -/
set_option autoImplicit false
namespace YangMills.MSbar

structure Coefficients {g : GaugeGroup} (B : Maxwell.Reference g) where
  correlation (n k : ℕ) (a : Fin n → Σ d, B.sector d) (x : Points n) : ℂ
  ope (n h k : ℕ) (a : Fin n → Σ d, B.sector d) (x : Points n) : B.sector h

end YangMills.MSbar
