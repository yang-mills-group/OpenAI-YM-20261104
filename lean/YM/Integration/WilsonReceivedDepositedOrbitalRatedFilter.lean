import YM.Integration.WilsonReceivedDepositedOrbitalCofinalLift

/-! Convergence after the original reversion on boards with varying period, lifted direction, and one volume factor. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedDepositedOrbitalRatedFilter
open Filter Comparison.RG02 Comparison.RG02.Valence Comparison.RG02.Adjacent
open WilsonReceivedDepositedOrbitalCofinalLift (pulled priced)
open scoped Topology
variable {Z E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]
variable {F:Z→Type*}[∀z,NormedAddCommGroup (F z)][∀z,NormedSpace ℝ (F z)]
theorem original (l:Filter Z)(R:Z→ℂ)(L:∀ z,E→L[ℝ](F z))(U:∀z,Display (F z))(V:Display E)
    (T:UnitCost)(r d:ℕ)(height:ℕ→ℕ)(finite:∀z,Charge r (fun j=>(height j:ℤ)) (U z))
    (paid:Charge r (fun j=>(height j:ℤ)) V)(x:E)
    (hear:∀j≤r,∀a≤height j,Tendsto (fun z=>R z*U z j (L z ((a:ℝ) • x))) l (𝓝 (V j ((a:ℝ) • x)))):
    Tendsto (fun z=>R z*born (U z) T 0 r d (L z x)) l (𝓝 (born V T 0 r d x)):=by
  let S(z:Z):Display E:=pulled (R z) (L z) (U z)
  have good (z:Z):Charge r (fun j=>(height j:ℤ)) (S z):=priced (R z) (L z) r height (U z) (finite z)
  have direct:=WilsonReceivedDepositedOrbitalCofinalClock.original l T 0 r d height S V good paid x hear
  apply direct.congr'
  filter_upwards with z
  exact WilsonReceivedDepositedOrbitalCofinalLift.original (R z) (L z) (U z) T 0 r d _ (finite z) x

end YM.Integration.WilsonReceivedDepositedOrbitalRatedFilter
end
