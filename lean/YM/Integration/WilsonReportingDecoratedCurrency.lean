import YM.Integration.WilsonReportingDecoratedSelection
import YM.Integration.WilsonRootedObservedRate

/-! The original physical root earns a vanishing prefactor at the actual
prescribed model order and before the period. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReportingDecoratedCurrency
open Function Filter Lattice RG Wilson Pressure PhysicalNext.Repeat.Legato
open PhysicalNext.JointLoad.Heir.Suite Push.PriceCompiler Supply Testing
open scoped Topology BigOperators Classical

theorem original {G:Gauge} (R:Run G) (simple:G.Simple) (q:ℕ) {ε:ℝ} (positive:0<ε) :
    ∀ᶠ m:ℕ in atTop, ∀ N per, m<N →
    let S:=R.alloy.B.a.clock.op m per
    let g:=Pert.Asymptotics.regulatorRun R.family N per (m+1)
    q ≤ S.patch.J ∧ (2*g)^((q:ℝ)+1-1/2) ≤ ε*g^q := by
  have tol:0<ε^2:=sq_pos_of_pos positive
  have deep : Tendsto R.alloy.B.a.clock.J atTop atTop:=R.family.path.levels.fits.deep
  filter_upwards [WilsonRootedObservedRate.power R simple (2*q) (2*q) le_rfl tol,
    (deep.comp (tendsto_add_atTop_nat 1)).eventually (eventually_ge_atTop q)] with m sale height N per hm S g
  have gp:0≤g:=(IterationFour.Currency.g_pos R.makes N per (m+1) hm).le
  refine ⟨?_,?_⟩
  · change q≤(R.alloy.B.a.clock.op m per).patch.J
    rw [(Testing.proceeds R.alloy.B N m per hm).atStep]
    exact height
  · have hs : 0 ≤ (2*g)^((q:ℝ)+1-1/2):=Real.rpow_nonneg (by positivity) _
    have ht : 0 ≤ ε*g^q:=mul_nonneg positive.le (pow_nonneg gp q)
    have eq : ((2*g)^((q:ℝ)+1-1/2))^2=(2*g)^(2*q+1) := by
      calc
        _ = ((2*g)^((q:ℝ)+1-1/2))^(2:ℝ) := (Real.rpow_natCast _ 2).symm
        _ = (2*g)^(((q:ℝ)+1-1/2)*2) := (Real.rpow_mul (by positivity : 0≤2*g) _ _).symm
        _ = _ := by rw [←Real.rpow_natCast]; congr 1;push_cast;ring
    have dst : (ε*g^q)^2=ε^2*g^(2*q) := by rw [mul_pow,←pow_mul,Nat.mul_comm]
    have bound := sale N per hm
    change (2*g)^(2*q+1)≤ε^2*g^(2*q) at bound
    rw [←eq,←dst] at bound
    nlinarith

end YM.Integration.WilsonReportingDecoratedCurrency
