import YM.Integration.WilsonConditionalTaylorThermalSecondProduct
import YM.Integration.WilsonConditionalTaylorThermalInteraction

/-! The quartic Wilson phase, the square of its cubic phase, and both
derivatives of the genuine Haar Jacobian on the entire tagged descent. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorThermalFourthActivity
open Function Filter MeasureTheory Lattice RG Tree Wilson Precision Push.BetaTransport
open RGComparison.Core16 RGComparison.Core16.Descent PertExtension PertExtension.Series Tested Radial GaussianScore
open WilsonConditionalTaylorThermalLaplace WilsonConditionalTaylorThermalInteraction
open scoped Classical BigOperators ContDiff Topology
variable {G : Gauge} {n c : Side} {d : Descent n c}
local notation "E" => Coordinates G d

def second (P : ChartRatio G) (t : d.Tags) (x : E) :=
  jet (haar P d) 2 x/density d P-jet (haar P d) 1 x/density d P*jet (d.phase G t) 3 x-
    jet (d.phase G t) 4 x+(jet (d.phase G t) 3 x)^2/2

private theorem phases (φ : E→ℝ) (x : E) :
    expsum (layers φ) 1 1 x = -jet φ 3 x ∧ expsum (layers φ) 2 2 x = (jet φ 3 x)^2/2-jet φ 4 x := by
  have one : Finset.antidiagonal 1 = {(0,1),(1,0)} := by decide
  have two : Finset.antidiagonal 2 = {(0,2),(1,1),(2,0)} := by decide
  constructor
  · simp [expsum,Finset.sum_range_succ,Zone.TaylorPow,Zone.mul,one,Radial.layers]
  · simp [expsum,Finset.sum_range_succ,Zone.TaylorPow,Zone.mul,one,two,Radial.layers,Nat.factorial];ring

theorem angular (P : ChartRatio G) (R : LocalRatio P) (room : d.Room G) (t : d.Tags)
    {Y : Fields G d→ℝ} (smooth : d.SmoothAtFlat Y) {w : ℕ} (grade : RadialOrder w (Y ∘ d.tablePath)) (x : E) :
    let F := Y ∘ d.tablePath
    integrandSeries (d.phase G t) (nearFee P t Y) (w+2) x =
      density d P*(jet F (w+2) x+jet F (w+1) x*interaction P t x+jet F w x*second P t x) := by
  intro F
  let J := haar P d
  have sj : ContDiffAt ℝ ∞ J 0 := ((Chart.Ratio.jacobian_smooth R).of_le le_top).mul contDiffAt_const
  have eq : nearFee P t Y =ᶠ[𝓝 0] J*F := by
    filter_upwards [prob_flat_tangent (room_ok d room) t] with z hz
    change Chart.jacobian P z * d.probability t (d.tablePath z) * _ = _
    rw [hz];rfl
  have same (k) : jet (nearFee P t Y) k x = jet (J*F) k x := by
    unfold jet;rw [(eq.iteratedFDeriv ℝ k).eq_of_nhds]
  have zeroJ : RadialOrder 0 J := fun y => (directions sj y).bounded
  have common : RadialOrder w (J*F) := fun y => by
    simpa only [Nat.zero_add] using! bill_mul (zeroJ y) (grade y)
  have head := head_product sj smooth zeroJ grade x
  have cut1 := WilsonConditionalTaylorThermalNextProduct.jets sj smooth zeroJ grade x
  have cut2 := WilsonConditionalTaylorThermalSecondProduct.jets sj smooth zeroJ grade x
  have pot := phases (d.phase G t) x
  have c := WilsonConditionalTaylorThermalSecondProduct.convolution
    (A:=fun j=>jet (J*F) j x) (B:=fun j=>expsum (layers (d.phase G t)) j j x)
    (a:=w) (b:=0) (fun j hj=>congrFun (jets_vanish (sj.mul smooth) common hj) x) (fun j hj=>by omega)
  simp only [Nat.zero_add,jet_zero] at head cut1 cut2
  simp only [Nat.add_zero] at c
  unfold integrandSeries Zone.mul
  simp_rw [same]
  rw [c,pot.1,pot.2,show expsum (layers (d.phase G t)) 0 0 x=1 by simp [expsum,Zone.TaylorPow],
    head,cut1,cut2,show J 0=density d P by rfl]
  unfold interaction second
  dsimp only [J]
  field_simp [(density_pos P R d).ne'];ring

end YM.Integration.WilsonConditionalTaylorThermalFourthActivity
