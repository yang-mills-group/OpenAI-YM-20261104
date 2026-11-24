import YM.Integration.WilsonConditionalTaylorThermalNextProduct

/-! First interacting variation of a graded field on the authentic
multiscale Wilson chart. The same cubic phase and Haar Jacobian enter the
source column and its unmarked denominator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorThermalInteraction
open Function Filter MeasureTheory Lattice RG Tree Wilson Precision Push.BetaTransport
open RGComparison.Core16 RGComparison.Core16.Descent
open PertExtension PertExtension.Series Tested Radial GaussianScore
open WilsonConditionalTaylorThermalLaplace
open scoped Topology ContDiff Classical BigOperators
variable {G : Gauge} {n c : Side} {d : Descent n c}
local notation "E" => Coordinates G d

def haar (P : ChartRatio G) (d : Descent n c) (x : Coordinates G d) :=
  Chart.jacobian P x * (Fintype.card d.Tags:ℝ)⁻¹

def interaction (P : ChartRatio G) (t : d.Tags) (x : E) :=
  jet (haar P d) 1 x / density d P - jet (d.phase G t) 3 x

def nextVertex (t : d.Tags) (v : ℕ → ℝ) :=
  jet (WilsonConditionalTaylorThermalWeight.account (G:=G) t v ∘ d.tablePath) 3

theorem density_pos (P : ChartRatio G) (R : LocalRatio P) (d : Descent n c) : 0 < density d P := by
  have ht : 0 < Chart.jacobian P (U:=d.Links) 0 := Finset.prod_pos fun i _ =>
    show 0 < Chart.fee P 0 from lt_max_of_lt_left (by rw [R.anchored,mul_one]; exact R.scale)
  exact mul_pos ht (inv_pos.mpr (Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr inferInstance)))

theorem tag (ok : d.OK G) (P : ChartRatio G) (t s : d.Tags) (v : ℕ → ℝ) :
    interaction P t = interaction P s ∧ nextVertex (G:=G) t v = nextVertex s v := by
  constructor
  · funext x; unfold interaction; rw [phase_jet ok t s]
  · have h := branch_independent (v := fun x : E => x) (Bg := fun _ => 0) ok contDiffAt_id rfl t s v
    simp only [link_one] at h
    funext x
    unfold nextVertex jet WilsonConditionalTaylorThermalWeight.account
    simp only [Function.comp_def]
    rw [(h.iteratedFDeriv ℝ 3).eq_of_nhds]

private theorem firstExp (φ : E→ℝ) (x : E) : expsum (layers φ) 1 1 x = -jet φ 3 x := by
  have two : Finset.antidiagonal 1 = {(0,1),(1,0)} := by decide
  simp [expsum,Finset.sum_range_succ,Zone.TaylorPow,Zone.mul,two,Radial.layers]

theorem angular (P : ChartRatio G) (R : LocalRatio P) (room : d.Room G) (t : d.Tags)
    {Y : Fields G d→ℝ} (smooth : d.SmoothAtFlat Y) {w : ℕ} (grade : RadialOrder w (Y ∘ d.tablePath))
    (x : E) :
    integrandSeries (d.phase G t) (nearFee P t Y) (w+1) x =
      density d P * (jet (Y ∘ d.tablePath) (w+1) x + jet (Y ∘ d.tablePath) w x * interaction P t x) := by
  let J := haar P d
  let F := Y ∘ d.tablePath
  have sj : ContDiffAt ℝ ∞ J 0 := ((Chart.Ratio.jacobian_smooth R).of_le le_top).mul contDiffAt_const
  have eq : nearFee P t Y =ᶠ[𝓝 0] J*F := by
    filter_upwards [prob_flat_tangent (room_ok d room) t] with z hz
    change Chart.jacobian P z * d.probability t (d.tablePath z) * _ = _
    rw [hz]
    rfl
  have same (k) : jet (nearFee P t Y) k x = jet (J*F) k x := by
    unfold jet; rw [(eq.iteratedFDeriv ℝ k).eq_of_nhds]
  have zeroJ : RadialOrder 0 J := fun y => (directions sj y).bounded
  have common : RadialOrder w (J*F) := fun y => by
    simpa only [Nat.zero_add] using! bill_mul (zeroJ y) (grade y)
  have next := WilsonConditionalTaylorThermalNextProduct.jets sj smooth zeroJ grade x
  have head := head_product sj smooth zeroJ grade x
  simp only [Nat.zero_add,jet_zero] at next head
  have j0 : J 0 = density d P := rfl
  have c := WilsonConditionalTaylorThermalNextProduct.convolution
    (A:=fun j => jet (J*F) j x) (B:=fun j => expsum (layers (d.phase G t)) j j x)
    (a:=w) (b:=0) (fun _ hw => congrFun (jets_vanish (sj.mul smooth) common hw) x)
    (fun _ hw => by omega)
  unfold integrandSeries Zone.mul
  simp_rw [same]
  simp only [Nat.add_zero] at c
  rw [c,firstExp,show expsum (layers (d.phase G t)) 0 0 x=1 by simp [expsum,Zone.TaylorPow],
    mul_one,head,next,j0]
  unfold interaction
  dsimp only [J,F]
  field_simp [(density_pos P R d).ne']
  ring

end YM.Integration.WilsonConditionalTaylorThermalInteraction
