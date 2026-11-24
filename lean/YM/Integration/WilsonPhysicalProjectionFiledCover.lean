import YM.Integration.WilsonPhysicalHistoryFieldTail
import YM.Integration.WilsonPhysicalHistoryAperture
import YM.Integration.WilsonPhysicalHistoryFormalPayoff

/-! Original landed tensor weights on the infinite cover, uniform before the observing cutoff and period. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonPhysicalProjectionFiledCover
open Function Filter Finset Lattice Laurent RG Precision Wilson FormalBulk08
open Next.Free Reef Flat Exterior Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp
open Pose Glide Bank Dawn Wine Rial Roof Dove Series Trellis Aster Borough Elm Dove.Lab
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels PowerSeries
open PhysicalNext.Repeat.Legato WilsonRunFormalMarkedStep RG16.Literal RG16.Guarding
open RG16 RG16.Literal RG16.Guarding Pert.Asymptotics Trace.Physical Next.Foundations
open MSbar Push.Uniform

open WilsonPhysicalHistoryAperture WilsonPhysicalHistoryFieldTail
open scoped Classical Topology BigOperators ENNReal
variable {G : Gauge} {d D : ℕ}


variable (R:Run G) (L:∀i,Lodge ((R.family.path.levels.clock.op i 0).patch)) (a:hue G) (depth:d<D)

theorem original (simple:G.Simple) {u:ℕ→ℕ} (grant:WilsonWindowFormalPurchase.Canonical u R.kit)
    (o:Loc G 1) (E:ℕ) (w:Letter (R.family.labels.level d)) (r:ℕ):
    ∃(B:ℝ)(m:ℕ),0≤B ∧ ∀ᶠ i:ℕ in atTop,∀N:ℕ,i≤N → ∀(f:Studio D)(e:ℕ),e≤E →
      Knoxville (fame _) (width R.family i) (0,o) (graph R L a depth N i w f e r)
        (B*(Borough.ageZ (R.family.path.levels.clock.hatBeta i))^m*‖Annex.compress D f‖):=by
  let C := R.family
  let J := d+D+E+5
  have j5 : 5≤J := by dsimp [J];omega
  have jD : D≤J := by dsimp [J];omega
  have jE : E≤J := by dsimp [J];omega
  have jd : d+3≤J := by dsimp [J];omega
  obtain ⟨K,after⟩ := eventually_atTop.mp (C.path.levels.fits.deep.eventually_ge_atTop J)
  have gate : J≤C.path.levels.clock.J (K+1) := after _ (Nat.le_succ K)
  let ann := WilsonWindowFormalAnnouncement.on_run R grant
  obtain ⟨B,m,B0,archive⟩ := Primer.landedFields C simple a L o ann j5 gate jE depth jd jD w r
  refine ⟨B,m,B0,?_⟩
  filter_upwards [eventually_ge_atTop K] with i past
  intro N cap f e he
  let Z := graph R L a depth N i w f e r
  have funded : Knoxville (fame _) (width C i) (0,o) Z
      (B*(Borough.ageZ (C.path.levels.clock.hatBeta i))^m*‖Annex.compress D f‖) := by
    dsimp only [Z]
    rw [WilsonPhysicalHistoryFieldTail.prescribed R L a depth grant]
    exact ((archive i past f e he).2.2 N cap).1
  exact funded

/-- The same receipt covers the half width needed to discard distant physical endpoints. -/
theorem width_charge (simple:G.Simple) {u:ℕ→ℕ} (grant:WilsonWindowFormalPurchase.Canonical u R.kit)
    (s m:ℕ) {B loss:ℝ} (B0:0≤B) (positive:0<loss):
    ∀ᶠ i:ℕ in atTop,∀N per:ℕ,i≤N → ∀t:ℝ,0<t → t⁻¹≤2*(width R.family i)⁻¹ →
      widthCost t s*(B*(Borough.ageZ (R.family.path.levels.clock.hatBeta i))^m)≤
        (regulatorRun R.family N per i)^(-loss):=by
  let k:ℝ:=2*((s:ℝ)+1)+1
  have k0:0≤k:=by dsimp [k];positivity
  filter_upwards [WilsonPhysicalHistoryFormalPayoff.polynomial R simple (k^s*B)
    (mul_nonneg (pow_nonneg k0 _) B0) (s+m) positive] with i paid
  intro N per hi t t0 limited
  let age:=Borough.ageZ (R.family.path.levels.clock.hatBeta i)
  let Λ:=RG16.Lambda R.family.path.levels i
  have al:age≤Λ:=WilsonPhysicalHistoryAperture.age R.family i
  have a1:1≤age:=Borough.progZ ((WilsonWindowFormalAnnouncement.on_run R grant).power.beta i)
  have Λ0:0≤Λ:=zero_le_one.trans (a1.trans al)
  have inv:t⁻¹≤2*Λ:=limited.trans (mul_le_mul_of_nonneg_left
    ((WilsonPhysicalHistoryAperture.width_paid R grant i).trans al) (by norm_num))
  have box:1+((s:ℝ)+1)*t⁻¹≤k*Λ:=by
    have x:=mul_le_mul_of_nonneg_left inv (show (0:ℝ) ≤ (s:ℝ) + 1 by positivity)
    dsimp only [k];linarith only [x,a1,al]
  have toll:widthCost t s ≤ k^s*Λ^s:=by
    rw [←mul_pow]
    apply pow_le_pow_left₀ (by positivity) _ _
    simpa [Nat.cast_add,div_eq_mul_inv] using box
  apply le_trans _ (paid N per hi)
  calc
    _ ≤ (k^s*Λ^s)*(B*Λ^m) := mul_le_mul toll
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans a1) al _) B0)
      (mul_nonneg B0 (pow_nonneg (zero_le_one.trans a1) _)) (mul_nonneg (pow_nonneg k0 _) (pow_nonneg Λ0 _))
    _ = (k^s*B)*Λ^(s+m) := by rw [pow_add];ring

end YM.Integration.WilsonPhysicalProjectionFiledCover
