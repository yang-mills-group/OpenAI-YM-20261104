import YM.Integration.WilsonPhysicalHistoryFormalWindow

/-! Spend the normalized inverse products in the *physical* regulated
coupling on the same measured interval and retain the cutoff discount. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalHistoryFormalPayoff

open Filter Real Lattice Wilson RG RG16 RG16.Literal RG16.Guarding Pert.Asymptotics
open PhysicalNext.Repeat.Legato Trace.Physical Trace.Physical.GermGraph
open FormalBulk08
open Next.Free Reef Flat Exterior Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp
open Pose Glide Bank Dawn Wine Rial Roof Dove Series Trellis Aster Borough Elm Dove.Lab
open Planned.PrimaryIntegral295 Source Source.Drops Labels PowerSeries
open WilsonPhysicalExteriorMeshStops WilsonPhysicalHistoryFormalWindow
open scoped Classical Topology

variable {G : Gauge} (R : Run G)

/-- Any fixed polynomial in the *measured log clock* is purchased by an
arbitrarily small inverse power of every finite vacuum coupling at that stage. -/
theorem polynomial (simple : G.Simple) (B : ℝ) (hB : 0≤B) (m : ℕ) {η : ℝ} (hη : 0<η) :
    ∀ᶠ k : ℕ in atTop, ∀ N n, k≤N → B*(RG16.Lambda R.family.path.levels k)^m ≤
      (regulatorRun R.family N n k)^(-η) := by
  let C := R.family
  let clockL := RG16.Lambda C.path.levels
  let t := η/4
  have hp : 0<t := by dsimp [t]; positivity
  let F := (B+1)*t⁻¹^m
  have fpos : 0<F := by dsimp [F]; positivity
  have rise : Tendsto (fun k=>t*clockL k) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hp).mpr (lambda_leads C simple)
  have negligible := ((Real.isLittleO_pow_exp_atTop (n:=m)).comp_tendsto rise).bound (inv_pos.mpr fpos)
  filter_upwards [negligible,(lambda_leads C simple).eventually_ge_atTop (4*log (2*Real.exp 1))] with k hm highway N n cap
  have lpos : 0≤clockL k := (lambda_pos C _).le
  change ‖(t*clockL k)^m‖ ≤ F⁻¹*‖Real.exp (t*clockL k)‖ at hm
  rw [Real.norm_of_nonneg (pow_nonneg (mul_nonneg hp.le lpos) _),
    Real.norm_of_nonneg (exp_pos _).le] at hm
  have mastered : F*(t*clockL k)^m ≤ Real.exp (t*clockL k) := by
    simpa only [←mul_assoc,mul_inv_cancel₀ fpos.ne',one_mul] using mul_le_mul_of_nonneg_left hm fpos.le
  have rearrange : F*(t*clockL k)^m=(B+1)*(clockL k)^m := by
    dsimp [F]
    rw [mul_pow]
    calc
      _ = (B+1)*(t⁻¹*t)^m*(clockL k)^m := by rw [mul_pow]; ring
      _ = _ := by rw [inv_mul_cancel₀ hp.ne',one_pow,mul_one]
  have small : B*(clockL k)^m ≤ Real.exp (t*clockL k) := by
    rw [rearrange] at mastered
    exact (mul_le_mul_of_nonneg_right (by linarith : B≤B+1) (pow_nonneg lpos _)).trans mastered
  have gc := (g_band C R.makes (p:=n) cap).2
  have gb : regulatorRun C N n k ≤Real.exp (-(clockL k)/4) := by
    apply gc.trans
    change (2*Real.exp 1)*Real.exp ((-(1:ℝ)/2)*clockL k) ≤Real.exp (-(clockL k)/4)
    rw [←exp_log (by positivity : 0<2*Real.exp (1:ℝ)),←exp_add]
    apply exp_le_exp.mpr
    change 4*log (2*Real.exp 1) ≤ clockL k at highway
    linarith
  have g0 : 0<regulatorRun C N n k := g_pos R.makes cap
  have paid := rpow_le_rpow_of_nonpos g0 gb (neg_nonpos.mpr hη.le)
  rw [rpow_def_of_pos (exp_pos _),log_exp] at paid
  exact small.trans (by simpa only [show t*clockL k=(-(clockL k)/4)*(-η) by dsimp [t];ring] using paid)

variable {d D : ℕ} (L : ∀ i, Lodge ((R.family.path.levels.clock.op i 0).patch))
variable (a : hue G) (depth : d<D)

/-- Both finite independent inverses, and the signed finite discrepancy:
one actual coupling bill at the reporting stage, uniform in cutoff and
period and every intermediate endpoint through the genuine first crossing. -/
theorem endpoints (last : Bool) (simple : G.Simple) (slow : WilsonWindowReportingPace.Slow R.kit)
    {U : ℕ→ℕ} (grant : WilsonWindowFormalPurchase.Canonical U R.kit)
    (o : Loc G 1) {c : ℝ} (hc : c≤2) (E : ℕ) (x y : Letter (R.family.labels.level d))
    {e : ℕ} (he : e≤E) {η : ℝ} (hη : 0<η) :
    ∀ᶠ k : ℕ in atTop, ∀ j M N n, k≤j → j≤ultraviolet R.family c k → j≤M → M≤N →
      let g := regulatorRun R.family N n k
      let v := coeff e (inverseAtClock R L a depth last M k j x y)
      let w := coeff e (inverseAtClock R L a depth last N k j x y)
      |v| ≤ g^(-η) ∧ |w| ≤ g^(-η) ∧ |v-w| ≤ g^(-η)*ratioR R.family.S M j targetPower := by
  obtain ⟨K,stamped⟩ := pricedAt R L a depth last simple slow grant o hc E
  have price := stamped x y e he
  obtain ⟨B,b,B0,first⟩ := price.left
  obtain ⟨C,f,C0,second⟩ := price.right
  obtain ⟨A,⟨P,p,P0,bound⟩,positive,discount⟩ := price.blur
  filter_upwards [eventually_ge_atTop K,polynomial R simple B B0 b hη,
    polynomial R simple C C0 f hη,polynomial R simple P P0 p hη] with k past fee₁ fee₂ fee₃ j M N n kj stop paid nested
  let t : Reading R.family c K := ⟨k,j,M,N,past,kj,stop,paid,nested⟩
  have live := kj.trans (paid.trans nested)
  have cheap : A t ≤ (regulatorRun R.family N n k)^(-η) :=
    (le_abs_self _).trans ((bound t).trans (fee₃ N n live))
  exact ⟨(first t).trans (fee₁ N n live),(second t).trans (fee₂ N n live),
    (discount t).trans (mul_le_mul_of_nonneg_right cheap (ratioR_pos ..).le)⟩

theorem coefficients (simple : G.Simple) (slow : WilsonWindowReportingPace.Slow R.kit)
    {U : ℕ→ℕ} (grant : WilsonWindowFormalPurchase.Canonical U R.kit)
    (o : Loc G 1) {c : ℝ} (hc : c≤2) (E : ℕ) (x y : Letter (R.family.labels.level d))
    {e : ℕ} (he : e≤E) {η : ℝ} (hη : 0<η) :
    ∀ᶠ k : ℕ in atTop, ∀ j M N n, k≤j → j≤ultraviolet R.family c k → j≤M → M≤N →
      let g := regulatorRun R.family N n k
      let v := coeff e (inverseAt R L a depth M k j x y)
      let w := coeff e (inverseAt R L a depth N k j x y)
      |v| ≤ g^(-η) ∧ |w| ≤ g^(-η) ∧ |v-w| ≤ g^(-η)*ratioR R.family.S M j targetPower := by
  simpa only [inverseAtClock,Bool.false_eq_true,if_false,inverseAt] using
    endpoints R L a depth false simple slow grant o hc E x y he hη

/-- For a fixed perturbative order one physical gate works for every mark,
every surviving coefficient, and both endpoint clocks. -/
theorem simultaneous (simple : G.Simple) (slow : WilsonWindowReportingPace.Slow R.kit)
    {U : ℕ→ℕ} (grant : WilsonWindowFormalPurchase.Canonical U R.kit)
    (o : Loc G 1) {c : ℝ} (hc : c≤2) (E : ℕ) {η : ℝ} (hη : 0<η) :
    ∀ᶠ k : ℕ in atTop, ∀ (last : Bool) (x y : Letter (R.family.labels.level d)) (e : Fin (E+1)),
      ∀ j M N n, k≤j → j≤ultraviolet R.family c k → j≤M → M≤N →
      let g := regulatorRun R.family N n k
      let v := coeff e.val (inverseAtClock R L a depth last M k j x y)
      let w := coeff e.val (inverseAtClock R L a depth last N k j x y)
      |v| ≤ g^(-η) ∧ |w| ≤ g^(-η) ∧ |v-w| ≤ g^(-η)*ratioR R.family.S M j targetPower := by
  exact eventually_all.mpr fun last=> eventually_all.mpr fun x=> eventually_all.mpr fun y=>
    eventually_all.mpr fun e=> endpoints R L a depth last simple slow grant o hc E x y
      (Nat.le_of_lt_succ e.isLt) hη

end YM.Integration.WilsonPhysicalHistoryFormalPayoff

