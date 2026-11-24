import YM.Integration.FVA1Physical.Wilson.OrbitLaw
import YM.Integration.FVA1Physical.Wilson.PureForest

/-! Independent interior orbit weights. Only the formal action, measured coupling,
blocking noise, and actual stationary coordinates enter the new density. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter MeasureTheory Set Finset Lattice RG YM.Wilson Tree Precision Exterior RGComparison.Core16 Metric
open MSbar MSbar.Lis MSbar.Whisk MSbar.Rolling MSbar.Midpoint MSbar.Wave MSbar.Bakery MSbar.Cacao Comparison.RG02 Push Push.Uniform
open MSbar.Heath MSbar.Heath.Cottage MSbar.Bulk SectorNext.Vacuum
open scoped Classical Topology
variable {G : Gauge} {c f : Side} {Q : StepData c f} {R : Rep G f} {out : Rep G c}

def interiorEnergy (Q : StepData c f) (V : Config G c) (v : Q.Choices)
    (copy : Config G f → Config G f) (β g : ℝ) (B : Positions (Primary f G) → ℝ)
    (U : Config G f) : ℝ := B (chartLog g (copy U))-β*noiseTaylor Q V (copy U) v

variable (W : ForestCell Q R out)
local notation "V" => represent (tint G (Exterior.Body 1 c) W.x)
local notation "A" => hotel W.F W.X W.Y W.J V W.center W.a W.b
local notation "copy" => chambers W.F W.Y W.J V W.center
local notation "I" => board W.F W.X
local notation "T" => rental W.F W.J R W.Y W.source V W.center

lemma interiorEnergy_meas {σ C δ Λ w g : ℝ} (law : R.Lawful σ C Λ δ w)
    (actual : Envelope T) (B : Positions (Primary f G) → ℝ) (mB : Measurable B) :
    Measurable (interiorEnergy Q V W.source copy R.beta g B) := by
  have mc := (informed W.F W.X W.Y W.J V W.center W.voice W.posture.extendsX).1
  have id : interiorEnergy Q V W.source copy R.beta g B =
      fun U=> B (chartLog g (copy U))-R.exponent (copy U)+T U := by
    funext U; unfold interiorEnergy rental; ring
  rw [id]
  exact ((mB.comp ((chartLog_meas g).comp mc)).sub ((R.exponentEnv law).meas.comp mc)).add actual.meas

lemma interiorEnergy_osc (pos : ∀ U,0 < R.eval U) {g w ε : ℝ} (hg : 0 < g) (hw : 0 < w) (hε : 0 ≤ ε)
    (fit : W.Fits g w) (B : Positions (Primary f G) → ℝ)
    (rows : ∀ z u : Positions (Primary f G),
      (∀ t∈Set.Icc (0:ℝ) 1,z+t • u∈closedBall 0 w) →
      |(Real.log (R.eval (palace (g • (z+u)))) - B (z+u)) -
       (Real.log (R.eval (palace (g • z)))-B z)|≤(∑ j,|u j|)*(ε/w))
    (U : Config G f) (hu : U∈A) (t : IV W.F I G) (ht : twirl W.F I t U∈A) :
    let P := interiorEnergy Q V W.source copy R.beta g B
    let U' := twirl W.F I t U
    |(T U'-P U')-(T U-P U)| ≤ motionCost G W.X w*(ε/w) := by
  intro P U'
  have reg (Z : Config G f) (hZ : Z∈A) : copy Z∈regularInputs g w :=
    chord_to_regular W.voice hg hw.le fit.1 fit.2.1 fit.2.2 (copy Z)
      (fun e=> hotel_chord W.voice W.posture hZ e)
  let z := chartLog g (copy U)
  let x := chartLog g (copy U')
  have rU := reg U hu
  have rV := reg U' ht
  have segment (a : ℝ) (ha : a∈Set.Icc 0 1) : x+a • (z-x)∈closedBall 0 w := by
    have e := convex_closedBall (0:Positions (Primary f G)) w (mem_closedBall_zero_iff.mpr rV.2)
      (mem_closedBall_zero_iff.mpr rU.2) (sub_nonneg.mpr ha.2) ha.1 (sub_add_cancel 1 a)
    rw [show x+a • (z-x)=(1-a) • x+a • z by rw [sub_smul,one_smul,smul_sub];abel]
    exact e
  have paid := rows x (z-x) segment
  have ce (Z : Config G f) (hZ : Z∈A) : Real.log (R.eval (copy Z))=R.exponent (copy Z) := by
    rw [log_eval R pos,Activities.gas_one _ _ (Posture.pose W.voice W.posture hZ).2.2.2.1,Real.log_one,add_zero]
  rw [show x+(z-x)=z by abel,recover_chartLog hg.ne' _ (Set.mem_univ_pi.mp rU.1),
    recover_chartLog hg.ne' _ (Set.mem_univ_pi.mp rV.1),ce U hu,ce U' ht] at paid
  have moved := (Posture.planT W.voice W.posture t hu ht).2.old
  have span := spine_coordinates moved g w rU.2 rV.2
  have id (Z : Config G f) : T Z-P Z=R.exponent (copy Z)-B (chartLog g (copy Z)) := by
    dsimp only [P,interiorEnergy,rental]; ring
  rw [id,id,abs_sub_comm]
  exact paid.trans (mul_le_mul_of_nonneg_right span (div_nonneg hε hw.le))

/-- At any admitted exterior the complete interior law on the forest is computed
by the Wilson bank. The estimate is uniform over *all* bounded signed measurable
tests of the inner field. No physical density or physical partition function
appears in the independent inner weight or its angular denominator. -/
theorem interior_orbit_price {σ C δ Λ b g w ε : ℝ} (law : R.Lawful σ C Λ δ b)
    (branch : Q.patch.Branches Q.kernel G) (dec : WilsonStartup.Decent R.clip R.p)
    (beta : 0 ≤ R.beta) (pos : ∀ U,0 < R.eval U) (hg : 0 < g) (hw : 0 < w) (hε : 0 ≤ ε)
    (fit : W.Fits g w) (B : Positions (Primary f G) → ℝ) (bcont : Continuous B)
    (rows : ∀ z u : Positions (Primary f G),
      (∀ t∈Set.Icc (0:ℝ) 1,z+t • u∈closedBall 0 w) →
      |(Real.log (R.eval (palace (g • (z+u)))) - B (z+u)) -
       (Real.log (R.eval (palace (g • z)))-B z)|≤(∑ j,|u j|)*(ε/w))
    (φ : Config G f→ℝ) (meas : Measurable φ) {H : ℝ} (hH : 0 ≤ H) (bound : ∀ U,|φ U| ≤ H)
    (U : Config G f) :
    let P := interiorEnergy Q V W.source copy R.beta g B
    let r := woolModel W.F W.X W.J R W.Y W.source V W.center W.a W.b
    |Rota.resample W.F I r A φ U-angularLaw W.F I A P φ U| ≤
      (Real.exp (2*(motionCost G W.X w*(ε/w)))-1)*H := by
  intro P r
  have model := Posture.buy W.source W.grant W.voice W.posture law branch dec beta
  have area : MeasurableSet A := (garden_main W.F W.X W.Y W.J V W.center W.voice W.posture.extendsX).from_here
  have rp : Rota.resample W.F I r A φ=angularLaw W.F I A T φ := resample_normalized W.F I A T φ
  rw [rp]
  exact angular_tilt W.F I A area model.currency (interiorEnergy_meas W law model.currency B bcont.measurable) meas hH
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg zero_le_two hw.le)) (div_nonneg hε hw.le))
    bound (interiorEnergy_osc W pos hg hw hε fit B rows) U
end YM.Integration.FVA1Physical.Wilson
