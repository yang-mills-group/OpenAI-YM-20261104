import YM.GradedFar.Pose.Calibrate
import YM.GradedFar.Continuation.WaveResult

/-!
# The field maps in the fixed sup-norm basis
-/
namespace YM.FVA2.GradedFar.Growth
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Scale Dframe Jury
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n d : ℕ} (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
local notation "ν"=> Teller.logNu 1
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=> gYM G
open Continuation

abbrev RowSpace (G : Gauge) (d : ℕ) := Toon G d→ℂ
def chair (G : Gauge) (d : ℕ) : Sec G d≃ₗ[ℂ] RowSpace G d := (Theater.Daylight (Press.portDeck G) d).equivFun
lemma fee_elt (x : Sec G d) (b : Toon G d) : chair G d x b = coord b x := rfl
lemma chair_ball (x : Sec G d) {r : ℝ} (hr : 0≤r) : Ball r x ↔ ‖chair G d x‖ ≤ r := (pi_norm_le_iff_of_nonneg hr).symm
abbrev Maps (G : Gauge) (d : ℕ) := RowSpace G d →L[ℂ] RowSpace G d
def chairs (G : Gauge) (d : ℕ) : (Module.End ℂ (Sec G d)) ≃ₗ[ℂ] Maps G d :=
  (((chair G d).conj)).trans LinearMap.toContinuousLinearMap
lemma appointed (A : Module.End ℂ (Sec G d)) (u : Sec G d) : chairs G d A (chair G d u)=chair G d (A u) := by
  change chair G d (A ((chair G d).symm (chair G d u)))=_; rw [LinearEquiv.symm_apply_apply]
@[simp] lemma chairs_mul (A B : Module.End ℂ (Sec G d)) : chairs G d (A*B) = chairs G d A * chairs G d B := by
  ext1 u; obtain ⟨u,rfl⟩:= (chair G d).surjective u
  change _=chairs G d A (chairs G d B (chair G d u)); rw [appointed, appointed, appointed]; rfl
@[simp] lemma chairs_one : chairs G d 1=1 := by ext1 u; obtain ⟨u,rfl⟩:=(chair G d).surjective u; rw [appointed]; rfl

abbrev engine (G : Gauge) (d : ℕ) (s : ℝ) := chairs G d (Level.Dial d (-s)) -- s now log T
lemma engine_amount (x : RowSpace G d) (b : Toon G d) (s : ℝ) : engine G d s x b = (exp s:ℂ)^b.size*x b := by
  obtain ⟨u,rfl⟩:= (chair G d).surjective x; rw [engine,appointed,fee_elt,Dial_coord,length_power,fee_elt]
lemma engine_pos_bound (s : ℝ) (h : 0 ≤ s) (d : ℕ) : ‖engine G d s‖ ≤ (exp s)^d := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity); intro x; refine (pi_norm_le_iff_of_nonneg (by positivity)).2 ?_
  intro i; rw [engine_amount,norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg (exp_pos _|>.le)]
  exact mul_le_mul (pow_le_pow_right₀ (Real.one_le_exp h) (size_le i)) (norm_le_pi_norm ..) (norm_nonneg _) (by positivity)
lemma engine_neg_bound (s : ℝ) (h : s ≤ 0) (d : ℕ) : ‖engine G d s‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro x; refine (pi_norm_le_iff_of_nonneg (by positivity)).2 ?_
  intro i; rw [engine_amount,norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg (exp_pos _|>.le)]
  exact mul_le_mul (pow_le_one₀ (exp_pos _|>.le) (Real.exp_le_one_iff.mpr h)) (norm_le_pi_norm ..) (norm_nonneg _) zero_le_one
@[simp] lemma engine_zero : engine G d 0=1 := by rw [engine, neg_zero, Level.flat, chairs_one]
lemma engine_sum (s t : ℝ) : engine G d (s+t)=engine G d s*engine G d t := by
  unfold engine; rw [neg_add, ← Level.group, chairs_mul]

section columns
open MS.Book.Program
local notation "ψ"=> GroupS.ψ N.criterion M ν
local notation "B"=> GroupS.gaugeN N.scheme N.criterion M ν
lemma Dial_comm (s : ℝ) (K : Guard G d) (h : Scale.Native K) :
    PowerSeries.C (Level.Dial d s) * K = K * PowerSeries.C (Level.Dial d s) := by
  ext1 i; rw [coeff_C_mul,coeff_mul_C,Level.rise _ _ (h i)]
lemma step_constant (x : PowerSeries ℂ) (A : FieldEnd G d) : Reg.Point.stepV x (C A)= C A := by
  ext1 i; rw [Reg.Point.stepV,coeff_mk,rules,Finset.sum_eq_single 0]
  · by_cases hi:i=0
    · subst i; simp [cut]
    rw [coeff_C_of_ne_zero hi,coeff_zero_C]; simp [cut,hi]
  · intro b hb hv; rw [coeff_C_of_ne_zero hv,smul_zero]
  simp
variable {simple : G.Simple} {A : Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
include H
lemma tendsK (s : ℝ) : Tangent (ψ (-s)) := (H.dilation ν).check.led _
lemma Lclock (s t : ℝ) : ψ (-(s+t))=(ψ (-t)).subst (ψ (-s)) := by
  rw [neg_add]; exact ((H.dilation ν).check.toTouched.additive _ _).1
lemma zero_clock : ψ 0=X := (H.dilation ν).check.toTouched.ground.1
lemma Lframe (s t : ℝ) : Kseries N M d (-(s+t))=
    Kseries N M d (-s) * Reg.Point.stepV (ψ (-s)) (Kseries N M d (-t)) := by
  have he := ((H.dilation ν).check.toTouched.additive (-s) (-t)).2 d
  rw [old_g _ _ ((H.dilation ν).check.ready _ _)] at he
  unfold Kseries; rw [Frame.step_mul _ _ _ (tendsK N M H s).start, step_constant, neg_add, he,← Level.group,map_mul]
  have hp := Dial_comm (-t) (B (-s) d) ((H.dilation ν).check.ready _ d)
  rw [mul_assoc (C (Level.Dial d (-s))) (B (-s) d), ← mul_assoc (B (-s) d) _ _, ← hp]; simp [mul_assoc]
lemma zero_frame (d : ℕ) : Kseries N M d 0=1 := by rw [Kseries,(H.dilation ν).check.toTouched.ground.2 d, Level.flat,map_one,one_mul]
end columns
end
end YM.FVA2.GradedFar.Growth
