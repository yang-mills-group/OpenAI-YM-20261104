import YM.OPE.Frame.Sampling
/-!
# Retractions from invariant sampling
-/
set_option autoImplicit false
noncomputable section

open MeasureTheory Function Filter Set
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
namespace YM.OPE.Frame
open Table
open MultipleContact (Detector)
local notation "ν" => normalizedRotations
variable {G : Gauge} {L : Register G} {S : Table L}
    {P : DiffPlan S} {X : Rotation S} (H : S.Hierarchy) (hX : X.Laws P H.spin) (ho : X.Oriented S)
    {I J : Type} [Fintype I] [Fintype J] {x : I → E4} {o : E4} {d m k : ℕ}
    (D : Detector S d)

variable (S)
private lemma front_by_side {e : Exterior L} (v : S.Field k) {o : E4} {K : Ortho} {b : Bool}
    (h : S.Hierarchy) : inspect X h.spin e b (sole o) (sole ⟨k,v⟩) o K = insertField S S o (escorts e o K) (counted X h.spin e b K) k v := (inserted _ v h.laws.toSymmetric (fun _=>le_rfl) (escorts_head ..)).symm
variable {S}
include hX

def measureOne (b : Bool) (k : ℕ) : S.Field k →ₗ[ℂ] S.Field d where
  toFun v := investigate X H.spin D b (sole 0) (sole (⟨k,v⟩ : S.Tag)) 0
  map_add' v w := by
    unfold investigate; rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun e _ => ?_
    rw [← MeasureTheory.integral_add (inspect_live X H.spin hX H (fun K=>escorts_head e.val 0 K)) (inspect_live X H.spin hX H (fun K=>escorts_head e.val 0 K))]
    apply integral_congr_ae (Eventually.of_forall (fun K=> ?_)); simp_rw [front_by_side _ _ H,map_add,add_smul]
  map_smul' c v := by
    change _ = c • _
    unfold investigate; rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun e _ => ?_
    rw [← MeasureTheory.integral_smul]; apply integral_congr_ae (Eventually.of_forall (fun K=> ?_))
    simp_rw [front_by_side _ _ H,map_smul,smul_assoc]

def notch (k : ℕ) : S.Field k →ₗ[ℂ] S.Field d := (1/2 : ℂ) • (measureOne H hX D false k + measureOne H hX D true k)
lemma realized (o : E4) (v : S.Field m) : notch H hX D m v = assess X H.spin D (sole o) (sole ⟨m,v⟩) o := by
  change assess X H.spin D (sole 0) (sole (⟨m,v⟩ : S.Tag)) 0 = _
  rw [← assess_shift X H.spin H _ o (show admissible D (sole 0) 0 from fun e K => escorts_head e.val 0 K),zero_add]
  simp only [sole,zero_add]; rfl
lemma notch_rises (hr : P.Inclusions S) (a : m ≤ k) (v : S.Field m) : notch H hX D k (P.rise a v) = notch H hX D m v := by
  have ht (b : Bool) : measureOne H hX D b k (P.rise a v)=measureOne H hX D b m v := by
    change investigate .. = investigate ..
    unfold investigate; refine Finset.sum_congr rfl fun e _ => ?_; apply integral_congr_ae (Eventually.of_forall (fun K=>?_))
    rw [front_by_side _ _ H,front_by_side _ _ H, insert_hold _ _ H.laws.toSymmetric (fun _=>le_rfl) hr a (escorts_head ..)]
  simp only [notch,LinearMap.smul_apply,LinearMap.add_apply,ht]
lemma notch_real (v : S.Field m) : notch H hX D m (S.conj H.spin m v) = S.conj H.spin d (notch H hX D m v) :=
  assess_conj X H.spin hX H (sole (⟨m,v⟩ : S.Tag)) (show admissible D (sole 0) 0 from fun e K=> escorts_head e.val 0 K)

include ho
lemma notch_act (v : S.Field m) (K : Ortho) : notch H hX D m (X.act m K v) = X.act d K (notch H hX D m v) := by
  have hv := assess_spin X H.spin hX H ho (sole (⟨m,v⟩ : S.Tag)) K (show admissible D (sole 0) 0 from fun e K=> escorts_head e.val 0 K)
  rw [show Ortho.move K ∘ sole 0 = sole 0 from funext fun _=>move_of_zero K,move_of_zero] at hv
  exact hv

private lemma raw_left (v : S.Field d) : measureOne H hX D false d v = v := by
  have hv (x : D.probes → ℂ) : (∑ e : D.probes, x e • answerAt D e) = D.decode x := by
    unfold answerAt; simp_rw [← map_smul]; rw [← map_sum]; congr 1
    ext1 j; simp only [Finset.sum_apply,Pi.smul_apply,Pi.single_apply,smul_eq_mul,mul_ite,mul_zero,mul_one]
    simp
  have he (K : Ortho) (e : D.probes) : inspect X H.spin e false (sole 0) (sole ⟨d,v⟩) 0 K =
        MultipleContact.response S d e (X.act d K⁻¹ v) := by
    let A := fun i : Fin e.val.n=> S.classTokens (e.val.letter i)
    let p : Unit → S.Tag := sole ⟨d,X.act d K⁻¹ v⟩
    have hh (i : Fin e.val.n) : counted X H.spin e.val false K i = X.label K (A i) := rfl
    have hu : X.label K ∘ p = sole (⟨d,v⟩ : S.Tag) := by
      funext _; change Sigma.mk d (X.act d K (X.act d K⁻¹ v)) = Sigma.mk d v
      rw [← hX.group,mul_inv_cancel,hX.fixes]
    rw [← insert_detect _ _ H, inserted _ _ H.laws.toSymmetric (fun _=>le_rfl) (bearing_clear _), inspect, ← hu, show counted X H.spin e.val false K = X.label K ∘ A from funext hh,
      show beside (sole 0) (escorts e.val 0 K) = Ortho.move K ∘ beside (sole (0:E4)) (bearing e.val) from by
        rw [beside_commutes]; congr 1; exact funext fun _=> (move_of_zero K).symm; exact funext fun _=> add_zero _, ← beside_commutes]
    exact same_spin _ _ ho (bearing_clear _)
  have hp (K : Ortho) : (∑ e : D.probes, inspect X H.spin e false (sole 0) (sole ⟨d,v⟩) 0 K • rotatedAnswer X H.spin D e false K) = v := by
    simp_rw [he,rotatedAnswer, mirrorVector,Bool.false_eq_true,if_false, ← map_smul]; rw [← map_sum,hv (fun e=> MultipleContact.response S d e.val (X.act d K⁻¹ v)),D.fixes, ← hX.group,mul_inv_cancel,hX.fixes]
  change investigate X H.spin D false _ _ _ = _
  unfold investigate; rw [← integral_finsetSum]; simp_rw [hp]; simp
  intro e _; exact inspect_live X H.spin hX H (fun K=>escorts_head e.val 0 K)

lemma notch_complete (v : S.Field d) : notch H hX D d v = v := by
  have hp : measureOne H hX D true d v=v := by
    have hh : bar H.spin ∘ sole (⟨d,S.conj H.spin d v⟩ : S.Tag)=sole (⟨d,v⟩ : S.Tag) :=
      funext fun i => congrArg (fun a=> (⟨d,a⟩ : S.Tag)) (S.reflect_star H.spin d v)
    have he := looks_conj X H.spin hX H (b:=false) (show admissible D (sole 0) 0 from fun e K=>escorts_head e.val 0 K) (A := sole (⟨d,S.conj H.spin d v⟩ : S.Tag)) -- ordering
    rw [hh] at he; change measureOne H hX D true d v = S.conj H.spin _ (measureOne H hX D false d _) at he
    rw [raw_left H hX ho, S.reflect_star] at he; exact he
  rw [notch,LinearMap.smul_apply,LinearMap.add_apply,hp,raw_left H hX ho]
  rw [← two_smul ℂ v,smul_smul, div_mul_cancel₀ _ (by norm_num),one_smul]
end YM.OPE.Frame
