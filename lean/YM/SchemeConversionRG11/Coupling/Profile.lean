import YM.Pert.Triangle.End

/-! Factorization of the actual finite diagnosis test. This lets the coupling readout be on the
connected correlation, not using a full three-point at some orders and a connected three-point
at others. -/

set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.Coupling

open Pert.Triangle Set Function MeasureTheory
open scoped Topology ContDiff BigOperators

-- Incorporate `stamp` simply in the outer field's profile.
private def number : Fin 3 → ℝ := ![conventionRadius,12,0]
private def buoy (i : Fin 3) : ℝ := if i = 0 then stamp else 1

def petal (i : Fin 3) (x : E4) : ℂ := ↑(buoy i * bellM (‖x‖^2-(number i)^2))

theorem trio (x : Points 3) : (∏ i : Fin 3, petal i (x i)) = profileChoice x := by
  change _ = (↑(stamp * candid conventionRadius x) : ℂ)
  simp only [Fin.prod_univ_three, petal, candid, ← Complex.ofReal_mul]; unfold buoy number
  simp [mul_assoc]

private lemma gap {i j : Fin 3} (h : i ≠ j) : |(number i)^2-(number j)^2| > 2 := by
  have hr := conventionSeparate
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals norm_num [number] <;> first | nlinarith [hr] | (by_contra hk; simp only [not_lt, abs_le] at hk; nlinarith [hk.1,hk.2])

private lemma petal_bound {i : Fin 3} {x : E4} (h : petal i x ≠ 0) :
    |‖x‖^2 - (number i)^2| ≤ 1 := by
  apply le_of_lt
  apply markM
  intro he; apply h; unfold petal; rw [he,mul_zero,Complex.ofReal_zero]

section Group
variable {m : ℕ} (e : Fin m → Fin 3)

def word (p : Points m) : ℂ := ∏ i, petal (e i) (p i)
private def bounds : Set (Points m) := ⋂ i : Fin m, {z | |‖z i‖^2 - (number (e i))^2| ≤ 1}
private lemma smooth_spot (i : Fin m) : ContDiff ℝ ω (fun z : Points m ↦ z i) := (PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin m ↦ E4) i).contDiff
omit e in
lemma petal_ok (i : Fin 3) : ContDiff ℝ ∞ (petal i) :=
  Complex.ofRealCLM.contDiff.comp (f := fun _ : E4 ↦ _ ) (contDiff_const.mul
    (bellM.contDiff.comp ((contDiff_norm_sq ℝ).sub contDiff_const)))
private theorem boundSupport : tsupport (word e) ⊆ bounds e := by
  classical
  apply closure_minimal
  · intro z hz; apply mem_iInter.mpr; intro i
    apply petal_bound; exact fun h ↦ hz (Finset.prod_eq_zero (Finset.mem_univ _) h)
  apply isClosed_iInter
  intro i
  exact isClosed_le ((((smooth_spot i).continuous.norm.pow 2).sub continuous_const).abs) continuous_const

private theorem hard : HasCompactSupport (word e) := by
  let A (i : Fin m) := Metric.closedBall (0:E4) (|(number (e i))|+2)
  have h := (isCompact_univ_pi fun i ↦ show IsCompact (A i) from isCompact_closedBall ..).image
    (f := @WithLp.toLp 2 (Fin m → E4)) (PiLp.continuous_toLp ..)
  refine h.of_isClosed_subset (isClosed_tsupport _) (fun p hp ↦ ⟨fun i ↦ p i, ?_, rfl⟩)
  intro i _
  have he : |‖p i‖^2 - (number (e i))^2| ≤ 1 := (mem_iInter.mp (boundSupport e hp) i)
  rw [abs_le] at he
  simp only [A, Metric.mem_closedBall, dist_zero_right]
  nlinarith [he.2,sq_abs (number (e i)),abs_nonneg (number (e i))]

private theorem safe (h : Injective e) : tsupport (word e) ⊆ conf m := by
  intro z hz i j ht
  by_contra he
  have hp k : |‖z k‖^2-(number (e k))^2| ≤ 1 := mem_iInter.mp (boundSupport e hz) k
  apply ((gap (h.ne he)).not_ge : ¬ |(number (e i))^2 - (number (e j))^2| ≤ 2)
  change z i = z j at ht
  have hi := hp i; rw [ht] at hi; have hj := hp j; rw [abs_le] at hi hj ⊢
  constructor <;> linarith [hi.1,hi.2,hj.1,hj.2]

def productProfile (h : Injective e) : Test m :=
  ⟨word e, (contDiff_prod fun i _ ↦ (petal_ok (e i)).comp ((smooth_spot i).of_le le_top)), hard e, safe e h⟩

end Group

def single (i : Fin 3) : Test 1 := productProfile (fun _ ↦ i) (injective_of_subsingleton _)

def duo (i j : Fin 3) (h : i ≠ j) : Test 2 := productProfile ![i,j] (by
  intro u v; fin_cases u <;> fin_cases v <;> simp_all [Ne.symm h])

@[simp] theorem single_value (i : Fin 3) (p : Points 1) : single i p = petal i (p 0) := by
  change (∏ j : Fin 1, petal i (p j)) = _; rw [Fin.prod_univ_one]

@[simp] theorem duo_value {i j : Fin 3} (h : i ≠ j) (p : Points 2) :
    duo i j h p = petal i (p 0) * petal j (p 1) := by
  change (∏ k : Fin 2, petal (![i,j] k) (p k)) = _; rw [Fin.prod_univ_two]; rfl

end YM.SchemeConversionRG11.Coupling
