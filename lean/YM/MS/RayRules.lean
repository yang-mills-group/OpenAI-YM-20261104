import YM.MS.RayLimit
import Mathlib.Data.Nat.Choose.Cast
/-!
# Test jets as ordinary Taylor coefficients along chart rays

Dimension label j relative to external dimensions. Derive smooth polynomials
from the weaker direction tests, including algebraic conversion with support.
No multi-completions or coordinate Taylor in graph routing needed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Plane
open Function Set Koszul Wire Tensor Real
open scoped Topology ContDiff
variable {A P ι E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P] {f g : E → ℂ} {j : ℕ}

lemma rangle {e:E→ℂ} (h:ContDiff ℝ ∞ e) (j : ℕ) x : reading j (fun t:ℝ=>e (t • x)) = stage j e x := by
    unfold stage Tensor.diagonal Tensor.coeff reading
    rw [smul_apply]; congr 1; let Q:=ContinuousLinearMap.toSpanSingleton ℝ x
    have h:= congr_arg (fun T : ℝ [×j]→L[ℝ] ℂ => T (fun _=>1)) (Q.iteratedFDeriv_comp_right h 0 (show (j:WithTop ℕ∞)≤ ∞ by exact_mod_cast le_top))
    convert! h using 1; simp [Q]

namespace Shape
variable {x y : ℤ}
lemma scalar (c : ℂ) (h : Shape f x) : Shape (c • f) x where
   smooth := contDiff_const.smul h.smooth
   charge hx := by rw [h.charge hx, smul_zero]
   scale t a := calc
      _ = c • (t^x • f a) := by simp [h.scale]
      _ = _ := smul_comm ..
lemma add (h : Shape f x) (H : Shape g x) : Shape (f+g) x := ⟨h.smooth.add H.smooth,fun hx=>by rw [h.charge hx,H.charge hx,add_zero],fun t i=>by simp only [Pi.add_apply,h.scale,H.scale,smul_add]⟩
lemma sum {s : Finset A} {f : A → E→ℂ} (h : ∀ i∈s, Shape (f i) x) : Shape (∑ i ∈ s, f i) x := by
   classical
   induction s using Finset.induction with
   | empty=> simpa using form_zero (E:=E) x
   | insert i s hi ih => rw [Finset.sum_insert hi]; exact (h i (Finset.mem_insert_self ..)).add (ih (fun i hx=> h i (Finset.mem_insert_of_mem hx)))
lemma mul (h : Shape f x) (H : Shape g y) : Shape (f*g) (x+y) := by
   rcases lt_or_ge x 0 with hx|hx
   · rw [h.charge hx,zero_mul]; exact form_zero _
   rcases lt_or_ge y 0 with hy|hy
   · rw [H.charge hy,mul_zero]; exact form_zero _
   refine ⟨h.smooth.mul H.smooth, fun h=>by omega, fun t i=>?_⟩
   rw [Pi.mul_apply,h.scale,H.scale,Pi.mul_apply]; obtain ⟨l,hl⟩ := Int.eq_ofNat_of_zero_le hx; obtain ⟨k,hk⟩:=Int.eq_ofNat_of_zero_le hy; subst x y; simp only [← Nat.cast_add, zpow_natCast, pow_add, Complex.real_smul,Complex.ofReal_mul]; ring
lemma linear {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q] (h : Shape f x) (L : Q →L[ℝ] E) : Shape (fun q=> f (L q)) x :=
  ⟨h.smooth.comp L.contDiff,fun hx=> by rw [h.charge hx]; rfl,fun t i=> by simp only [map_smul,h.scale]⟩
lemma stage' (h : Shape f x) (u : E) : stage j f u= if x=(j:ℤ) then f u else 0:= by
   rcases lt_or_ge x 0 with hx|hx; · rw [h.charge hx, if_neg (by omega)]; simp [stage,Tensor.diagonal,Tensor.coeff]
   lift x to ℕ using hx
   rw [← rangle h.smooth, show (fun t:ℝ=> f (t • u))=(fun t:ℝ=>t^x • f u) from by ext; rw [h.scale]; simp, reading, iteratedDeriv_smul_const, iteratedDeriv_fun_pow_zero]
   · split_ifs <;> first | (push_cast; grind) | simp_all <;> field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero x)]
   fun_prop
lemma form (h : Shape f j) : f = Tensor.diagonal (Tensor.coeff f j 0):= funext fun x => (by simpa [stage] using (stage' (j:=j) h x).symm)
end Shape

section scalar
variable {f g : ℝ→ℂ}
lemma read_add (h : ContDiff ℝ ∞ f) (g' : ContDiff ℝ ∞ g) : reading j (fun t=>f t+g t) = reading j f + reading j g:= by
    simp_rw [reading, iteratedDeriv_fun_add (h.contDiffAt.of_le (by exact_mod_cast le_top)) (g'.contDiffAt.of_le (by exact_mod_cast le_top)), smul_add]
lemma read_const (c : ℂ) (f : ℝ→ℂ) : reading j (fun t=>c*f t)=c*reading j f:=by
    rw [reading, iteratedDeriv_const_mul_field]; exact smul_comm ((Nat.factorial j:ℝ)⁻¹) c (iteratedDeriv j f 0)
lemma read_pow (c : ℂ) (i : ℕ) : reading j (fun t : ℝ=> t^i • c) = if i=j then c else 0 := by
    rw [reading, iteratedDeriv_smul_const (f:= (· ^ i)) (by fun_prop), iteratedDeriv_fun_pow_zero]
    by_cases h:i=j
    · subst i; simp only [↓reduceIte]; exact inv_smul_smul₀ (by positivity) _
    simp [h,Ne.symm h]
lemma read_mul (h : ContDiff ℝ ∞ f) (H : ContDiff ℝ ∞ g) : reading j (fun t=> f t*g t)=∑ i∈ Finset.range (j+1), reading i f * reading (j-i) g := by
    unfold reading; rw [iteratedDeriv_fun_mul (h.contDiffAt.of_le (by exact_mod_cast le_top)) (H.contDiffAt.of_le (by exact_mod_cast le_top)), Finset.smul_sum]
    refine Finset.sum_congr rfl fun i hi=>?_
    have hi : i≤j:= Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have he : (j.choose i:ℂ)*(Nat.factorial i:ℂ)*(Nat.factorial (j-i):ℂ)=(Nat.factorial j:ℂ):= by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi
    have hx (k:ℕ) : (Nat.factorial k:ℂ)≠0:= Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    simp only [Complex.real_smul, Complex.ofReal_inv,Complex.ofReal_natCast]; field_simp [hx]; rw [← he]; ring
lemma read_sum {s : Finset A} {f : A→ℝ→ℂ} (h : ∀ i∈s, ContDiff ℝ ∞ (f i)) : reading j (fun t=>∑ i ∈s,f i t)=∑ i∈s, reading j (f i):= by
    classical
    induction s using Finset.induction with
    | empty => simp [reading]
    | insert i s hi ih => simp_rw [Finset.sum_insert hi]; rw [read_add, ih]; exact fun j hj=> h j (Finset.mem_insert_of_mem hj); exact h i (Finset.mem_insert_self ..); exact ContDiff.sum (fun j hj=> h j (Finset.mem_insert_of_mem hj))
end scalar
lemma Form.const_term {f : Row A P ℂ} {m : A→ℤ} {h : ℤ} {b : Bool} (H : Form f m h b) (w : Legs (Mode A P)) (hw : Course b w): torch j f w=if fieldDim m w+j=h then f w else 0 := by
   unfold torch; rw [(H ℝ (ray w) (ray_course hw)).stage',fieldVal,ray_sail,ray_dim]; split <;> split <;> first | rfl | omega

/-! Negative jets are not terms. Take according to total dimension integer. -/
variable (m : A → ℤ) (h : ℤ)
def skin (f : Row A P ℂ) : Row A P ℂ := fun w=> if fieldDim m w≤h then torch (h-fieldDim m w).toNat f w else 0
lemma skin_eq (f : Row A P ℂ) {w : Legs (Mode A P)} (hv : fieldDim m w+j=h) : skin m h f w = torch j f w:=by
   simp only [skin,show fieldDim m w≤h by omega,↓reduceIte]; congr 1; omega
lemma skin_form {f : Row A P ℂ} {b : Bool} (H : ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E], ∀ w : Wire A E P, Course b w→ ContDiff ℝ ∞ (fieldVal f w)) : Form (skin m h f) m h b:= by
   intro X _ _ w hw; rcases lt_or_ge h (fieldDim m w) with hi|hi
   · rw [show fieldVal (skin m h f) w=0 from funext fun i=> by simp only [fieldVal,skin,sail_dim, not_le.mpr hi, ↓reduceIte, Pi.zero_apply]]; exact form_zero _
   rw [show fieldVal (skin m h f) w=stage (h-fieldDim m w).toNat (fieldVal f w) from funext fun x=> by unfold fieldVal; rw [skin_eq]; exact lit _ _ (H _ w hw) x; rw [sail_dim]; omega]; exact form_diag _ _ (by omega)
end YM.MS.Plane
