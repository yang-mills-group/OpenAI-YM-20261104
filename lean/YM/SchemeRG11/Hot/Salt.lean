import YM.SchemeRG11.Hot.Fabric
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
/-! A small class for Schwinger-integrand estimates. -/
set_option autoImplicit false
set_option maxHeartbeats 380000
noncomputable section
namespace YM.SchemeRG11.Hot
open Function Set MeasureTheory Metric Filter
open scoped Topology ContDiff Classical

variable {I X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
/-- Polynomials in inverse times. -/
inductive Tint (I X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] : Type
| number (z : ℂ→ℂ) (hz : Differentiable ℂ z)
| smooth (c : X→ℂ) (hc : ContDiff ℝ ∞ c)
| slot (i : I)
| add : Tint I X → Tint I X → Tint I X
| mul : Tint I X → Tint I X → Tint I X

namespace Tint
def read (e : ℂ) (r : I→ℝ) (x : X) : Tint I X → ℂ
| number z _ => z e
| smooth c _ => c x
| slot i => r i
| add P Q => read e r x P + read e r x Q
| mul P Q => read e r x P * read e r x Q

def digit (y : ℂ) : Tint I X := number (fun _=> y) (differentiable_const _)
@[simp] lemma read_digit {p : ℂ} (r : I→ℝ) (x : X) (y : ℂ) : read p r x (digit y) = y := rfl

lemma position (P : Tint I X) (e : ℂ) (r : I→ℝ) : ContDiff ℝ ∞ fun x=> read e r x P := by
  induction P with
  | number _ h => exact contDiff_const
  | smooth _ h => exact h
  | slot _ => exact contDiff_const
  | add P Q h k => exact h.add k
  | mul P Q h k => exact h.mul k
lemma dim (P : Tint I X) (r : I→ℝ) (x : X) : Differentiable ℂ fun e=> read e r x P := by
  induction P with
  | number _ h => exact h
  | smooth _ _ => exact differentiable_const _
  | slot _ => exact differentiable_const _
  | add _ _ h k => exact h.add k
  | mul _ _ h k => exact h.mul k

lemma team (P : Tint I X) : Continuous fun y : ℂ × (I→ℝ) × X=> read y.1 y.2.1 y.2.2 P := by
  induction P with
  | number _ h => exact h.continuous.comp continuous_fst
  | smooth _ h => exact h.continuous.comp (continuous_snd.comp continuous_snd)
  | slot i => unfold read; fun_prop
  | add P Q h k => exact h.add k
  | mul P Q h k => exact h.mul k
lemma top (P : Tint I X) {U : Set ℂ} (hu : IsCompact U) {K : Set X} (hk : IsCompact K) :
    ∃ C>0, ∃ k : ℕ, ∀ e∈U, ∀ x∈K, ∀ R≥(1:ℝ), ∀ r : I→ℝ, (∀ i, ‖r i‖ ≤ R) → ‖read e r x P‖ ≤ C*R^k := by
  induction P with
  | number z hz =>
    obtain ⟨C,hC⟩ := hu.exists_bound_of_continuousOn hz.continuous.continuousOn
    refine ⟨1+|C|,by positivity,0,fun e he _ _ R _ r _=>?_⟩
    rw [pow_zero,mul_one,read]
    grw [hC e he]; linarith [le_abs_self C]
  | smooth c hc =>
    obtain ⟨C,hC⟩ := hk.exists_bound_of_continuousOn hc.continuous.continuousOn
    refine ⟨1+|C|,by positivity,0,fun e _ x hx R _ r _=>?_⟩
    rw [pow_zero,mul_one,read]
    grw [hC x hx]; linarith [le_abs_self C]
  | slot i => refine ⟨1,zero_lt_one,1,fun e _ x _ R h r hr=> by simpa only [one_mul,pow_one,read,Complex.norm_real] using hr i⟩
  | add P Q h k =>
    obtain ⟨C,hC,j,hj⟩:=h; obtain ⟨D,hD,l,hl⟩:=k
    refine ⟨C+D,by positivity,max j l,fun e he x hx R hR r hr=>?_⟩
    rw [read,add_mul]; apply (norm_add_le ..).trans
    apply add_le_add
    · exact (hj e he x hx R hR r hr).trans (by gcongr; exact le_max_left ..)
    exact (hl e he x hx R hR r hr).trans (by gcongr; exact le_max_right ..)
  | mul P Q h k =>
    obtain ⟨C,hC,j,hj⟩:=h; obtain ⟨D,hD,l,hl⟩:=k
    refine ⟨C*D,by positivity,j+l,fun e he x hx R hR r hr=>?_⟩
    rw [read,norm_mul]
    grw [hj e he x hx R hR r hr,hl e he x hx R hR r hr]
    exact le_of_eq (by rw [pow_add]; ring)

def dance (v : X) : Tint I X → Tint I X
| number _ _ => digit 0
| smooth c h => smooth _ ((h.fderiv_right (by simp)).clm_apply (contDiff_const (c:=v)))
| slot _ => digit 0
| add P Q => add (dance v P) (dance v Q)
| mul P Q => add (mul P (dance v Q)) (mul Q (dance v P))

lemma dance_reads (v : X) (e : ℂ) (r : I→ℝ) (P : Tint I X) (x : X) :
    read e r x (dance v P)= fderiv ℝ (fun x=> read e r x P) x v := by
  induction P with
  | number _ _ | slot _ => simp [read,dance]
  | smooth _ _ => rfl
  | add P Q h k =>
    rw [dance,read,show (fun x=> read e r x (add P Q))=(fun x=>read e r x P)+(fun x=>read e r x Q) from rfl,h,k,fderiv_add ((P.position e r).differentiable (by simp) x) ((Q.position e r).differentiable (by simp) x)]; rfl
  | mul P Q h k =>
    rw [dance,read,read,read,show (fun x=> read e r x (mul P Q))=(fun x=>read e r x P)*(fun x=>read e r x Q) from rfl,h,k,fderiv_mul ((P.position e r).differentiable (by simp) x) ((Q.position e r).differentiable (by simp) x)]; rfl

def slant : Tint Unit X → Tint Unit X
| number _ _ => digit 0
| smooth _ _ => digit 0
| slot i => mul (digit (-1)) (mul (slot i) (slot i))
| add P Q => add (slant P) (slant Q)
| mul P Q => add (mul (slant P) Q) (mul P (slant Q))

lemma slants (P : Tint Unit X) (e : ℂ) (x : X) {t : ℝ} (ht : 0<t) :
    HasDerivAt (fun t : ℝ=>read e (fun _=> t⁻¹) x P) (read e (fun _=> t⁻¹) x (slant P)) t := by
  induction P with
  | number _ _ | smooth _ _ => simpa only [read,slant,read_digit] using hasDerivAt_const t _
  | slot i =>
    simp only [read,slant,read_digit]
    convert! ((hasDerivAt_inv ht.ne').ofReal_comp) using 1 ; push_cast; ring
  | add P Q h k => exact h.add k
  | mul P Q h k => exact h.mul k
end Tint
end YM.SchemeRG11.Hot
