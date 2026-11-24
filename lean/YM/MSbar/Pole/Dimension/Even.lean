import YM.MSbar.Pole.Analysis.Bottles
import YM.MSbar.Pole.Analysis.Planes
import Mathlib.Analysis.Calculus.Deriv.ZPow

/-!
# Two added ambient dimensions

The operation is smooth across zero. It preserves any dual seminorms on external variables
and their parameter holomorphy (the latter established separately).
-/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole.Radial
open Function Set Filter MeasureTheory
open scoped Topology ContDiff Classical Interval
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Shape controls. -/
def Moment (q : Price E) : Price (ℝ × E) := ticket Prod.fst * q.back Prod.snd
omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
@[simp] lemma moment_apply (q : Price E) (x : ℝ × E) : Moment q x=(1+|x.1|)*q x.2 := rfl

def EvenOn (U : Set E) (f : ℝ × E → ℂ) := ∀ x∈U, Function.Even fun t => f (t,x)

def letter (f : ℝ×E→ℂ) := fieldD (1,(0:E)) f
/-- Formula honest for any nonzero radius after differentiating. At zero picks germ. -/
def higher (f : ℝ×E → ℂ) (u : ℝ×E) :=
    -(2:ℝ)⁻¹ • ∫ t : ℝ in Ioc (0:ℝ) 1, deriv (fun s : ℝ => deriv (fun x : ℝ => f (x,u.2)) s) (t*u.1)

variable {U : Set E} {f : ℝ × E→ℂ} {p q : Price E}
variable (h : Packet (univ ×ˢ U) (p.back Prod.snd) (Moment q) f)
include h
lemma through_letter : Packet (univ ×ˢ U) (p.back Prod.snd) (Moment q) (letter f) :=
    h.fderiv.apply (X:=ContinuousLinearMap.apply ℝ ℂ _)
lemma letter_read (t : ℝ) {x : E} (hx : x∈U) : HasDerivAt (fun s : ℝ=> f (s,x)) (letter f (t,x)) t := by
  have hl := h.smooth (t,x) ⟨mem_univ _,hx⟩
  exact ((hl.differentiableAt (by simp)).hasFDerivAt).comp_hasDerivAt t ((hasDerivAt_id' t).prodMk (hasDerivAt_const t x))
lemma alternative {x : E} (hx : x∈U) : ∀ r,higher f (r,x) = -(2:ℝ)⁻¹ • ∫ t : ℝ in (0:ℝ)..1, letter (letter f) (t*r,x) := by
  intro r; unfold higher
  simp_rw [(letter_read h _ hx).deriv,(letter_read (through_letter h) _ hx).deriv, intervalIntegral.integral_of_le zero_le_one]

lemma opposite (he : EvenOn U f) {x : E} (hx : x∈U) (t : ℝ) : letter f (-t,x) = -letter f (t,x) := by
  have hv := letter_read h (-t) hx
  have hs := he x hx; have hh := hv.scomp t (hasDerivAt_id' t).neg -- x ∘ -(y)
  change HasDerivAt (fun z => f (-z,x)) _ t at hh
  have hy : (fun z => f (-z,x))=fun z : ℝ=> f (z,x) := funext hs
  rw [hy] at hh
  have H := hh.unique (letter_read h t hx)
  simpa only [neg_smul,one_smul,neg_eq_iff_eq_neg] using H

lemma formula (he : EvenOn U f) (r : ℝ) {x : E} (hx : x∈U) :
    r • higher f (r,x) = -(2:ℝ)⁻¹ • letter f (r,x) := by
  have hz : letter f (0,x) =0 := by
    have ha : -letter f (0,x)=letter f (0,x) := by simpa using (opposite h he hx 0).symm
    apply mul_left_cancel₀ (show (2:ℂ)≠0 from by norm_num)
    calc 2*letter f (0,x) = _ := two_mul _
         _ = 0 := by nth_rw 1 [← ha]; simp
         _ = _ := by rw [mul_zero]
  have hc : Continuous (fun t : ℝ=> letter (letter f) (t*r,x)) := by
    let H := through_letter (through_letter h)
    refine continuous_iff_continuousAt.mpr fun i => ?_
    exact (H.smooth _ ⟨mem_univ _,hx⟩).continuousAt.comp (show Continuous (fun t : ℝ => (t*r,x)) from by fun_prop).continuousAt
  rw [alternative h hx,smul_comm, ← intervalIntegral.integral_smul,intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f:=fun t : ℝ => letter f (t*r,x)) (fun y _ => ?_) ((show Continuous (fun i : ℝ=>r • letter (letter f) (i*r,x)) from hc.const_smul r).intervalIntegrable _ _)]
  · rw [one_mul,zero_mul,hz,sub_zero]
  have hl : HasDerivAt (fun t : ℝ => t*r) r y := by simpa using (hasDerivAt_id' y).mul_const r
  exact (letter_read (through_letter h) (y*r) hx).scomp y hl
lemma alt_of_ne (he : EvenOn U f) {r : ℝ} (hr : r ≠ 0) {x : E} (hx : x∈U) : higher f (r,x) = r⁻¹ • (-(2:ℝ)⁻¹ • letter f (r,x)) := by
  rw [← formula h he r hx, inv_smul_smul₀ hr]
lemma higher_even (he : EvenOn U f) : EvenOn U (higher f) := by
  intro x hx t; by_cases ht : t=0
  · subst t; simp
  change higher f (-t,x) = higher f (t,x)
  rw [alt_of_ne h he (neg_ne_zero.mpr ht) hx,alt_of_ne h he ht hx,opposite h he hx t]; simp
end YM.MSbar.Pole.Radial
