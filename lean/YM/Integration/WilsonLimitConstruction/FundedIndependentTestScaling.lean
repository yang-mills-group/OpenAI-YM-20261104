import YM.Integration.LocalComparisonEnvelopeDensity
import YM.Integration.FullQLocalOutputScaling
import YM.RG3.Held.Typed

/-! Independent test normalization of every original occurrence, including
compulsory marked labels. At an arbitrary test the exact scale of a
particular mode is the product over its own slot set. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedIndependentTestScaling
open Function Finset Lattice Wilson RG Marker Overlay RG3.Forms RG3.Held RG3.Script.Picnic LocalComparison
open FullQLocal
open scoped Classical BigOperators

variable {V : Type} [DecidableEq V] {D : V → ComparisonDensity.Address.Orbit}

def shrink (w : V→ℝ) (x : TestSpace D) : TestSpace D := VariableScaling.tests (fun v => (w v:ℂ)⁻¹) x

theorem row {Γ : Census V} (s : Γ.Mode) {f : TestSpace D→ℂ} (hf : Letter ℂ (fun v => (D v).Mood) s.val f)
    (w : V→ℝ) (x : TestSpace D) : f (shrink w x)=(∏v∈s.val,w v)⁻¹ • f x := by
  have named : Published (K:=ℂ) (fun v=>(D v).Mood) (fun y=>Poly.send s (f y)) := by
    intro j
    by_cases eq : j=s
    · subst j
      simpa only [Poly.part_send,↓reduceIte] using hf
    · simp only [Poly.part_send,if_neg eq]
      exact Letter.still
  have h := VariableScaling.published_part (fun y => Poly.send s (f y)) named
    (fun v => (w v:ℂ)⁻¹) x s
  simpa only [Poly.part_send,↓reduceIte,shrink,Finset.prod_inv_distrib,Complex.real_smul,
    Complex.ofReal_inv,Complex.ofReal_prod] using h

omit [DecidableEq V] in
/-- Each test slot is normalized independently before any size, field, or period
is evaluated. Its finite scalar can be recovered by native multilinearity. -/
theorem represent (x : TestSpace D) :
    ∃ (w : V→ℝ), (∀v,0<w v) ∧ ∃ t : IndependentTests D, testInclusion D t=shrink w x := by
  choose c hc using fun v => (D v).admits (x v)
  let w : V→ℝ := fun v => max 1 (c v)
  have pos (v) : 0<w v := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let t : IndependentTests D := fun v => ⟨(shrink w x v).val,by
    apply ((hc v).smul (w v:ℂ)⁻¹).more
    rw [norm_inv,Complex.norm_real,Real.norm_of_nonneg (pos v).le]
    calc (w v)⁻¹*c v ≤ (w v)⁻¹ * w v := mul_le_mul_of_nonneg_left (le_max_right _ _) (inv_nonneg.mpr (pos v).le)
         _=1 := inv_mul_cancel₀ (pos v).ne'⟩
  exact ⟨w,pos,t,rfl⟩

variable [Fintype V] {Γ : Census V} {G : Gauge} {n : Side} {P : Rep G n}
    {o : V→Site n} (T : Taste (TestSpace D) o P Γ) (H : Multilinear D T)

include H

omit [Fintype V] in
/-- Rescaling the physical independent test itself realizes the native
`priceNormalized` deck on every regular, compulsory, global, and caption row. -/
theorem deck (w : V→ℝ) : pullback (shrink w) T=priceNormalized (envelopeProduct w) T := by
  have hu : (fun y => T.menu.global (shrink w y))=
      fun x v => (envelopeProduct w (Γ.fire v))⁻¹ • T.menu.global x v := by
    funext x v
    simpa only [envelopeProduct,Census.fire,Finset.prod_singleton] using row (Γ.fire v) (H.unit v) w x
  have hr : (fun y => T.menu.regular (shrink w y))=
      fun x i U => (envelopeProduct w (T.menu.rays i))⁻¹ • T.menu.regular x i U := by
    funext x i U
    exact row (T.menu.rays i) (H.regular i U) w x
  have hf : (fun y => T.menu.force (shrink w y))=
      fun x i j U => (envelopeProduct w (T.menu.marks i j))⁻¹ • T.menu.force x i j U := by
    funext x i j U
    exact row (T.menu.marks i j) (H.forced i j U) w x
  have hc : (fun y => T.score (shrink w y))=fun x i => (envelopeProduct w (T.tag i))⁻¹ • T.score x i := by
    funext x i
    exact row (T.tag i) (H.captions i) w x
  simp only [pullback,priceNormalized,hu,hr,hf,hc]

theorem density (w : V→ℝ) (hw : ∀ v,0<w v) (x : TestSpace D) (U : Config G n) (a : Γ.Mode) :
    ((T.leaf (shrink w x)).density U).part a=(envelopeProduct w a)⁻¹ • ((T.leaf x).density U).part a := by
  change (((pullback (shrink w) T).leaf x).density U).part a=_
  rw [deck T H]
  exact priceNormalized_density_part T w hw x U a

theorem restore (w : V→ℝ) (hw : ∀v,0<w v) (x : TestSpace D) (U : Config G n) (a : Γ.Mode) :
    ((T.leaf x).density U).part a=envelopeProduct w a • ((T.leaf (shrink w x)).density U).part a := by
  rw [density T H w hw,smul_smul,mul_inv_cancel₀ (envelopeProduct_positive hw a).ne',one_smul]

end YM.Integration.WilsonLimitConstruction.FundedIndependentTestScaling
end
