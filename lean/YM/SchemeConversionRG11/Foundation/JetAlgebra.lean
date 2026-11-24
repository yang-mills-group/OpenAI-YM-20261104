import YM.SchemeConversionRG11.Foundation.Limits

/-! Pointwise algebra lemmas, for noncommuting field matrices & capture transforms.
Use by representing the *same* truncated coefficients. -/

set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.Series

open Function Filter Pert.Position
open scoped Topology ContDiff BigOperators

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {a a' : Series E} {b b' : Series F} {f : E → G} {n : ℕ}

@[simp] theorem Represents_zero (n : ℕ) : Represents n (0 : ℝ → E) 0 := by
  convert! trunc_represents (0 : Series E) n
  simp [trunc, curve, funext_iff]

theorem Represents_linear_eq {γ : ℝ → E} (L : E →L[ℝ] F) (h : ContDiffAt ℝ ω γ 0) (i : ℕ) :
    record (L ∘ γ) i = L (record γ i) :=
  ((record_represents (n:=i) h).linear L).valid i le_rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem Through.both (h : Through n a a') (k : Through n b b') :
    Through n (both a b) (both a' b') := fun i hi ↦ Prod.ext (h i hi) (k i hi)

theorem liftJet_subst (hf : ContDiffAt ℝ ω f (a 0)) {x : Series ℝ} (hx : x 0 = 0) :
    liftJet f (subJet a x) = subJet (liftJet f a) x := by
  funext i
  have H := trunc_represents a i
  have K := trunc_represents x i
  have he := H.subJet K hx
  exact (he.lift (f:=f) ((subJet_base (a:=a) hx).symm ▸ hf)).unique ((H.lift hf).subJet K hx) i le_rfl

theorem both_subst {x : Series ℝ} (hx : x 0 = 0) :
    both (subJet a x) (subJet b x) = subJet (both a b) x := by
  funext i
  have H := trunc_represents a i
  have K := trunc_represents b i
  have V := trunc_represents x i
  exact ((H.subJet V hx).pair (K.subJet V hx)).unique ((H.pair K).subJet V hx) i le_rfl

theorem jet_of_linear (L : E →L[ℝ] F) : liftJet L a = fun i ↦ L (a i) := by
  funext i
  have h := trunc_represents a i
  exact (h.lift L.contDiff.contDiffAt).unique (h.linear L) i le_rfl
end YM.SchemeConversionRG11.Series
