import YM.Pert.Position.Implicit

/-!
# Finite jets used in scheme conversion

Use `Position.curve` to represent finite formal coefficients. Mixed substitutions and tests will
be tracked by jets at **zero**. This file does not put any smoothness or analyticity assumptions
on actual physics as a function of the real coupling. Analytic germs here are just (arbitrary)
*finite* jet representatives. No radius or remainder estimate is implied. Coefficients use the
ordinary factorial convention (coefficient of `t^j`, **not** the j-th derivative).
-/

set_option autoImplicit false
noncomputable section

namespace YM.SchemeConversionRG11

/-- Formal coefficients, not asserted summable. Even use with a finite order of known data;
  the rest can be filled arbitrarily. -/
abbrev Series (V : Type*) := ℕ → V

namespace Series

open Set Function Filter Pert.Position
open scoped Topology ContDiff

/-- Inclusive order convention. -/
def Through {E : Type*} (n : ℕ) (a b : Series E) : Prop := ∀ i ≤ n, a i = b i

section facts
variable {E : Type*} {a b c : Series E} {p q : ℕ}

@[refl] theorem Through.rfl : Through p a a := fun _ _ ↦ Eq.refl _
@[symm] theorem Through.symm (h : Through p a b) : Through p b a := fun _ hi ↦ (h _ hi).symm
@[trans]
theorem Through.trans (h : Through p a b) (k : Through p b c) : Through p a c :=
  fun _ hi ↦ (h _ hi).trans (k _ hi)
theorem Through.zero (h : Through p a b) : a 0 = b 0 := h _ (Nat.zero_le _)
theorem Through.mono (h : Through p a b) (he : q ≤ p) : Through q a b :=
  fun _ hi ↦ (h _ (hi.trans he))

end facts

section analytic
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Our specific polynomial representative at finite order. -/
abbrev trunc (a : Series E) (n : ℕ) : ℝ → E := curve a n

/-- Record of all *coefficients* of a germ. No properties unless regularity is added. -/
def record (γ : ℝ → E) : Series E :=
  fun i ↦ ((Nat.factorial i : ℝ))⁻¹ • iteratedDeriv i γ 0

/-- A jet calculation using a convenient polynomial or analytic function to represent
  a finite initial segment of formal coefficients. -/
structure Represents (n : ℕ) (γ : ℝ → E) (a : Series E) : Prop where
  regular : ContDiffAt ℝ ω γ 0
  valid : Through n (record γ) a

variable {a a' : Series E} {b : Series F} {n i : ℕ} {γ γ' : ℝ → E} {δ : ℝ → F}

theorem record_represents (h : ContDiffAt ℝ ω γ 0) : Represents n γ (record γ) :=
  ⟨h, Through.rfl⟩

@[simp] theorem record_zero_degree (γ : ℝ → E) : record γ 0 = γ 0 := by
  simp [record]

@[simp] theorem record_one_degree (γ : ℝ → E) : record γ 1 = deriv γ 0 := by
  simp [record]

theorem Represents.value (h : Represents n γ a) : γ 0 = a 0 :=
  (record_zero_degree γ).symm.trans h.valid.zero

theorem Represents.first (h : Represents n γ a) (hn : 1 ≤ n) : deriv γ 0 = a 1 :=
  (record_one_degree γ).symm.trans (h.valid 1 hn)

theorem trunc_represents (a : Series E) (n : ℕ) : Represents n (trunc a n) a := by
  refine ⟨(curve_diff a n).contDiffAt, fun i hi ↦ ?_⟩
  simp [record, trunc, curve_deriv a hi, inv_smul_smul₀ (show (Nat.factorial i : ℝ) ≠ 0 by positivity)]

theorem Represents.mono (h : Represents n γ a) (hi : i ≤ n) : Represents i γ a :=
  ⟨h.regular, h.valid.mono hi⟩

theorem Represents.unique (h : Represents n γ a) (h' : Represents n γ a') : Through n a a' :=
  h.valid.symm.trans h'.valid

theorem Represents.congr (h : Represents n γ a) (he : Through n a a') :
    Represents n γ a' := ⟨h.regular, h.valid.trans he⟩

theorem Represents.germ (h : Represents n γ a) (he : γ' =ᶠ[𝓝 0] γ) :
    Represents n γ' a :=
  ⟨h.regular.congr_of_eventuallyEq he,
   fun j hj ↦ (congrArg (((Nat.factorial j : ℝ))⁻¹ • ·) (he.iteratedDeriv_eq j)).trans
     (h.valid j hj)⟩

private theorem agree_iff (p : ℝ → E) (q : ℝ → E) (i : ℕ) :
    record p i = record q i ↔ iteratedFDeriv ℝ i p 0 = iteratedFDeriv ℝ i q 0 := by
  rw [iteratedFDeriv_eq_equiv_comp, iteratedFDeriv_eq_equiv_comp, comp_apply, comp_apply]
  unfold record
  exact (smul_right_injective E (show ((Nat.factorial i : ℝ))⁻¹ ≠ 0 by positivity)).eq_iff.trans
    (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin i) E).injective.eq_iff.symm

/-- Convenience calculus: if both inner scalar curves hit zero, composition to this order can
  read any representatives. -/
theorem chain_curve {w w' : ℝ → ℝ} (hw : Represents n w (record w'))
    (hz : w 0 = 0) (hw' : ContDiffAt ℝ ω w' 0)
    (hg : Represents n γ (record γ')) (hg' : ContDiffAt ℝ ω γ' 0) :
    Represents n (γ ∘ w) (record (γ' ∘ w')) := by
  have hew : w 0 = w' 0 := hw.value.trans (record_zero_degree _)
  have he0 : w' 0 = 0 := hew.symm.trans hz
  have hr : ContDiffAt ℝ ω γ (w 0) := hz.symm ▸ hg.regular
  have hr' : ContDiffAt ℝ ω γ' (w' 0) := he0.symm ▸ hg'
  refine ⟨hr.comp _ hw.regular, fun j hj ↦ ?_⟩
  apply (agree_iff ..).mpr
  refine Work.G05.jets_comp (d := n) (hw.regular.of_le le_top) (hw'.of_le le_top) (hr.of_le le_top)
    (hr'.of_le le_top) hew (fun k hk ↦ (agree_iff ..).1 (hw.valid k hk)) ?_ j hj
  intro k hk; rw [he0]; exact (agree_iff ..).1 (hg.valid k hk)

/-- Apply a smooth finite-dimensional user operation to a jet. -/
def liftJet (f : E → F) (a : Series E) : Series F :=
  fun i ↦ record (f ∘ trunc a i) i

theorem Represents.lift {f : E → F} (h : Represents n γ a) (hf : ContDiffAt ℝ ω f (a 0)) :
    Represents n (f ∘ γ) (liftJet f a) := by
  have hu : ContDiffAt ℝ ω f (γ 0) := h.value.symm ▸ hf
  refine ⟨hu.comp _ h.regular, fun j hj ↦ ?_⟩
  apply (agree_iff ..).mpr
  have hc := trunc_represents a j
  have he := (h.mono hj).valid.trans hc.valid.symm
  have hu' : ContDiffAt ℝ ω f (trunc a j 0) := hc.value.symm ▸ hf
  exact Work.G05.jets_comp (d := j) (h.regular.of_le le_top) (hc.regular.of_le le_top)
    (hu.of_le le_top) (hu'.of_le le_top) (h.value.trans hc.value.symm)
    (fun k hk ↦ (agree_iff ..).1 (he k hk)) (fun _ _ ↦ rfl) j le_rfl

theorem Through.lift {f : E → F} (h : Through n a a') (hf : ContDiffAt ℝ ω f (a 0)) :
    Through n (liftJet f a) (liftJet f a') :=
  ((trunc_represents a n).lift hf).unique (((trunc_represents a n).congr h).lift (h.zero ▸ hf))

@[simp] theorem liftJet_zero (f : E → F) (a : Series E) : liftJet f a 0 = f (a 0) := by
  rw [liftJet, record_zero_degree]; exact congrArg f (trunc_represents a 0).value

theorem Represents.linear (L : E →L[ℝ] F) (h : Represents n γ a) :
    Represents n (L ∘ γ) (fun i ↦ L (a i)) := by
  refine ⟨L.contDiff.contDiffAt.comp _ h.regular, fun j hj ↦ ?_⟩
  rw [← h.valid _ hj]
  unfold record iteratedDeriv
  rw [L.iteratedFDeriv_comp_left (h.regular.of_le (show ↑j ≤ ω from le_top)) le_rfl, _root_.map_smul]
  rfl

/-- Pair jet; projection rules are literal. -/
def both (a : Series E) (b : Series F) : Series (E × F) := fun i ↦ (a i, b i)

theorem Represents.pair (h : Represents n γ a) (h' : Represents n δ b) :
    Represents n (fun w ↦ (γ w, δ w)) (both a b) := by
  let f := fun w ↦ (γ w, δ w)
  have hf : Represents n f (record f) := record_represents (h.regular.prodMk h'.regular)
  have he : Through n (fun i ↦ (record f i).1) a :=
    (show Represents n γ _ from hf.linear (ContinuousLinearMap.fst ℝ E F)).unique h
  have he' : Through n (fun i ↦ (record f i).2) b :=
    (show Represents n δ _ from hf.linear (ContinuousLinearMap.snd ℝ E F)).unique h'
  exact ⟨hf.regular, fun j hj ↦ Prod.ext (he j hj) (he' j hj)⟩

section Substitution
variable {x : Series ℝ} {w : ℝ → ℝ}

/-- Outer a, inner coupling w. Legal substitution requires `x 0 = 0`. -/
def subJet (a : Series E) (x : Series ℝ) : Series E :=
  fun i ↦ record (trunc a i ∘ trunc x i) i

theorem Represents.subJet (h : Represents n γ a) (hw : Represents n w x) (hz : x 0 = 0) :
    Represents n (γ ∘ w) (subJet a x) := by
  have hz' : w 0 = 0 := hw.value.trans hz
  have hr : ContDiffAt ℝ ω γ (w 0) := hz'.symm ▸ h.regular
  refine ⟨hr.comp _ hw.regular, fun j hj ↦ ?_⟩
  have hc := trunc_represents a j
  have hw' := trunc_represents x j
  exact ((chain_curve ((hw.mono hj).congr hw'.valid.symm) hz' hw'.regular
    ((h.mono hj).congr hc.valid.symm) hc.regular).valid _ le_rfl)

theorem subJet_base (hx : x 0 = 0) : subJet a x 0 = a 0 := by
  rw [subJet, record_zero_degree]
  simp only [comp_apply, (trunc_represents x 0).value, hx, (trunc_represents a 0).value]

theorem Through.subst_jet {x' : Series ℝ} (h : Through n a a') (he : Through n x x')
    (hx : x 0 = 0) : Through n (subJet a x) (subJet a' x') := by
  have hg := trunc_represents a n
  have hw := trunc_represents x n
  exact (hg.subJet hw hx).unique ((hg.congr h).subJet (hw.congr he) (he.zero.symm.trans hx))

theorem subJet_assoc {z : Series ℝ} (hx : x 0 = 0) (hz : z 0 = 0) :
    subJet a (subJet x z) = subJet (subJet a x) z := by
  funext i
  have hg := trunc_represents a i
  have hw := trunc_represents x i
  have hp := trunc_represents z i
  exact (hg.subJet (hw.subJet hp hz) ((subJet_base hz).trans hx)).unique
    ((hg.subJet hw hx).subJet hp hz) _ le_rfl

/-- Identity parameter. -/
def parameter : Series ℝ := record id

@[simp] theorem parameter_zero : parameter 0 = 0 := record_zero_degree _
@[simp] theorem parameter_one : parameter 1 = 1 := by simp [parameter]

@[simp] theorem subJet_id (a : Series E) : subJet a parameter = a := by
  funext i
  have h := trunc_represents a i
  exact (h.subJet (record_represents contDiffAt_id) parameter_zero).unique h i le_rfl

@[simp] theorem id_subJet (hx : x 0 = 0) : subJet parameter x = x := by
  funext i
  have h := trunc_represents x i
  exact ((record_represents contDiffAt_id).subJet h hx).unique h i le_rfl

end Substitution
end analytic
end Series
end YM.SchemeConversionRG11
