import YM.Integration.ActualRunUnmaskedPartners
import YM.Integration.ForcedPolynomialPages

/-!
One finite Page family for the actual unmasked input.  The original regular
kernels and every nonquiet forced correction are combined without replacing
the old Nat-indexed gas.  The family is fixed before its scalar readings.
The price theorem consumes the genuine common coefficient sheet and retains
its rooted bill; it does not manufacture a smallness estimate.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualRunFullPages
open Finset Function MeasureTheory Lattice Wilson RG Marker FVA1
open MergeProof MergeProof.Accent MergeProof.Replicums Planned.GuardedAtom Extra.Histories
open Push.GridApprox.Nil PhysicalNext.Repeat.Legato OriginalForcedAddresses
open ActualRunUnmaskedPartners MergeProof.Ribbon
open scoped BigOperators Classical

section ForcedPrice
variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V] [Fintype V]
    {Γ : Census V} {P : Rep G n}

/-- The finite compatible modes pay only the original sheet price, with no
mode-count factor and at the original complete support. -/
theorem forced_hit (K : Guard.Keeper P.p P.activities) (o : Positions V n)
    (F : Box n → Config G n → Poly Γ) (w : V → ℝ) (hw : ∀ i, 0 < w i)
    (b : Box n → Sheet Γ) (hb : ∀ s, 0 ≤ b s) {a c : ℝ}
    (h : Ac.Hit Prod.fst P.p.B (fun s => wordsPrice w (b s)) a c) :
    Ac.Hit (fun j : ForcedPolynomialPages.Index (Γ := Γ) o =>
      (P.activities.forced (cart K j.1)).support) P.p.B
      (fun j => (ForcedPolynomialPages.page K o F j).due w (b j.1.val j.2.val)) a c := by
  intro x
  have hs (s : StockTag n) :
      (P.activities.forced (cart K s)).support = s.val.1 :=
    congrArg Prod.fst (cardK K s)
  refine ⟨?_, Summable.of_finite, ?_⟩
  · intro j
    dsimp only
    split_ifs
    · exact mul_nonneg
        (by rw [ForcedPolynomialPages.due_exact]; exact mul_nonneg (Poly.worth hw _).le (hb _ _))
        (Real.exp_pos _).le
    exact le_rfl
  rw [tsum_fintype, Fintype.sum_sigma]
  simp_rw [hs]
  calc
    _ = ∑ s : StockTag n, if x ∈ s.val.1 then
        (∑ q : ForcedPolynomialPages.Modes (Γ := Γ) o s,
          (ForcedPolynomialPages.page K o F ⟨s, q⟩).due w (b s.val q.val)) *
          Real.exp (a * coverNumber P.p.B s.val.1) else 0 := by
      apply Finset.sum_congr rfl
      intro s _
      by_cases hx : x ∈ s.val.1 <;> simp only [hx, ite_true, ite_false,
        Finset.sum_const_zero, Finset.sum_mul]
    _ ≤ ∑ s : StockTag n, if x ∈ s.val.1 then
        wordsPrice w (b s.val) * Real.exp (a * coverNumber P.p.B s.val.1) else 0 := by
      apply Finset.sum_le_sum
      intro s _
      split_ifs
      · exact mul_le_mul_of_nonneg_right
          (ForcedPolynomialPages.sum_due_le K o F s w hw (b s.val) (hb s.val))
          (Real.exp_pos _).le
      exact le_rfl
    _ ≤ c := by
      have hh := Push.Local.sumBudget_subtype Sure (h x)
      have ht : (∑' s : StockTag n, if x ∈ s.val.1 then
          wordsPrice w (b s.val) * Real.exp (a * coverNumber P.p.B s.val.1) else 0) ≤ c := hh.2.2
      simpa only [tsum_fintype] using ht

end ForcedPrice

abbrev Index {n : Side} {V : Type} [DecidableEq V] [Fintype V] (o : Positions V n) :=
  V ⊕ ForcedPolynomialPages.Index (Γ := Bud V) o

section Actual
variable {G : Gauge} (R : Run G) (hG : G.Simple) (N p L : ℕ)
    (hLN : L ≤ N) {V : Type} [DecidableEq V] [Fintype V]
    (o : Positions V (R.family.side L p)) (d : V → ℕ)
    (v : ∀ i, R.family.label (d i))


/-- Original pre-mask regular Pages, followed by their full forced partners
at the old Keeper addresses.  Neither branch changes the representation. -/
def pages : Index o → Page (Bud V) (R.family.path.rep N p L) :=
  Sum.elim (fun i => ActualRunPhysicalPages.page R N p L (d i) o i (v i))
    (ForcedPolynomialPages.page (actual_keeper R hG N L p hLN) o
      (actualCorrection R N p L o d v))

def prices (b : Box (R.family.side L p) → Sheet (Bud V)) : Index o → ℝ :=
  Sum.elim (fun i => ActualRunPhysicalPages.price R L (d i) (v i))
    (fun j => b j.1.val j.2.val)

theorem entries (href : ∀ i, R.family.ref (d i) ≤ L)
    (b : Box (R.family.side L p) → Sheet (Bud V))
    (hb : ∀ s U q, ‖(actualCorrection R N p L o d v s U).part q‖ ≤ b s q)
    (j : Index o) :
    (pages R hG N p L hLN o d v j).Entry o (prices R p L o d v b j) := by
  cases j with
  | inl i => exact ActualRunPhysicalPages.entry R N p L (d i) hLN (href i) o i (v i)
  | inr j =>
    exact ForcedPolynomialPages.entry
      (actual_keeper R hG N L p hLN) o (actualCorrection R N p L o d v)
      (actual_correction_flow R N p L o d v hLN href) j _ (fun U => hb _ U _)

theorem aroma (U : Config G (R.family.side L p)) :
    (∑ j : Index o, (pages R hG N p L hLN o d v j).aroma 1 U) =
      healthyLog R N p L o d v U := by
  rw [Fintype.sum_sum_type]
  simp only [pages, Sum.elim_inl, Sum.elim_inr, ActualRunPhysicalPages.page,
    ForcedPolynomialPages.page, Page.aroma, Page.point, Page.ready,
    Sum.elim_inl, Sum.elim_inr, mul_one, one_mul, Finset.sum_const_zero, add_zero]
  rfl

theorem payments (href : ∀ i, R.family.ref (d i) ≤ L)
    (U : Config G (R.family.side L p)) (k : ℕ) :
    (∑ j : Index o, (pages R hG N p L hLN o d v j).payment 1 U k) =
      NativeForcedPolynomialReentry.rebook (actual_keeper R hG N L p hLN)
        (actualCorrection R N p L o d v) k U := by
  rw [Fintype.sum_sum_type]
  have hz : (∑ i : V,
      (pages R hG N p L hLN o d v (.inl i)).payment 1 U k) = 0 := by
    simp only [pages, Sum.elim_inl, ActualRunPhysicalPages.page, Page.payment,
      Sum.elim_inl, Finset.sum_const_zero]
  rw [hz, zero_add]
  exact ForcedPolynomialPages.sum_payment (actual_keeper R hG N L p hLN) o
    (actualCorrection R N p L o d v)
    (actual_correction_quiet R N p L o d v hLN href)
    (actual_correction_stubs R N p L o d v) U k

/-- Equality of the complete polynomial, including all mixed modes and every
old gas factor.  No nonzero-vacuum hypothesis or division is used. -/
theorem essence_full (href : ∀ i, R.family.ref (d i) ≤ L)
    (U : Config G (R.family.side L p)) :
    essence (pages R hG N p L hLN o d v) (fun _ => 0) (fun _ => 1) U =
      fullInput R N p L o d v U := by
  unfold essence
  rw [aroma R hG N p L hLN o d v U]
  simp_rw [payments R hG N p L hLN o d v href U]
  have hm : Mach (Bud V) (fun _ : V => (0 : ℂ)) = 0 := by
    simp [Mach]
  rw [hm, zero_add]
  exact (actual_density_original_dictionary R N p L o d v hG hLN href U).symm

/-- The same family has the sum of the original regular bill and the common
forced sheet bill.  Both bills use the actual support exponent and block. -/
theorem menuSafe (href : ∀ i, R.family.ref (d i) ≤ L)
    (b : Box (R.family.side L p) → Sheet (Bud V))
    (hb : ∀ s, 0 ≤ b s)
    (hcoef : ∀ s U q, ‖(actualCorrection R N p L o d v s U).part q‖ ≤ b s q)
    (w : V → ℝ) (hw : ∀ i, 0 < w i) {r f : ℝ}
    (hr : Ac.Hit (fun i => ActualRunPhysicalPages.cover R p L (d i) o i)
      (R.family.path.rep N p L).p.B
      (fun i => (ActualRunPhysicalPages.page R N p L (d i) o i (v i)
        (B := Bud V)).due w (ActualRunPhysicalPages.price R L (d i) (v i)))
      ((R.family.path.rep N p L).p.supportExponent - 4) r)
    (hf : Ac.Hit Prod.fst (R.family.path.rep N p L).p.B
      (fun s => wordsPrice w (b s))
      ((R.family.path.rep N p L).p.supportExponent - 4) f) :
    MenuSafe (pages R hG N p L hLN o d v) o (prices R p L o d v b) w (r + f) := by
  refine ⟨entries R hG N p L hLN o d v href b hcoef, hw, ?_⟩
  have hh := forced_hit (actual_keeper R hG N L p hLN) o
    (actualCorrection R N p L o d v) w hw b hb hf
  intro x
  refine ⟨?_, Summable.of_finite, ?_⟩
  · intro j
    cases j with
    | inl i => exact (hr x).1 i
    | inr j => exact (hh x).1 j
  rw [tsum_fintype, Fintype.sum_sum_type]
  exact add_le_add
    (by simpa only [tsum_fintype, pages, prices, Sum.elim_inl,
      ActualRunPhysicalPages.page, Seal.scope, id_eq] using (hr x).2.2)
    (by simpa only [tsum_fintype, pages, prices, Sum.elim_inr,
      ForcedPolynomialPages.page, Seal.scope] using (hh x).2.2)

end Actual
end YM.Integration.ActualRunFullPages
