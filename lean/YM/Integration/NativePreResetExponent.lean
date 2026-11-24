import YM.Integration.LocalComparisonPreReset
import YM.Integration.ActualRunVacuumGermInput

/-! Full exponent identities retain the zero-density branches of the gas.
The append summation proof is copied from the native full pre-reset donor;
no logarithm or division of a possibly zero physical density is used. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativePreResetExponent
open Function Lattice Wilson RG
open AnalyticBridge VerifiedReset Collection Quotes
open IterationFour.Vacuum LocalComparison
open scoped Classical BigOperators
variable {G : Gauge} {n : Side}

set_option maxHeartbeats 800000 in
private lemma attach_series_additive (P : Payload G n) (A : Activities G n)
    (p : BudgetPoint) (k : ℝ) (U : Config G n)
    (hA : Summable (fun i => A.regularOccurrence p i U))
    (hP : Summable (fun i => masked p.threshold (P.labels i).support (P.action i) U)) :
    Summable (fun i => (P.attach k A).regularOccurrence p i U) ∧
      (P.attach k A).additive p U = A.additive p U + k * P.amount p U := by
  let f (i : ℕ ⊕ ℕ) := (P.attach k A).regularOccurrence p (Payload.coding.symm i) U
  have h0 (i : ℕ) : f (.inl i) = A.regularOccurrence p i U := by
    simp only [f, Activities.regularOccurrence, Payload.attach, comp_apply,
      Equiv.apply_symm_apply, Sum.elim_inl]
  have h1 (i : ℕ) : f (.inr i) = k * masked p.threshold (P.labels i).support (P.action i) U := by
    simp only [f, Activities.regularOccurrence, Payload.attach, comp_apply,
      Equiv.apply_symm_apply, Sum.elim_inr, Pi.smul_apply]
    by_cases hv : Healthy p.threshold (P.labels i).support U <;> simp [hv]
  have hs0 : Summable (fun i => f (.inl i)) := hA.congr (fun i => (h0 i).symm)
  have hs1 : Summable (fun i => f (.inr i)) := (hP.mul_left k).congr (fun i => (h1 i).symm)
  have hs : Summable f := Summable.sum _ hs0 hs1
  have hi i : (P.attach k A).regularOccurrence p i U = f (Payload.coding i) := by
    simp only [f, Equiv.symm_apply_apply]
  constructor
  · exact (hs.comp_injective Payload.coding.injective).congr (fun i => (hi i).symm)
  change (∑' i, (P.attach k A).regularOccurrence p i U) = _
  simp_rw [hi]
  rw [Payload.coding.tsum_eq f, Summable.tsum_sum hs0 hs1]
  simp_rw [h0, h1]
  rw [tsum_mul_left]
  rfl


/-- Exact full exponent of every rendered row, under genuine summability. -/
theorem append_exponent (S : List (Piece G n)) (R : Rep G n)
    (k : Piece G n → Real)
    (hR : ∀ U, Summable (fun i => R.activities.regularOccurrence R.p i U))
    (hS : ∀ w ∈ S, ∀ U, Summable
      (fun i => masked R.p.threshold (w.packet.labels i).support (w.packet.action i) U))
    (U : Config G n) :
    (Render.append S R k).exponent U = R.exponent U - Render.renders k R.p U S := by
  have hsum : Summable (fun i => (Render.adorn k R.activities S).regularOccurrence R.p i U) ∧
      (Render.adorn k R.activities S).additive R.p U =
        R.activities.additive R.p U + Render.renders k R.p U S := by
    induction S with
    | nil => exact ⟨hR U, by simp [Render.adorn, Render.renders]⟩
    | cons w l ih =>
      have ht := ih (fun s hs => hS s (List.mem_cons_of_mem w hs))
      have hp := attach_series_additive w.packet (Render.adorn k R.activities l) R.p (k w) U
        ht.1 (hS w List.mem_cons_self U)
      refine ⟨hp.1, ?_⟩
      change (w.packet.attach (k w) (Render.adorn k R.activities l)).additive R.p U = _
      rw [hp.2, ht.2, Render.renders]
      ring
  change R.v * _ - R.path.inChannels R.clip R.p R.beta U -
    (Render.adorn k R.activities S).additive R.p U = _
  rw [hsum.2]
  unfold Rep.exponent
  ring

/-- At alpha zero, no extra low or high action is inserted into the full
original source. All original rows and every rendered model row remain. -/
theorem zero_append_exponent (S : List (Piece G n)) (W : PathData G)
    (c : Clip) (p : BudgetPoint) (X : Listing G n) (v : Collection.Source G n)
    (beta tau : Real) (k : Piece G n → Real) {sigma C Lambda : Real}
    (hW : W.Bounds c sigma C Lambda)
    (hX : ∀ U, Summable (fun i => (X.read v).regularOccurrence p i U))
    (hS : ∀ w ∈ S, ∀ U, Summable
      (fun i => masked p.threshold (w.packet.labels i).support (w.packet.action i) U))
    (U : Config G n) :
    (PreReset.append S W c p X v beta tau 0 k).exponent U =
      (frozen X W c p v beta tau).exponent U - Render.renders k p U S := by
  have hl := fun U : Config G n => Low.maskedPlain_sum hW p (0 : Site n) U
  have hh := fun U : Config G n => summit_sum hW p U (0 : Site n)
  have he : (PreReset.rep W c p X v beta tau 0).exponent U =
      (frozen X W c p v beta tau).exponent U := by
    change tau * _ - W.inChannels c p beta U -
      (PreReset.activities W c p X v 0).additive p U =
      tau * _ - W.inChannels c p beta U - (X.read v).additive p U
    simp only [(PreReset.raw_series_additive W c p X v 0 hX hl hh U).2,
      zero_mul, add_zero]
  exact (append_exponent S (PreReset.rep W c p X v beta tau 0) k
    (fun U => (PreReset.raw_series_additive W c p X v 0 hX hl hh U).1) hS U).trans
      (congrArg (fun z => z - Render.renders k p U S) he)

/-- Norm orders and support prices do not alter the original physical
channel function when its threshold is unchanged. -/
theorem channels_same_threshold (W : PathData G) (c : Clip)
    (p q : BudgetPoint) (h : p.threshold = q.threshold) (beta : Real)
    (U : Config G n) : W.inChannels c p beta U = W.inChannels c q beta U := by
  simp only [PathData.inChannels, PathData.principal, PathData.baseTerm,
    PathData.atomSeries, Atom.placed, h]

private theorem exponent_same_threshold (Q : Rep G n) (p q : BudgetPoint)
    (h : p.threshold = q.threshold) (U : Config G n) :
    ({Q with p := p} : Rep G n).exponent U =
      ({Q with p := q} : Rep G n).exponent U := by
  have ha : Q.activities.additive p U = Q.activities.additive q U := by
    simp only [Activities.additive, Activities.regularOccurrence, h]
  change Q.v * _ - Q.path.inChannels Q.clip p Q.beta U - Q.activities.additive p U =
    Q.v * _ - Q.path.inChannels Q.clip q Q.beta U - Q.activities.additive q U
  rw [channels_same_threshold Q.path Q.clip p q h, ha]

/-- Exact norm transport of the full original exponent, without cancelling
a gas or taking a logarithm. The common block preserves all low-row labels. -/
theorem append_norm_exponent (S : List (Piece G n)) (W : PathData G)
    (c : Clip) (p q : BudgetPoint) (X : Listing G n) (v : Collection.Source G n)
    (beta tau alpha : Real) (k : Piece G n → Real)
    (hB : p.B = q.B) (hT : p.threshold = q.threshold) (U : Config G n) :
    (PreReset.append S W c p X v beta tau alpha k).exponent U =
      (PreReset.append S W c q X v beta tau alpha k).exponent U := by
  calc
    _ = ({PreReset.append S W c p X v beta tau alpha k with p := q} : Rep G n).exponent U :=
      exponent_same_threshold (PreReset.append S W c p X v beta tau alpha k) p q hT U
    _ = _ := congrArg (fun Z : Rep G n => Z.exponent U)
      (ActualRunVacuumGermInput.append_budget_eq S W c p q X v beta tau alpha k hB)

end YM.Integration.NativePreResetExponent
end
