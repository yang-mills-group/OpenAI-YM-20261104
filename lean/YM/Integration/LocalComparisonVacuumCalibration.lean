import YM.Integration.LocalComparisonGlobalContract

/-!
Exact calibration remainder on the selected qlocal output. The original
source, scalar, masks and full model list survive. This file identifies the
full-field remainder; it does not declare that remainder a masked Calibration,
purchase a reset, or assert a vanishing cap.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.LocalComparison.VacuumCalibration
open Function Lattice Wilson RG
open AnalyticBridge VerifiedReset Collection Quotes
open IterationFour.Vacuum Extra.Iteration
open scoped BigOperators
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


/-- The exponent identity underlying the already-proved full render. -/
theorem render_exponent (S : List (Piece G n)) (R : Rep G n) (k : Piece G n → ℝ)
    (hR : ∀ U, Summable (fun i => R.activities.regularOccurrence R.p i U))
    (hS : ∀ w ∈ S, ∀ U, Summable (fun i =>
      masked R.p.threshold (w.packet.labels i).support (w.packet.action i) U))
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
  have he : (Render.append S R k).exponent U = R.exponent U - Render.renders k R.p U S := by
    change R.v * _ - R.path.inChannels R.clip R.p R.beta U -
      (Render.adorn k R.activities S).additive R.p U = _
    rw [hsum.2]
    unfold Rep.exponent
    ring
  exact he

/-- The full correction relative to a specified physical beta and renderer.
In particular the low/high alpha receipts are retained on every field. -/
theorem raw_calibration_exponent (S : List (Piece G n))
    (W : PathData G) (c : Clip) (p : BudgetPoint) (X : Listing G n)
    (v : Collection.Source G n) (β τ α b : ℝ) (k k0 : Piece G n → ℝ)
    {σ C Λ : ℝ} (hW : W.Bounds c σ C Λ)
    (hX : ∀ U, Summable (fun i => (X.read v).regularOccurrence p i U))
    (hS : ∀ w ∈ S, ∀ U, Summable (fun i =>
      masked p.threshold (w.packet.labels i).support (w.packet.action i) U))
    (U : Config G n) :
    (PreReset.append S W c p X v (β - α) τ α k).exponent U =
      (PreReset.append S W c p X v (β - α) τ α k).scalar -
      (W.inChannels c p b U + Render.renders k0 p U S) -
      (X.read v).additive p U -
      ((β - α - b) * Push.BetaTransport.kinetic W c p U +
        α * receipt W c p U + α * Reset.leading W p U +
        Render.renders (k - k0) p U S) := by
  have hl := fun U : Config G n => Low.maskedPlain_sum hW p (0 : Site n) U
  have hh := fun U : Config G n => summit_sum hW p U (0 : Site n)
  rw [PreReset.append,
    render_exponent S (PreReset.rep W c p X v (β - α) τ α) k
      (fun U => (PreReset.raw_series_additive W c p X v α hX hl hh U).1) hS U]
  change (τ * Fintype.card (Site n) - W.inChannels c p (β - α) U -
      (PreReset.activities W c p X v α).additive p U) - Render.renders k p U S =
    τ * Fintype.card (Site n) - (W.inChannels c p b U + Render.renders k0 p U S) -
      (X.read v).additive p U -
      ((β - α - b) * Push.BetaTransport.kinetic W c p U +
        α * receipt W c p U + α * Reset.leading W p U +
        Render.renders (k - k0) p U S)
  rw [(PreReset.raw_series_additive W c p X v α hX hl hh U).2,
    Render.render_sub, Push.BetaTransport.channels_split U (β - α),
    Push.BetaTransport.channels_split U b]
  ring

section Selected
open Global
variable {V : Type} [DecidableEq V] [Fintype V] {R : Marker.Census V} {C : Family G}
    {Y : Comparison.RG02.Bulk.Chain C.path} {J : Setup V} {A : Admission C J}
    {K : Prices A} {datum : LocalFormal.Datum C R} {I : Input Y J A datum}
    {delta : ℝ} {forcedOrder : ℕ}

/-- Exact next-vacuum algebra on the SAME selected output. No output
representation, source row, independent test family or scalar is replaced. -/
theorem selected_calibration_exponent (H : Result K I delta forcedOrder)
    (hC : C.Makes) (U : Config G (C.side datum.level datum.period)) :
    let W := (C.path.rep datum.cutoff datum.period datum.level).path
    let c := (C.path.levels.params datum.level).clip
    let p := C.path.levels.budget datum.level
    let b := C.path.β datum.cutoff datum.period datum.level
    let k := Render.prefactor (IterationFour.Currency.gain (I.plan.predict datum.level))
    let k0 := Render.prefactor (IterationFour.Currency.g C datum.cutoff datum.period datum.level)
    H.output.carrier.rep.exponent U =
      H.output.carrier.rep.scalar -
      (W.inChannels c p b U + Render.renders k0 p U (I.plan.layers datum.level)) -
      (H.vacuum.listing.read H.vacuum.source).additive p U -
      ((I.plan.predict datum.level - I.plan.alpha datum.level - b) *
          Push.BetaTransport.kinetic W c p U +
        I.plan.alpha datum.level * receipt W c p U +
        I.plan.alpha datum.level * Reset.leading W p U +
        Render.renders (k - k0) p U (I.plan.layers datum.level)) := by
  dsimp only
  have hs := hC.wilson.represents datum.cutoff datum.period datum.level datum.below.le
  have hW : (C.path.rep datum.cutoff datum.period datum.level).path.Bounds
      (C.path.levels.params datum.level).clip (C.path.levels.params datum.level).width
      (C.path.levels.params datum.level).paths (C.path.levels.clock.loopCap datum.level) := by
    rw [← hs.clip]
    exact hs.good.paths
  rw [H.vacuum.representation]
  exact raw_calibration_exponent _ _ _ _ _ _ _ _ _ _ _ _ hW
    H.vacuum.source_summable H.vacuum.model_summable U

end Selected
end YM.Integration.LocalComparison.VacuumCalibration
end
