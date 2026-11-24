import YM.Integration.FullQLocalRetainedOutput
import YM.Ac.Tree

/-! Each retained pre-reset source row survives in the chosen output's
activities. Restricting a paid bound on that bank gives a new estimate for
the very same retained source, with its marked and forced laws intact. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FullQLocal.RenderedStep.Numeric.Retained.SourceAncestor
open Function Filter Finset Lattice Wilson RG Marker
open RG3.Script.Picnic Comparison.RG02 IterationFour IterationFour.Vacuum
open LocalComparison LocalComparison.Global AnalyticBridge VerifiedReset Collection
open Push.AbsoluteSums Extra.Iteration
open scoped BigOperators Classical
variable {G : Gauge} {n : Side}

private def baseIndex (n : Side) : ℕ ↪ ℕ :=
  ⟨fun i => (numbering (EKey n)).symm (Sum.inl i),
    fun _ _ h => Sum.inl.inj ((numbering (EKey n)).symm.injective h)⟩

private def keep : ℕ ↪ ℕ :=
  ⟨fun i => Payload.coding.symm (Sum.inl i),
    fun _ _ h => Sum.inl.inj (Payload.coding.symm.injective h)⟩

private def layers : ℕ → ℕ ↪ ℕ
  | 0 => .refl ℕ
  | k + 1 => (layers k).trans keep

/-- Injection of all old rows through the pre-reset tags and every selected
vacuum layer, in the native carrier's actual enumeration. -/
def index (S : List (Piece G n)) : ℕ ↪ ℕ := (baseIndex n).trans (layers S.length)

private lemma layered (S : List (Piece G n)) (k : Piece G n → ℝ)
    (A : Activities G n) (i : ℕ) :
    (Render.adorn k A S).reg (layers S.length i) = A.reg i ∧
    (Render.adorn k A S).E (layers S.length i) = A.E i := by
  induction S with
  | nil => exact ⟨rfl,rfl⟩
  | cons s l ih =>
    simpa [Render.adorn, Payload.attach, layers, keep, Function.comp_def] using ih

/-- Address and unmasked signed source agree at each ancestor. -/
theorem rows (S : List (Piece G n)) (W : PathData G) (c : Clip) (p : BudgetPoint)
    (X : Listing G n) (v : Collection.Source G n) (β τ α : ℝ) (k : Piece G n → ℝ)
    (i : ℕ) :
    (PreReset.append S W c p X v β τ α k).activities.reg (index S i) = X.reg i ∧
    (PreReset.append S W c p X v β τ α k).activities.E (index S i) = v.logRead i := by
  have h := layered S k (PreReset.activities W c p X v α) (baseIndex n i)
  simpa [PreReset.append, PreReset.rep, Render.append, index, baseIndex,
    PreReset.activities, PreReset.labels, PreReset.rows, Function.comp_def] using h

private lemma layered_forced (S : List (Piece G n)) (k : Piece G n → ℝ)
    (A : Activities G n) : (Render.adorn k A S).forced = A.forced ∧
    (Render.adorn k A S).K = A.K := by
  induction S with
  | nil => exact ⟨rfl,rfl⟩
  | cons s l ih => exact ih

/-- The forced channel retains its entire unmasked bank at unchanged indices. -/
theorem forced (S : List (Piece G n)) (W : PathData G) (c : Clip) (p : BudgetPoint)
    (X : Listing G n) (v : Collection.Source G n) (β τ α : ℝ) (k : Piece G n → ℝ) :
    (PreReset.append S W c p X v β τ α k).activities.forced = X.hard ∧
    (PreReset.append S W c p X v β τ α k).activities.K = v.hardRead :=
  layered_forced S k (PreReset.activities W c p X v α)

private lemma subseries {ι κ : Type*} (e : ι ↪ κ) {f : κ → ℝ} {B : ℝ}
    (h : SumBudget f B) : SumBudget (f ∘ e) B :=
  budget_of_sum (fun i => h.1 (e i)) fun s => by
    simpa [Finset.sum_map, Function.comp_def] using budget_sum h (s.map e)

private lemma restrict_early (p : BudgetPoint) (r t : ℕ → RegularAddress n) (e : ℕ ↪ ℕ)
    (hrow : ∀ i, r (e i) = t i) (u : ℕ → ℝ) {B : ℝ} (h : Quotes.early p r u B) :
    Quotes.early p t (u ∘ e) B := by
  intro o
  simpa [Function.comp_def, hrow] using subseries e (h o)

/-- Support-point incidence at the exact native three-unit reserve controls
the native pre-reset anchor invoice with the same total. -/
theorem early_of_hit (p : BudgetPoint) (r : ℕ → RegularAddress n) (u : ℕ → ℝ) {B : ℝ}
    (h : Ac.Hit (fun i => (r i).support) p.B u (Quotes.preExponent p) B) :
    Quotes.early p r u B := by
  intro o
  apply budget_mono (h o)
  · intro i
    by_cases hs : (r i).site = o
    · have hm : o ∈ (r i).support := by rw [← hs]; exact (r i).anchor
      simpa [hs, hm] using (h o).1 i
    · simp [hs]
  · intro i
    by_cases hs : (r i).site = o
    · have hm : o ∈ (r i).support := by rw [← hs]; exact (r i).anchor
      simp [hs,hm]
    · simpa [hs] using (h o).1 i

variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V} {C : Family G}
  {J : Request V} {A : NumericSchedule C J} {datum : LocalFormal.Datum C R}
  {caps : Handoff.OutputCapacities} {Y : Bulk.Chain C.path} {K : NumericPrices A}
  {F : AnalyticInput J A datum} {η : ℝ} {I : FullPreparedInputAt F η}
  {M : AnalyticOutput caps Y K F}
  {O : ProducedOutput J.tests I.carrier F.fineRoots F.coarseRoots I.input}

/-- Original ancestor rows inside this very chosen physical carrier. -/
theorem chosen_rows (v : ChosenVacuum K I M O) (i : ℕ) :
    O.carrier.rep.activities.reg (index (M.plan.layers datum.level) i) = v.listing.reg i ∧
    O.carrier.rep.activities.E (index (M.plan.layers datum.level) i) = v.source.logRead i := by
  rw [v.representation]
  exact rows ..

/-- The same chosen carrier's unmasked forced entries, with the full
inventory and eligibility predicate at each original index. -/
theorem chosen_forced (v : ChosenVacuum K I M O) :
    O.carrier.rep.activities.forced = v.listing.hard ∧
    O.carrier.rep.activities.K = v.source.hardRead := by
  rw [v.representation]
  exact forced ..

/-- Apply the actual appended carrier's regular invoice to its retained
source. This preserves all forced estimates and all gauge laws for that
source, and replaces the complete ordinary allowance. -/
theorem estimate (v : ChosenVacuum K I M O) {B : ℝ} (u : ℕ → ℝ)
    (hb : ∀ i, (A.outputNorm datum.level).supBounds (O.carrier.rep.activities.reg i).site
      (O.carrier.rep.activities.reg i).support (O.carrier.rep.activities.E i) (u i))
    (he : Quotes.early (A.outputNorm datum.level) O.carrier.rep.activities.reg u B) :
    Collection.Local v.listing (A.outputNorm datum.level) v.source B
      (C.path.levels.clock.forcedAllowance datum.level) := by
  refine { v.estimate with cheap := ⟨u ∘ index (M.plan.layers datum.level), ?_,
    restrict_early _ _ _ _ (fun i => (chosen_rows v i).1) _ he⟩ }
  intro i
  simpa [Function.comp_def, (chosen_rows v i).1, (chosen_rows v i).2]
    using hb (index (M.plan.layers datum.level) i)

/-- Simultaneous ordinary and forced invoices at distinct native reserves,
on the full old source with the original structural certificates. -/
theorem joint (v : ChosenVacuum K I M O) {B w : ℝ} (u t : ℕ → ℝ)
    (hb : ∀ i, (A.outputNorm datum.level).supBounds (O.carrier.rep.activities.reg i).site
      (O.carrier.rep.activities.reg i).support (O.carrier.rep.activities.E i) (u i))
    (he : Ac.Hit (fun i => (O.carrier.rep.activities.reg i).support) (A.outputNorm datum.level).B
      u (Quotes.preExponent (A.outputNorm datum.level)) B)
    (hk : ∀ i, 0 ≤ t i ∧ ∀ U, ‖O.carrier.rep.activities.K i U‖ ≤ t i)
    (hp : Ac.Hit (fun i => (O.carrier.rep.activities.forced i).support) (A.outputNorm datum.level).B
      t ((A.outputNorm datum.level).supportExponent+1) w) :
    Collection.Local v.listing (A.outputNorm datum.level) v.source B w := by
  refine { estimate v u hb (early_of_hit _ _ _ he) with expensive := ⟨t, ?_, ?_⟩ }
  · simpa [(chosen_forced v).2] using hk
  · simpa [(chosen_forced v).1] using hp

end YM.Integration.FullQLocal.RenderedStep.Numeric.Retained.SourceAncestor
end
