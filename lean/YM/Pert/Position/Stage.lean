import YM.Pert.Position.Actual
/-!
# Public partial endpoint for position tests
This is *not yet* the all-orders match (in particular `uvReading` is a stability implication, not a regulator-limit supply; determinant and actual matching hypotheses are not interchangeable). It integrates the finite raw Wilson scheme/position criterion with the actual mean leading theory and its fixed witnesses.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Position
open Spec Maxwell Labels Filter Function Submodule Climb Org Ward RawLabels MeasureTheory Lattice
open scoped Topology BigOperators ContDiff Classical
variable {G : Gauge}

lemma motor_unit {d : ℕ} {F : Frames G} (b : Buffer F d) : motor F b ((freeTable F).unit d)=(freeTable F).unit d := by simp only [motor,_root_.add_apply,b.property.1,add_zero]; rfl
lemma motor_filter {j d : ℕ} {F : Frames G} (b : Buffer F d) (j0 : j<d) {v : E F d} (h : v ∈ lower F j d) : motor F b v ∈ lower F j d := by
  change v+b.val v∈lower F j d; exact Submodule.add_mem _ h (b.property.2.1 j j0 _ h)
lemma motor_bar {d : ℕ} {F : Frames G} (b : Buffer F d) (v : E F d) :
    (freeTable F).conj (Extra.FD.table_spin F) d (motor F b v)=motor F b ((freeTable F).conj (Extra.FD.table_spin F) d v) := by unfold motor; simp only [_root_.add_apply,map_add,b.property.2.2.1]; rfl
lemma motor_spin {d : ℕ} {F : Frames G} (b : Buffer F d) (s : Signed) (v : E F d) : Extra.FD.rideO F s.ortho d (motor F b v) = motor F b (Extra.FD.rideO F s.ortho d v) := by unfold motor; simp only [_root_.add_apply,map_add,b.property.2.2.2.1]; rfl
lemma motor_mulI {d : ℕ} {F : Frames G} (b : Buffer F d) (v : E F d) : motor F b (Complex.I • v) = Complex.I • motor F b v := by unfold motor; simp only [_root_.add_apply,b.property.2.2.2.2,smul_add]; rfl

section criterion
variable {C : Family G} {F : Extraction.Order} {S : Table C.book}
variable {d t : ℕ} (Q : Conditions C.labels d t) (X : Scaling S) (b : Final C F S)

structure Mode (φ : Ledger Q → Buffer C.labels d) : Prop where
  patch : Reports (chart Q) (white Q) 0 φ
  actual : ∃ B : ℕ→Buffer C.labels d, Tendsto B atTop (𝓝 0) ∧
    (∀ᶠ k in atTop, IsUnit (motor C.labels (B k)) ∧ testedMean Q X (B k) k = chart Q (white Q,0)) ∧
    ∀ {m : ℕ} (R : Conditions C.labels d m), CleanProfiles R → Tendsto (fun k : ℕ => testedMean R X (B k) k) atTop (𝓝 (chart R (white R,0)))
  calibrates_pt (L : Side) (hL : Tendsto (fun m=> finite Q L m 0) atTop (𝓝 (white Q))) (p j : ℕ) :
    ∀ᶠ m in atTop, readJet φ p j (chart Q) (finite Q L m) (finite Q L m) = iteratedDeriv j (fun _ : ℝ=> chart Q (white Q,0)) 0
  uvReading {m} (R : Conditions C.labels d m) (L : Side) (u : ℕ→Ledger Q) (v : ℕ→Ledger R)
    (hz : u 0=white Q) (hq : ∀ i, Tendsto (fun k=> finite Q L k i) atTop (𝓝 (u i))) (hr : ∀ i, Tendsto (fun k=> finite R L k i) atTop (𝓝 (v i))) (n p : ℕ) :
    Tendsto (fun k=> readJet φ p n (chart R) (finite Q L k) (finite R L k)) atTop (𝓝 (readJet φ p n (chart R) u v)) ∧
    (n ≤ p → readJet φ p n (chart R) u v = readJet φ n n (chart R) u v)

def tailMode (d t : ℕ) (b : Final C F S) (X : Scaling S) :=
  ∀ Q : Conditions C.labels d t, square Q → CleanProfiles Q → ∃ φ, Mode Q X φ

lemma loads (h : FirstExtension b X) : tailMode d t b X := by
  intro Q hq hw; obtain ⟨φ,H⟩ := squareSolve Q hq
  refine ⟨φ,H,(actual_square Q hq hw X h), deletes_position_orders Q H, fun R L u v he hq hv n p => ⟨solvesJets Q H L he hq hv n p, ?_⟩⟩
  intro hk; have ht := H.diff; rw [← he] at ht
  apply read_together _ _ _ _ (chart_diff R).contDiffAt ht le_rfl hk
end criterion

/-- Stage-I finite position theorem combined with the same first actual target (and hence all results of `Final` on that Wilson input). No subsequence per profile. At this stage the square determinant test itself is explicit, not proved for all horizons. The actual correction is only a near-identity perturbation *in the moving frames*, with no estimate on returning to fixed labels. -/
theorem stageTarget (hg : G.Simple) {p : ℝ} (hp : 0<p) : ∃ C : Family G,
  C.path.levels.clock.kernel.penalty=p ∧ Extraction.Wcmain C ∧
  MergeProof.Ribbons.Materials C ∧ MergeProof.Ribbons.Plenty C ∧ ∀ f : Extraction.Order,
    ∃ (g : Extraction.Order) (S : Table C.book) (h : Final C (f.refine g) S), ∃ X : Scaling S, FirstExtension h X ∧ ∀ d t : ℕ, tailMode d t h X := by
  obtain ⟨C,h0,hW,hM,hP,H⟩ := firstTarget hg hp
  refine ⟨C,h0,hW,hM,hP,fun f => ?_⟩
  obtain ⟨g,S,k,X,hX⟩ := H f
  exact ⟨g,S,k,X,hX,fun d t => loads X k hX⟩
end YM.Pert.Position
