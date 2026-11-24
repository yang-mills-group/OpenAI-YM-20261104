import YM.Integration.WilsonIndependentOccupiedContinuity
import YM.RegulatorIR.Ledger.Ages
import YM.RegulatorIR.Ledger.Ether

/-! Passage from finite sums of captured occupied sources to their issued finite-period
report.  The full vacuum, conditional Wick contractions and measured reset are shared
at each edge.  Only convergence at the capture page is required. -/
noncomputable section
set_option autoImplicit false
open Filter
open scoped Topology
namespace YM.Integration.WilsonIndependentOccupiedLimit
open RegulatorIR RegulatorIR.Budget RegulatorIR.Ledger RegulatorIR.Ledger.Sky

variable {W ι : Type} {M : W → ℕ} {X Y : Page M → Type} {S : Sky X Y}
  [∀ p : Page M, Fintype (Y p)] {T : S.Accounts} {m : ℕ}

theorem passage (source : ι → T.Report m) (total : T.Report m) (l : Filter ι)
    (capture : Choice M)
    (entrance : ∀ w, Tendsto (fun a => (source a).point (capture.choose w)) l
      (𝓝 (total.point (capture.choose w)))) (page : Page capture.after.spans) :
    Tendsto (fun a => (source a).point (capture.after.page page)) l
      (𝓝 (total.point (capture.after.page page))) := by
  apply Page.proves (g := fun p => Tendsto (fun a => (source a).point (capture.after.page p))
    l (𝓝 (total.point (capture.after.page p)))) _ _ page
  · exact entrance
  · intro f arrived
    let edge := capture.after.wing f
    have step := (WilsonIndependentOccupiedContinuity.island (S.frames edge) m
      (T.orb edge.prev)).continuousAt.tendsto.comp arrived
    change Tendsto (fun a => (source a).point edge.next) l (𝓝 (total.point edge.next))
    change Tendsto (fun a => (S.frames edge).island m (T.orb edge.prev) ((source a).point edge.prev)) l
      (𝓝 ((S.frames edge).island m (T.orb edge.prev) (total.point edge.prev))) at step
    rw [← total.step_p edge]
    exact step.congr' (Filter.Eventually.of_forall fun a => (source a).step_p edge)

theorem dated (source : ι → T.Report m) (total : T.Report m) (l : Filter ι)
    (capture stop : Choice M) (within : ∀ w, capture.age w ≤ stop.age w)
    (entrance : ∀ w, Tendsto (fun a => (source a).point (capture.choose w)) l
      (𝓝 (total.point (capture.choose w)))) (w : W) :
    Tendsto (fun a => (source a).point (stop.choose w)) l (𝓝 (total.point (stop.choose w))) := by
  let p : Page capture.after.spans := ⟨w,stop.age w-capture.age w, by
    exact Nat.sub_le_sub_right (stop.young w) _⟩
  have location : capture.after.page p = stop.choose w := by
    simp [Era.page,p,Choice.choose,Choice.after,Nat.add_sub_of_le (within w)]
  rw [← location]
  exact passage source total l capture entrance p

omit [∀ p : Page M, Fintype (Y p)] in
theorem scalar {y : Page M} (source : ι → T.Report m) (total : T.Report m) (l : Filter ι)
    (arrived : Tendsto (fun a => (source a).point y) l (𝓝 (total.point y))) (e : ℕ) :
    Tendsto (fun a => note ((source a).point y e 0)) l (𝓝 (note (total.point y e 0))) :=
  (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp arrived e) 0) Fin.elim0)

/-- The uniform finite-subfamily estimate survives summing a complete planted source.
Both signed scalar reports use the same lower quiet and the same finite-period program. -/
theorem complete (source : ι → T.Report m) (total : T.Report m) (l : Filter ι) [NeBot l]
    (capture stop : Choice M) (within : ∀ w, capture.age w ≤ stop.age w)
    (entrance : ∀ w, Tendsto (fun a => (source a).point (capture.choose w)) l
      (𝓝 (total.point (capture.choose w)))) (w : W) (e : ℕ) (fare : ℝ)
    (bought : ∀ᶠ a in l, ‖note ((source a).point (Page.finallyW M w) e 0) -
      note ((source a).point (stop.choose w) e 0)‖ ≤ fare) :
    ‖note (total.point (Page.finallyW M w) e 0) - note (total.point (stop.choose w) e 0)‖ ≤ fare := by
  have done_ := passage source total l capture entrance (Page.finallyW _ w)
  rw [Choice.finalPage] at done_
  have stop_ := dated source total l capture stop within entrance w
  exact le_of_tendsto ((scalar source total l done_ e).sub (scalar source total l stop_ e)).norm bought

end YM.Integration.WilsonIndependentOccupiedLimit
