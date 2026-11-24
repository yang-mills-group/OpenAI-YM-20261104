import YM.Integration.WilsonIndependentOccupiedLimit
import YM.RegulatorIR.Ledger.Terminal

/-! The finite-volume read includes its last covariance and its Haar contribution to
the already evolved vacuum. The captured occupied array alone is varied here. -/
noncomputable section
set_option autoImplicit false
open Filter
open scoped Topology
namespace YM.Integration.WilsonIndependentOccupiedVista
open RegulatorIR RegulatorIR.Budget RegulatorIR.Ledger RegulatorIR.Ledger.Sky
open WilsonIndependentOccupiedLimit

variable {W ι : Type} {M : W → ℕ} {X Y : Page M → Type} (S : Sky X Y)
  [∀ p : Page M, Fintype (Y p)] (T : S.Accounts) {m : ℕ}

theorem reading (source : ι → T.Report m) (total : T.Report m) (l : Filter ι)
    (F : Margins Y) (capture : Choice M)
    (entrance : ∀ w, Tendsto (fun a => (source a).point (capture.choose w)) l
      (𝓝 (total.point (capture.choose w)))) (w : W) (e : ℕ) :
    Tendsto (fun a => S.vista T (source a) F w e) l (𝓝 (S.vista T total F w e)) := by
  have final_ := passage source total l capture entrance (Page.finallyW _ w)
  rw [Choice.finalPage] at final_
  let quiet := Diagram.logHeat (F.endK w) (S.stump T F w) true
  have h : Continuous fun z : Diagram.Orders (Y (Page.finallyW M w)) =>
      Diagram.endHeat m (F.endK w) quiet z e 0 := by
    apply WilsonIndependentOccupiedContinuity.finiteHeat
    intro a r
    exact (continuous_apply r).comp (continuous_apply a)
  exact tendsto_pi_nhds.mp (h.continuousAt.tendsto.comp final_) Fin.elim0

theorem complete (source : ι → T.Report m) (total : T.Report m) (l : Filter ι) [NeBot l]
    (F : Margins Y) (capture stop : Choice M) (within : ∀ w, capture.age w ≤ stop.age w)
    (entrance : ∀ w, Tendsto (fun a => (source a).point (capture.choose w)) l
      (𝓝 (total.point (capture.choose w)))) (w : W) (e : ℕ) (fare : ℝ)
    (bought : ∀ᶠ a in l, ‖S.vista T (source a) F w e -
      note ((source a).point (stop.choose w) e 0)‖ ≤ fare) :
    ‖S.vista T total F w e - note (total.point (stop.choose w) e 0)‖ ≤ fare := by
  have right := scalar source total l (dated source total l capture stop within entrance w) e
  exact le_of_tendsto ((reading S T source total l F capture entrance w e).sub right).norm bought

end YM.Integration.WilsonIndependentOccupiedVista
