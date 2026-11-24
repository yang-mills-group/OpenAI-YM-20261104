import YM.Integration.WilsonOriginalCollarWidthAtPost
import YM.Integration.WilsonIndependentCollarEventMenu

/-! The numerical demands are listed before the physical election. At a finite
stage only a finite initial part of that list sets prices and widths. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalAllOrderCalendar
open Wilson RG RG.Supply QuadraticLocal.Mentor WilsonCoeffUV.Bank Finset
open WilsonOriginalCollarTeacher
open scoped Classical BigOperators
universe u v
variable {G : Gauge}

abbrev Key := List ℕ × ℕ × ℕ × ℕ × ℕ

/-- An index can describe the complete finite grade list, detector and accuracy. -/
def list {α : Type u} [Encodable α] {β : Type v} (missing : β) (entry : α → β) (j : ℕ) : β :=
  (Encodable.decode (α:=α) j).elim missing entry

theorem at_code {α : Type u} [Encodable α] {β : Type v} (missing : β) (entry : α → β) (a : α) :
    list missing entry (Encodable.encode a) = entry a := by simp [list]

/-- A single neutral request supplies the actual stage floors of all
preceding members; the analytic tests and their amplitudes are chosen later. -/
def diagonal (rows : ℕ → Request G) : Request G where
  radius K j H := univ.inf' univ_nonempty (fun q : Fin (j+1) =>
    WilsonThermometerUnitFilingWeakStrip.trial (rows q) K j H)
  positive K j H := (lt_inf'_iff _).2 (fun q _ => WilsonThermometerUnitFilingWeakStrip.trial_pos (rows q) K j H)
  multiplier _ := 1
  grows _ := zero_lt_one
  entrance K j A := (range (j+1)).sup (fun q => (rows q).entrance K j A)

theorem at_stage (rows : ℕ → Request G) (K : KernelChoices) (j H q : ℕ) (A : Stage) (live : q ≤ j) :
    WilsonThermometerUnitFilingWeakStrip.trial (diagonal rows) K j H ≤
      WilsonThermometerUnitFilingWeakStrip.trial (rows q) K j H ∧
    (rows q).entrance K j A ≤ (diagonal rows).entrance K j A := by
  constructor
  · have cap : (diagonal rows).radius K j H ≤ WilsonThermometerUnitFilingWeakStrip.trial (rows q) K j H := by
      exact inf'_le (f:=fun b : Fin (j+1) => WilsonThermometerUnitFilingWeakStrip.trial (rows b) K j H)
        (mem_univ (⟨q,by omega⟩ : Fin (j+1)))
    have plus := lt_min ((diagonal rows).positive K j H) (WilsonThermometerUnitFilingWeakRoom.width_pos G K j)
    have denom : 1 ≤ 16 * max 1 ((diagonal rows).multiplier H) := by
      change (1:ℝ) ≤ 16 * max 1 1
      norm_num
    exact (min_le_right ..).trans ((div_le_self plus.le denom).trans ((min_le_left ..).trans cap))
  · exact le_sup (f:=fun q => (rows q).entrance K j A) (mem_range_succ_iff.mpr live)

/-- All fixed grade, order, mask and root requests on the high actual gear. -/
def combined (rows : ℕ → Request G) (events : ℕ → ℕ → WilsonIndependentCollarEventMenu.Request G)
    (j : ℕ) (I : Gear G) : ℝ :=
  max (prices (diagonal rows) j I) (WilsonIndependentCollarEventMenu.price (fun j => range (j+1)) events j I)

theorem earn {rows : ℕ → Request G} {events : ℕ → ℕ → WilsonIndependentCollarEventMenu.Request G}
    {j : ℕ} {I : Gear G} {z : ℝ} (h : combined rows events j I ≤ z) :
    prices (diagonal rows) j I ≤ z ∧ ∀ q, q ≤ j → (events j q).price I ≤ z := by
  refine ⟨(le_max_left ..).trans h,?_⟩
  intro q live
  exact WilsonIndependentCollarEventMenu.charged (fun j => range (j+1)) events
    (mem_range_succ_iff.mpr live) ((le_max_right ..).trans h)

end YM.Integration.WilsonOriginalAllOrderCalendar
end
