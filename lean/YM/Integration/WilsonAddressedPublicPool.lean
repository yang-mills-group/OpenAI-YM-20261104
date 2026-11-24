import YM.Integration.WilsonAddressedReportingCalendar
import YM.Integration.WilsonOriginalMicroscopicStandingLabels

/-! The physical field of each grade is chosen once on the same raw reporting
grid before selecting a finite roster or a required accuracy. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonAddressedPublicPool
open Function Filter Finset Set RG Wilson Extraction Table Spec Trace.Pilot GapsContact.Seams
open PhysicalNext.Repeat.Legato WilsonThermometerUnitFilingFourPool WilsonAddressedReportingScale
open WilsonOriginalMicroscopicStandingLabels WilsonOriginalMicroscopicGuardedNomination
open scoped Classical Topology
variable {G : Gauge} (R : Run G) {f : Extraction.Order} {S : Table R.family.book}
  (F : Final R.family f S) {l : Ultrafilter (ℕ×ℕ)} {H : (Climb.Bel R.family.book).Hierarchy}
  {Z : Trace.Terrace.Arch R.family}
local notation "C₀" => R.family

structure Pool (D : ℕ) (g : ℝ → ℝ) (U : ℝ) where
  ρ : ℝ → ℝ
  B : ℝ → ℝ
  j : ℝ → ℕ
  m : ℝ → ℕ
  power : ℕ
  field : (i : Fin (D+1)) → ℝ → S.Field i.val → ℕ×ℕ → (C₀).label i.val
  onset : Tendsto ρ trail trail
  enters : Tendsto j trail atTop
  receipt : ∀ᶠ r in trail, Receipt F l (ρ r) (j r) (m r) D (B r)
  mesh : ∀ᶠ r in trail, (C₀).S.a (j r)/r ≤ (g r)^2 ∧ (r/(C₀).S.a (j r))*(g r)^power ≤ U
  standing : ∀ᶠ r in trail, ∀ i, Press R F (l:=l) (ρ r) (j r) (m r) i.val (B r) (field i r)
  named : ∀ q, ∀ᶠ r in trail, ∀ i, ∀v, Named R F (l:=l) (ρ r) (j r) (m r) i.val q (B r) v (field i r v)

theorem original (simple : G.Simple) (bliss : Bliss F l Z H)
    (wide : ∀j,1 ≤ ((C₀).path.levels.budget j).supportExponent) (g : ℝ → ℝ) (hg : Coupling G g)
    (D : ℕ) : ∃ U : ℝ, 0<U ∧ Nonempty (Pool (l:=l) R F D g U) := by
  classical
  obtain ⟨T,U,up,⟨C⟩⟩ := WilsonAddressedReportingCalendar.original F simple bliss g hg (fun _ => D)
  let ρ := radius (univ.sup T)
  let B (r : ℝ) := dock (ρ r)^(T 0)
  let j (r : ℝ) := C.j r 0
  let m (r : ℝ) := C.m r 0
  have card : ∀ᶠ r in trail, Receipt F l (ρ r) (j r) (m r) D (B r) := C.receipt.mono fun _ h => h 0
  let stands (r : ℝ) (i : Fin (D+1)) (Y : S.Field i.val → ℕ×ℕ → (C₀).label i.val) :=
    Press R F (l:=l) (ρ r) (j r) (m r) i.val (B r) Y
  let Y (i : Fin (D+1)) (r : ℝ) := Classical.epsilon (stands r i)
  have press : ∀ᶠ r in trail, ∀ i, stands r i (Y i r) := by
    filter_upwards [card] with r h i
    have own : Receipt F l (ρ r) (j r) (m r) i.val (B r) :=
      ⟨h.fore,h.breadth,h.front,fun d hd => h.budget d (hd.trans (Nat.le_of_lt_succ i.isLt))⟩
    exact Classical.epsilon_spec (before R F own)
  refine ⟨U,up,⟨ρ,B,j,m,2*(2*univ.sup T+2),Y,near _,C.enters 0,card,C.mesh.mono (fun _ h => h 0),press,?_⟩⟩
  intro q
  have late : ∀ᶠ r in trail, ∀ i : Fin (D+1), ∀ w M b W,
      Press R F (l:=l) w (j r) M i.val b W → ∀v, Named R F (l:=l) w (j r) M i.val q b v (W v) :=
    Filter.eventually_all.mpr fun i => (C.enters 0).eventually (WilsonOriginalMicroscopicStandingLabels.named R F simple wide i.val q)
  exact (press.and late).mono fun _ h i => h.2 i _ _ _ _ (h.1 i)

end YM.Integration.WilsonAddressedPublicPool
end
