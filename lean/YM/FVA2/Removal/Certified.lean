import YM.FVA2.Removal.Wires
import YM.FVA2.Notch.Platter

/-!
# Getting the unmarked comparison estimates from the same supplies

Whenever using `Removal.MenuCost` (e.g. `Notch.Poise.passengers`), one can unpack its
`fabric` to get the two `Images` (for the two choices of input to the comparison on the SAME
geometry -- purely physical or with the added canonical-generator changes for mark matching).
This gives extensive estimate data, including `Images.small` on nonempty sets of marks and
`Images.runs` (`Period` includes the bulk and defect bounds). Here is how to get also explicit
positive-order *difference* bounds on the unmarked bulk parts in those same estimates (use with
the formulas of `Removal/Wires.lean`, with these same `X` and `U`).

`TaylorOKF` input from `Main.Match.details.method.Taylor`. These are the kernel norms of the
supplied MS implementation; `Images` uses *lattice units*.
-/

set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Removal

open Function Set Filter MeasureTheory Lattice
open MS MS.High MS.Book MS.Book.Program MS.Menus MS.Wind MS.Wind.Leading
open MS.Plane MS.Orbit MS.Orbit.LogReal MS.Rake MS.Vane MS.Vista MS.Fleet MS.SpaceOut
open MS.Swirl MS.Swirl.Near MS.Tide MS.Dial MS.Land
open scoped Topology ContDiff Interval

variable {G : Gauge} {I W : Type} [LinearOrder W]
    (T : Trial I W) {ν : ℝ} (H : Spots T ν) (p : W → Label (Press.portDeck G))
    (Y : XSpace.Initialize G) (A : Prescription (Press.portDeck G))
    {O : Booked (Press.portDeck G)} (Z : MS_Data G O) (S : TaylorOKF Z (Press.wickInput Y) A)
    (h : G.Simple)
variable {X U : Rake.Dance G I W}

/-- Bulk component difference and corresponding defect bounds; here `Q` has the placements
built in (see `MenuCost`). Order-zero Gaussian is accounted separately. -/
abbrev ComparedBulk (G : Gauge) {I W : Type} [LinearOrder W]
    (T : Trial I W) (ν : ℝ) (A : Prescription (Press.portDeck G))
    (Q : Seeds G I W) (U : Rake.Dance G I W) : Prop :=
  let F := enterV T.side true
  let K := lampV G T.side
  let V := loose T.profile ν
  ∃ B D,
    Circuit F K (TokenB G A.team T.profile.η) T.head Q B D U ∧
    Period (Mid V T.side) F K B D U T.head 1 ∧
    Period (After V T.side) F K B D U T.head (Tail V T.side) ∧
    (∀ n : ℕ, 0 < n → DoubleB V T.side true true
      (B n - Orbit.Scope G (Wind.skyline G A.team) T.profile.η n))

include H h S
lemma bulkPhysical (hI : Images G (loose T.profile ν) T.side T.profile.η T.head
    (goalsK T.off T.profile.η (ApplyMF (Press.wickInput Y) A.team A p)) A.team true X U) :
    ComparedBulk G T ν A
      (goalsK T.off T.profile.η (ApplyMF (Press.wickInput Y) A.team A p)) U := by
  have ht := extent H.total H.reality
  have hf := (billMenusF p (φ := Press.wickInput Y) (A := A) h).1
  obtain ⟨B, D, _, hB, ⟨hm, hl⟩, hd⟩ :=
    Body_frame hI (moneyM T.off ht fun i => ⟨false, 0, hf.badge i⟩) S.bulk ht.proper
  exact ⟨B, D, hB, hm, hl, hd⟩

lemma bulkAuxiliary (hI : Images G (loose T.profile ν) T.side T.profile.η T.head
    (goalsK T.off T.profile.η (PortEntryF (Press.wickInput Y) A ∘ p)) A.team true X U) :
    ComparedBulk G T ν A (goalsK T.off T.profile.η (PortEntryF (Press.wickInput Y) A ∘ p)) U := by
  have ht := extent H.total H.reality
  have hf := (billMenusF p (φ := Press.wickInput Y) (A := A) h).2.1
  obtain ⟨B, D, _, hB, ⟨hm, hl⟩, hd⟩ :=
    Body_frame hI (moneyM T.off ht fun i => ⟨false, 0, hf.badge i⟩) S.bulk ht.proper
  exact ⟨B, D, hB, hm, hl, hd⟩

end YM.FVA2.Removal
