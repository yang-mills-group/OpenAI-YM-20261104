import YM.Integration.WilsonMatrixTicketLanesMarket
import YM.UVExt.StrongRelay

/-! The physical marked-slot and microscopic estimates of the manuscript on
one specified projected presentation. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonMatrixTicketLanesPhysicalBins
open YM.PhysicalNext YM.PhysicalNext.Repeat YM.PhysicalNext.Repeat.Legato
open Set Function MeasureTheory Filter Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Guard Next.Foundations Local Next.Rank Edition Spindle Extra.Multi Motion
open PhysicalNext.Repeat.Legato.Bandage Cells Extraction Extraction.Lease Exponential Bid Next.Extract RelayDifference Opening
open Labels Maxwell
open YM.MergeProof
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
open Dash Spec UVExt.Slots
variable {G : Gauge} {C : Family G}

theorem of_hearth (M : C.Makes) (tabs : Stock.Tabs C.path.levels) {w : Bid.Worth}
    {u ψ φ δ : ℕ → ℝ} {ζ : ℕ → ℕ → ℝ} {r : ℕ → ℕ}
    {doors : ∀ N p m : ℕ, m < N → GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
    (scrim : Scrim C w u ψ φ δ ζ r doors) (fridge : Fridge C u ζ)
    {V : ∀ d, SectionData (C.labels.level d)} {weave : Push.Mark.Weave G}
    (sections : ∀ d, Push.Mark.Portfolio C.params (V d) (weave d)) (simple : G.Simple)
    {Y : ∀ d, Cutoffs → (C.label d ≃ₗ[ℂ] C.label d)} {tr : Presentation C}
    (scotia : Scotia C weave Y tr) (hearth : ∀ d, ∃ E U, Hearth (C := C) (V d) ζ E (fun i j => Y d (i,j)) U)
    {A : Table C.book} {B : Bin A} {f : Extraction.Order} {Z : ∀ d, ℕ → CoordMap C d}
    (projected : Projected tr f B Z) (d : ℕ) : UVExt.Slots.StrongBin C B f d := by
  obtain ⟨E,U,h⟩ := hearth d
  refine ⟨fun x hx hv => UVExt.Slots.marshal_strong M tabs (V d) weave (sections d) _ h x hv
    (fun j => ((scotia.step d j.1 j.2).ker) ▸ (show x j ∈ LinearMap.ker (tr.step d j).toLinearMap from
      LinearMap.mem_ker.mpr ?_)),fun x p => onions M tabs scrim simple fridge _
      (protectedMixed M simple (fridge.shifts f) _ _) (stencilled_mixed (Stencilled.visits M x) p)
      (Eventually.of_forall fun i => slot_continuous _ _ _ _ _)⟩
  rw [← projected.same d];exact hx j

/-- The original Run already has a common physical marked-slot bin before
requesting matrix prices. A strengthened presentation from the same source
can use of_hearth again to carry both families of estimates. -/
theorem original (R : Run G) (simple : G.Simple) (f : Extraction.Order) :
    ∃ (g : Extraction.Order) (A : Table R.family.book) (L : ℕ → Table R.family.book)
      (B : Bin A) (Z : ∀ d, ℕ → CoordMap R.family d) (tr : Presentation R.family)
      (S : Table R.family.book) (E : DiffPlan S),
      Projected tr (f.refine g) B Z ∧ Base R.family (f.refine g) A L B S E ∧
      Nonempty (Seed R.family (f.refine g) S) ∧ ∀ d, UVExt.Slots.StrongBin R.family B (f.refine g) d := by
  obtain ⟨owned,tabs,_,fridge,⟨V,W,Y,tr,sections,issued⟩,_,_,_⟩ :=
    R.bought R.T R.tuning.receipts R.t R.accepts R.stories R.doors R.makes R.carries R.books
  obtain ⟨g,A,L,B,Z,S,E,projected,base,seed⟩ :=
    WilsonMatrixTicketLanesMarket.original R issued.foundation f
  exact ⟨g,A,L,B,Z,tr,S,E,projected,base,seed,of_hearth R.makes tabs
    owned.reception.2.2.2.1 fridge sections simple issued.foundation issued.hearth projected⟩

end YM.Integration.WilsonMatrixTicketLanesPhysicalBins
