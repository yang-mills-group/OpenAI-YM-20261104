import YM.Integration.WilsonMatrixTicketLanesJoinedBins
import YM.Integration.WilsonMatrixTicketLanesPhysicalBins
import YM.Integration.WilsonMatrixTicketLanesOriginalSections

/-! Extract the actual quotient seed and the strong marked-field estimate on
one and the same projected bin of the original retained Run. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonMatrixTicketLanesStrongSeed
open Filter PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Next.Extract Dash Spec OPE OPE.RigE MergeProof MergeProof.Accent

variable {G : Gauge}

/-- The marked sections, paid trial matrices, and ultraviolet room all come
from the original run's single funded observation. The strong presentation
is chosen before the projected table. -/
theorem original (R : Run G) (simple : G.Simple) (f : Extraction.Order) :
    ∃ (g : Extraction.Order) (A : Table R.family.book) (L : ℕ → Table R.family.book)
      (B : Bin A) (Z : ∀ d, ℕ → CoordMap R.family d) (tr : Presentation R.family)
      (S : Table R.family.book) (E : DiffPlan S),
      Projected tr (f.refine g) B Z ∧ Base R.family (f.refine g) A L B S E ∧
      Nonempty (Seed R.family (f.refine g) S) ∧ (∀ d, StrongBin R.family B (f.refine g) d) ∧
      (∀ d, UVExt.Slots.StrongBin R.family B (f.refine g) d) := by
  obtain ⟨V,W,owned,tabs,fridge,sections,estimates⟩ :=
    WilsonMatrixTicketLanesOriginalSections.purchased R
  obtain ⟨q,tr,stock,strong⟩ := WilsonMatrixTicketLanesJoinedBins.issue (C := R.family) R.makes tabs
    owned.reception.2.2.2.1 fridge V W sections simple estimates
  obtain ⟨g,A,L,B,Z,S,E,projected,base,seed⟩ :=
    WilsonMatrixTicketLanesMarket.original R stock.foundation f
  exact ⟨g,A,L,B,Z,tr,S,E,projected,base,seed,strong A B (f.refine g) Z projected,
    WilsonMatrixTicketLanesPhysicalBins.of_hearth R.makes tabs owned.reception.2.2.2.1 fridge
      sections simple stock.foundation stock.hearth projected⟩

end YM.Integration.WilsonMatrixTicketLanesStrongSeed
