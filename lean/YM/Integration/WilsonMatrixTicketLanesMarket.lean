import YM.Integration.WilsonMatrixTicketLanesSeed

/-! Original trial purchases for every candidate raw table let us project a
specified physical presentation and keep both its projected bin and its seed. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonMatrixTicketLanesMarket
open YM.PhysicalNext YM.PhysicalNext.Repeat YM.PhysicalNext.Repeat.Legato
open YM.MergeProof YM.MergeProof.Accent
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G : Gauge} (R : Run G) {V : Push.Mark.Weave G} {Y tr}

/-- The same original run funds the trial matrices after extracting the table
and the projection of the specified presentation. -/
theorem original (funded : Scotia R.family V Y tr) (f : Extraction.Order) :
    ∃ (g : Extraction.Order) (A : Table R.family.book) (L : ℕ → Table R.family.book)
      (B : Bin A) (Z : ∀ d, ℕ → CoordMap R.family d) (S : Table R.family.book) (E : DiffPlan S),
      Projected tr (f.refine g) B Z ∧ Base R.family (f.refine g) A L B S E ∧
      Nonempty (Seed R.family (f.refine g) S) := by
  let C := R.family
  let M := R.makes
  obtain ⟨chateau, _, _, _, _, market, _, _⟩ :=
    R.bought R.T R.tuning.receipts R.t R.accepts R.stories R.doors R.makes R.carries R.books
  have wc : Wcmain C := chateau.reception.2.2.2.2.1
  obtain ⟨g₀, A, L, raw⟩ := Extraction.crops M (wc.projects C f M)
  let f₀ := f.refine g₀
  obtain ⟨g₁, B, Z, projected⟩ := include_projections A tr (funded.packed f₀)
  let f₁ := f₀.refine g₁
  have limits : RawLimits C f₁ A L := Extraction.copy_down C f₀ raw g₁
  choose X U paid using market A
  obtain ⟨g, _, p, hp, _, ⟨S,E,hE⟩, data⟩ := Beam.arriving_seed M (wc.projects C _ M)
    limits B (fun i => projected.ready i (funded.relay f₁ i)) (savings funded projected) X U paid
  have tail := Tails.refine f₁ g
  have seed := (data S E hE).1
  have base : Base C (f₁.refine g) A L B S E :=
    ⟨M, wc.projects C _ M, fun i => (tail.projected projected).ready i (funded.relay _ i),
     p, hp, hE, Work.D05.answer M (wc.projects C _ M) hE.smooth seed.generic, seed.kernel⟩
  exact ⟨g₀.refine (g₁.refine g), A,L,B,Z,S,E,tail.projected projected,base,⟨seed⟩⟩

end YM.Integration.WilsonMatrixTicketLanesMarket
