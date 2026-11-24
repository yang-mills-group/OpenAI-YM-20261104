import YM.Integration.WilsonCapturedSoldSeedPanel
import YM.Integration.WilsonMarkedFiniteIndependentHistory

/-! The ordinary finite programme of the predeclared microscopic source, with its original source-index maps. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicVerseSeed
open Function Finset Lattice Laurent Bloch Wilson RG Precision Tree Exterior Stationary
open PowerSeries Next.Free FormalBulk08 Flat Reef Jets Series Shore Gorge Lotus Mesa City Cork
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue
open WilsonCoeffUV.Soil WilsonCoeffUV.Mer WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Winding WilsonPointChildPlacedFamily
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open PhysicalNext.Repeat.Legato Next.Foundations Pose Dawn Kemp Rift
open scoped Classical BigOperators
variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I](R:Run G)
  (u:I→G.ColorIndex)(k h:I→ℕ)(depth:∀s,k s<h s)(digit:I→∀j,Site (R.family.S.block j))
  (N:ℕ)(v:∀s,Letter (R.family.labels.level (k s)))

def seed : Outerm G h :=
  fun p=>WilsonPointChildCenteredPortfolio.bank R u depth digit N N v p

omit [Fintype I] [DecidableEq I] in
theorem lawful (simple:G.Simple)(o:Loc G 1):Wellness k (seed R u k h depth digit N v):=by
  classical
  have paid(p:I→ Cover):=WilsonPointChildCenteredPortfolio.lawful R u depth o simple digit N N le_rfl v p
  refine ⟨fun p=>(paid p).2,fun p=>(paid p).1,?_⟩
  intro p x S same
  by_cases one:S.card=1
  · obtain ⟨s,rfl⟩:=Finset.card_eq_one.mp one
    simp only [seed,WilsonPointChildCenteredPortfolio.bank,WilsonPointChildPlacedFamily.singleton]
    rw [same s (by simp)]
  · simp only [seed,WilsonPointChildCenteredPortfolio.bank,WilsonPointChildPlacedFamily.other _ one]

variable (a:G.ColorIndex)
  (tags:∀j n,(Flat.primary (R.family.path.levels.clock.op j 0).patch R.family.path.levels.clock.kernel n).Choices)
local notation "V" => R.family.path.levels
local notation "bare" => seed R u k h depth digit N v

omit [Fintype I] in
/-- Every ordinary face reads the predeclared finite history. At each step the
previous unmarked action, the complete ordinary source, all offsets and their
engineering weights are the ones in the original finite recursion. -/
theorem original (simple:G.Simple)(o:Loc G 1)(price:ℕ→Gear G→ℝ)
    (fund:FundedMarkedCoverRows.prices price R.kit)(engineering:I→ℕ)
    (j:ℕ)(live:j≤N)(x:I→ Cover)(S:Finset I)(f:Pen h S→L[ℝ]ℝ)(n:Side):
    (tuftV f (levelsO (Gears V R.metals.O engineering k N N j (bare) x) S)).1 n=
      WilsonMarkedFiniteIndependentHistory.moments R a tags N engineering (bare) (N-j) j x S f n:=by
  exact WilsonMarkedFiniteIndependentHistory.descend R a tags simple price fund
    (N:=N) (b:=N) le_rfl engineering k (bare) (lawful R u k h depth digit N v simple o)
    (N-j) j (by omega) x S f n

end YM.Integration.WilsonOriginalMicroscopicVerseSeed
end
