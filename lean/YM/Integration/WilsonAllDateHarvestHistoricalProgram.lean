import YM.Integration.WilsonAllDateHarvestReopening
import YM.Integration.WilsonAllDateHarvestObservedReplay
import YM.Integration.WilsonAllDateHarvestFiledReplay
import YM.Integration.WilsonAllDateHarvestClearance

/-! On the original representation at the actual observation lattice, feed the
same old forecast to the existing signed physical cofactor and nuclear program.
The later labels are obtained by propagating the original early palette. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonAllDateHarvestHistoricalProgram

open Function Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Many RG05Readout.Address RG05Readout.Native RG05Readout.View RG05Readout.Records
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi
open PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station
open WilsonAllDateHarvestAffine WilsonAllDateHarvestPropagation WilsonAllDateHarvestStability
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical


open RG05Readout.Nuclear
variable {G:Gauge}{C:Family G}{n m t N per d k:ℕ}{Q fee:ℝ}

theorem original (tabs:Stock.Tabs C.path.levels) (o:Fin 3→Site (C.side n per)) (E:Fin 3→Motion)
    (s:Fin 3→ℕ) (q:ManyStem C o n→Body)(h:C.Makes)
    (P:(v:Fin 3)→Sight C (s v) per)(S:(v:Fin 3)→Emblems C (s v))(x:(v:Fin 3)→Palette C (s v))
    (roster:Census (Fin 3)) (nm:n ≤ m)(mt:m ≤ t)(tN:t ≤ N)
    (clear:Clearance o E s (headings o E q) roster m)
    (paid:WilsonAllDateHarvestHistoricalEntry.Captured o E s q h P S x roster nm mt tN d k Q fee):
    WilsonAllDateHarvestObservedReplay.Captured o E s q h P S (WilsonAllDateHarvestRebook.raised s S x m t)
      roster (nm.trans mt) tN d k Q fee := by
  unfold WilsonAllDateHarvestObservedReplay.Captured
  intro A J Y I T rows f F inc opened
  have rowEq:T=plants (m:=m) s P S x:=WilsonAllDateHarvestRebook.singleton s S x P m t
  have colEq:f=WilsonAllDateHarvestPhysical.columns o E s q S x m N:=
    WilsonAllDateHarvestRebook.columns s S x o E q m t N
  obtain ⟨L,run,initial,pay⟩:=paid
  obtain ⟨B,_,_,_⟩:=pay t (nm.trans mt) (le_refl t)
  refine ⟨L,run,?_,?_⟩
  · dsimp only [rows]
    rw [rowEq]
    refine initial.trans (funext fun U=>?_ )
    exact WilsonAllDateHarvestReopening.opening_at tabs o E s q roster nm mt clear (Y t)
      (imprint h A I (plants (m:=m) s P S x) t tN) B.legal U
  · intro i ni it α w
    dsimp only [rows,F]
    rw [rowEq,colEq]
    exact pay i ni it

end YM.Integration.WilsonAllDateHarvestHistoricalProgram
