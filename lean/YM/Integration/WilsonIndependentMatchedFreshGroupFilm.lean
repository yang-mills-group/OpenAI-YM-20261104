import YM.Integration.WilsonIndependentMatchedInheritedSheets
import YM.Integration.WilsonPositionProgramTrialHomeReprint

/-! The finite K-only vacuum prints its reissued reporting coordinate on the
actual normalized original or survey group stencil, on every torus. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedFreshGroupFilm
open Filter Function Finset Matrix Lattice RG Wilson PhysicalNext PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Embroider WilsonCoeffUV.Power
open WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Wheel.Flooring PertExtension
open XSpace Precision Source Labels Next.Foundations WilsonCoeffUV.StableStrip
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonIndependentMatchedFiledIncome (plate)
open WilsonIndependentMatchedCoverProfile (word)
open WilsonIndependentMatchedOrdinaryProfile (stems)
open WilsonIndependentMatchedReportedProxy (sectionSeal)
open WilsonMarkedIndependentNormalizedElection (normalized)
open WilsonPositionProgramTrialReverseLens (received)
open scoped BigOperators Classical Topology
variable {G:Gauge}{n D:ℕ}(P:Run G)(W:Initialize G)(kind:Fin (n+1)→Bool)(d:Fin (n+1)→ℕ)
    (dim:∀s,d s<D)
def named (s:Fin (n+1)):SealR G:=sectionSeal (sectionAt P W (kind s) (d s)) (dim s)
local notation "Q" => named P W kind d dim

theorem slot (L:Levels G)(O:ChartRatio G)(φ:Wilt Q)(b:Herit Q)(m K:ℕ)(y:ℝ)(o:CellR)
    (s:Fin (n+1))(side:Side):
    flash ((awaken Q L O φ (normalized L O Q b m K) m K K y o s).1 side)=
      stems P W side (kind s) (dim s) (received L O (Q s) m K K (b s))
        (φ s) (paceT L.S m K) y o (d s):=by
  change flash ((word (Shrine (Peaks L O (sectionAt P W (kind s) (d s)) (dim s) K K)
    (received L O (Q s) m K K (b s))) (φ s) (paceT L.S m K) y o (d s)).1 side)=_
  rw [Peak_initial]
  exact WilsonIndependentMatchedOrdinaryProfile.original P W side (kind s) (dim s) _ (φ s) _ y o (d s) (pace_pos ..)

theorem original (L:Levels G)(O:ChartRatio G)(φ:Wilt Q)(b:Herit Q)(m K:ℕ)(y:ℝ)(o:CellR)(side:Side):
    flash ((Ashore Q L O φ (normalized L O Q b m K) m K K y o).1 side)=
      ∏s,stems P W side (kind s) (dim s) (received L O (Q s) m K K (b s)) (φ s) (paceT L.S m K) y o (d s):=by
  let inlet:=awaken Q L O φ (normalized L O Q b m K) m K K y o
  have valid (s:Fin (n+1)):Auth (d s) (inlet s):=by
    let v:=received L O (Q s) m K K (b s)
    change Auth (d s) (word (Shrine (Peaks L O (sectionAt P W (kind s) (d s)) (dim s) K K) v)
      (φ s) (paceT L.S m K) y o (d s))
    rw [Peak_initial]
    obtain ⟨_,_,fund⟩:=WilsonIndependentMatchedFiledIncome.named P W (kind s) (d s) (dim s) le_rfl 0 0
    exact locale_val _ (Mer.placed (d s) (φ s) ((fund v).1) _ y) o
  change flash ((MassP G ℝ n inlet).1 side)=_
  rw [poly_agate n inlet d valid]
  exact Finset.prod_congr rfl (fun s _=>slot P W kind d dim L O φ b m K y o s side)
end YM.Integration.WilsonIndependentMatchedFreshGroupFilm
