import YM.Integration.WilsonIndependentMatchedFreshGroupFilm
import YM.Integration.WilsonIndependentMatchedPhysicalPeer

/-! A fresh Wilson word realizing a specified measured vector on its own K-cut
vacuum. All source coefficients are chosen by the transfer of this K chart.
The same raw compact section is used at every stencil site and torus. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedFreshCompact
open Function Filter Finset Matrix Lattice RG Wilson Source Labels Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato XSpace PertExtension
open WilsonCoeffUV.Blue
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Power WilsonCoeffUV.Embroider
open WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Wheel.Flooring WilsonCoeffUV.StableStrip
open WilsonIndependentMatchedOrdinaryProfile (stems)
open WilsonMarkedIndependentNormalizedElection (deck normalized)
open WilsonPositionProgramTrialFittedLens (ticket)
open WilsonPositionProgramTrialReverseLens (received)
open WilsonIndependentMatchedFreshGroupFilm (named)
open scoped BigOperators Classical Topology

variable {G:Gauge}{n h D H k u e:ℕ}(R:Run G)(W:Initialize G)
    (d:Fin (n+1) → ℕ)(fit:∀i,d i<D)
local notation "Q" => named R W (fun _ => false) d fit
local notation "L" => R.family.path.levels
local notation "O" => R.metals.O
local notation "CC" => Credit.leanC

theorem original (simple:G.Simple)(v:ℕ  →  Gear G  →  ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (big:h<H)(rails:Rails h k u e)(cap:capP (deck (G:=G) d (fun _=>D) fit) ≤ k):
    ∀ᶠ j:ℕ in atTop,∀ m K,j ≤ m → m ≤ K → ∀ b:Herit Q,
    let x := fun i=>received L O (Q i) m K K (b i)
    (∀i,ticket L O (Q i) K m K (x i)=b i) ∧
    ∀(φ:Wilt Q)(y:ℝ)(o:CellR)(side:Side),
      flash ((Ashore Q L O φ (normalized L O Q b m K) m K K y o).1 side)=
        ∏i,stems R W side false (fit i) (x i) (φ i) (paceT R.family.path.levels.S m K) y o (d i):=by
  filter_upwards [WilsonMarkedIndependentNormalizedElection.original R simple v funded big rails
    d (fun _=>D) fit cap] with j sale
  obtain ⟨_,chair,levels,clock,_,base,_,_,_,frames,_⟩:=sale
  intro m K late before b x
  constructor
  · intro i
    let bidder:AheadT (hol G) chair.L.V CC CC (Q i) CC:=(frames i).some
    have entered:bidder.p.f.arch.V.anchor ≤ m:=by rw [bidder.p.tap,base];exact late
    have field:=WilsonPositionProgramTrialReverseLens.field _ (Q i) bidder.p.f.arch entered before le_rfl (b i)
    simpa only [bidder.p.lands,bidder.p.modes,levels,clock] using field
  · intro φ y o side
    exact WilsonIndependentMatchedFreshGroupFilm.original R W (fun _=>false) d fit L O φ b m K y o side

end YM.Integration.WilsonIndependentMatchedFreshCompact
