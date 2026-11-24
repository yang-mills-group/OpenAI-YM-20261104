import YM.Integration.WilsonPositionProgramTrialFittedLens
import YM.Integration.WilsonPositionProgramBlockedTrialBirth

/-! All registered real and imaginary measured directions share the elected house. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialFittedIntake
open Filter Function Finset Matrix Lattice Wilson RG RG.Supply PhysicalNext.Repeat.Legato Precision Source Labels
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Flooring WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonCoeffUV.Shard WilsonCoeffUV.Power WilsonCoeffUV.Soil
open WilsonMarkedIndependentNormalizedElection (deck normalized)
open WilsonPositionProgramTrialFittedLens (ticket)
open WilsonPositionProgramSubmittedCoordinates (submitted)
open scoped BigOperators Classical
variable {G:Gauge}(R:Run G){a h D e k u:ℕ}
variable (l d:Fin (a+1)→ℕ)(fit:∀i,l i<d i)

def convert (N m K:ℕ)(x:(i:Fin (a+1))→R.family.label (l i))(φ:Fin (a+1)→ℂ →L[ℝ] ℝ):
    Herit (deck (G:=G) l d fit):=fun i=>
  ticket R.family.path.levels R.metals.O (deck (G:=G) l d fit i) N m K (submitted R l d fit x φ i)

def Received (j:ℕ):Prop:=∀m K N:ℕ,j ≤ m → m ≤ K → K ≤ N →
  ∀(x:(i:Fin (a+1))→R.family.label (l i))(φ:Fin (a+1)→ℂ →L[ℝ] ℝ)(i:Fin (a+1)),
    let Q:=deck (G:=G) l d fit
    let A:=R.family.path.levels
    let O:=R.metals.O
    let v:=submitted R l d fit x φ i
    let z:=normalized A O Q (convert R l d fit N m K x φ) m N i
    steep A O (Q i).ans (Q i).path N m (K-m) z=v ∧
    centralL A O N m K (Q i) z=Shrine (Peaks A O (Q i).ans (Q i).path N K) v

theorem original (simple:G.Simple)(s:ℕ→Gear G→ℝ)(paid:FundedMarkedCoverRows.prices s R.kit)
    (big:h<D)(rails:Rails h k u e)(cap:capP (deck (G:=G) l d fit) ≤ k):
    ∀ᶠ j:ℕ in atTop,Received R l d fit j:=by
  filter_upwards [WilsonMarkedIndependentNormalizedElection.original R simple s paid big rails l d fit cap] with j sale
  obtain ⟨_,Y,level,cash,_,date,_,_,_,rows,_⟩:=sale
  intro m K N older before live x φ i
  let board:=(rows i).some
  have admitted:board.p.f.arch.V.anchor ≤ m:=by rw [board.p.tap,date];exact older
  have earned:=(WilsonPositionProgramTrialFittedLens.original _ _ board.p.f.arch admitted before live
    (submitted R l d fit x φ i)).2
  simpa only [normalized,convert,board.p.lands,board.p.modes,level,cash] using earned

end YM.Integration.WilsonPositionProgramTrialFittedIntake
