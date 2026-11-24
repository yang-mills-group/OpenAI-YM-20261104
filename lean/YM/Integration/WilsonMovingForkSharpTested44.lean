import YM.Integration.WilsonMovingForkSharpMomentMaster
import YM.Integration.WilsonSeparatedPrefixMovingPhasePolynomial

/-! The degree-four moving detector. The two independent inner directions,
and the direction and signed reflected profile read by the exterior, are
all evaluated on their own enrolled Mer section on the same course. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkSharpTested44
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonSeparatedPrefixMovingCalendar (epoch window)
open WilsonSeparatedPrefixMovingLateLaw (whole)
open WilsonSeparatedPrefixMovingWages (coupon)
open WilsonSeparatedPrefixMovingOwnDate (fee)
open WilsonCoeffUV.Cosmos.Polestar
open WilsonIndependentMovingRosterAllFineSeats (Elected Named)
open scoped BigOperators Topology Classical
local notation "C" => Credit.leanC
variable {G:Gauge}{h D k n height seats:ℕ}{H:Hol G}{F:Labels.Frame G h}{T:SectionData F}{p:h<D}

open WilsonMovingForkSharpMaster (Paid)
open WilsonCoeffUV.Mer.Patrol (BayV)
open WilsonSeparatedPrefixMovingMomentCut (reported)
open WilsonSeparatedPrefixMovingCenterMoments (captured)


variable {D':ℕ}
theorem ranks (M:Master H)(p:4<D):
  capP (fun _:Fin 2=>BayV M 4 D p)=8:=by norm_num [capP,asp,BayV,Fin.sum_univ_two]

def inner (M:Master H)(p:4<D):Fin 2 → SealR G:=fun _=>BayV M 4 D p

theorem original (M:Master H)(p:4<D)(pF:4<D')(u e:ℕ)(v:Rails 4 8 (u+16) e)
    (height4:4 ≤ height)(nearData:D ≤ seats)(farData:D' ≤ seats)(sensors:u+16 ≤ seats):
    ∃capture C₀ C₁ C₂:Credit,∀(torch:Torch H (M.T 4) p v C C C)(choir:ChorusLine H (M.T 4) p e C C C)
      (_same:choir.arch=torch.L),let R:=torch.L.V
      ∀(_sold:Elected M R height seats)(t s m N:ℕ),
      R.anchor  ≤  t  →  t+s  ≤  m  →  m  ≤  N  → 
      ∀(φ:Wilt (inner M p))(X:Herit (inner M p))(B:Fin 2 → ℝ)(Z:ℝ),
      PadRank R (t+s) m Z  →  Bough (inner M p) φ (paceT R.draws.S m (t+s)) Z B  → 
      ∀(k:ℕ)(axes:Fin k → Axis)(o:CellR),let ω:=WilsonSeparatedPrefixMovingCenterMoments.monomial o axes
      let genuine:=captured R.draws R.paid φ X m (t+s) N D ω
      ∃Y:CutsP H (M.T 4) p v C C C C,
        Y.L=torch ∧ Y.L'=choir ∧ Y.vesselsC=R ∧ Y.N=N ∧ Y.m=t ∧ Y.i=s ∧ Y.pt=genuine ∧
        Y.fuel=max 0 (capture.buy Z*∏i,B i*fee ((inner M p) i) e (X i)) ∧
        reported R.draws R.paid (M.T 4) p genuine m (t+s) t N 8=
          (paceT R.draws.S m (t+s))^4 • steep R.draws R.paid (M.T 4) p N (t+s) (m-(t+s)) Y.tileP ∧
        Y.springP s=genuine-Shrine Y.Ntop Y.tileP ∧ Paid Y (BayV M 4 D' pF) C₀ C₁ C₂:=by
  have en (i:Fin 2):Named M height seats ((inner M p) i):=⟨height4,nearData,rfl⟩
  have ex:Named M height seats (BayV M 4 D' pF):=⟨height4,farData,rfl⟩
  have cap:capP (inner M p)=8:=ranks M p
  obtain ⟨capture,C₀,C₁,C₂,purchase⟩:=WilsonMovingForkSharpMomentMaster.original M p (inner M p) (BayV M 4 D' pF) 16 u e v
    (by change (16:ℕ)=4+4+8;decide) (by decide) cap.le en ex (by omega) sensors
  refine ⟨capture,C₀,C₁,C₂,?_⟩
  intro torch choir same R sold t s m N gate formed top φ X B Z age spacing k axes o ω genuine
  exact purchase torch choir same sold t s m N gate formed top φ X B Z age spacing ω
    (WilsonSeparatedPrefixMovingCenterMoments.bounded o axes)

end YM.Integration.WilsonMovingForkSharpTested44
