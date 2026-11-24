import YM.Integration.WilsonSeparatedPrefixMovingMomentBooking
import YM.Integration.WilsonSeparatedPrefixMovingBookedMaster

/-! On the enrolled common Mer course, each finite phase moment has its
own reported subtracted field and an actual earlier fixed-exterior
hearing. The angular source and both kinetic charts are unchanged. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingMomentMaster
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

open WilsonSeparatedPrefixMovingBookedMaster (Paid)
open WilsonSeparatedPrefixMovingMomentCut (reported)
open WilsonSeparatedPrefixMovingCenterMoments (captured)

theorem original (M:Master H)(p:h<D)(arms:Fin (n+1) → SealR G)(Q:SealR G)(a u e:ℕ)
    (v:Rails h k (u+a) e)(exterior:a=h+Q.h+k)(covered:capP arms  ≤  k)
    (entered:∀i,Named M height seats (arms i))(far:Named M height seats Q)
    (rank:capP arms+2  ≤  seats)(derivatives:u+a  ≤  seats):
    ∃capture C₀ C₁ C₂:Credit,∀(torch:Torch H (M.T h) p v C C C)(choir:ChorusLine H (M.T h) p e C C C)
      (_same:choir.arch=torch.L),let R:=torch.L.V
      ∀(_sold:Elected M R height seats)(t s m N:ℕ),
      R.anchor  ≤  t  →  t+s  ≤  m  →  m  ≤  N  → 
      ∀(φ:Wilt arms)(X:Herit arms)(B:Fin (n+1) → ℝ)(Z:ℝ),
      PadRank R (t+s) m Z  →  Bough arms φ (paceT R.draws.S m (t+s)) Z B  →  ∀(ω:Lounge), (∀z:CellR,|ω z|  ≤  1)  → 
      let genuine:=captured R.draws R.paid φ X m (t+s) N D ω
      ∃Y:CutsP H (M.T h) p v C C C C,
        Y.L=torch ∧ Y.L'=choir ∧ Y.vesselsC=R ∧ Y.N=N ∧ Y.m=t ∧ Y.i=s ∧ Y.pt=genuine ∧
        Y.fuel=max 0 (capture.buy Z*∏i,B i*fee (arms i) e (X i)) ∧
        reported R.draws R.paid (M.T h) p genuine m (t+s) t N k=
          (paceT R.draws.S m (t+s))^h • steep R.draws R.paid (M.T h) p N (t+s) (m-(t+s)) Y.tileP ∧
        Y.springP s=genuine-Shrine Y.Ntop Y.tileP ∧ Paid Y Q C₀ C₁ C₂:=by
  obtain ⟨capture,C₀,C₁,C₂,issued⟩:=WilsonSeparatedPrefixMovingMomentBooking.original H (M.T h) p arms Q
    a u k (k+Q.h) e v C C C C C C C C C C exterior
  refine ⟨capture,C₀,C₁,C₂,?_⟩
  intro torch choir same R sold t s m N gate formed cut φ X B Z clock seatsNear ω bill genuine
  obtain ⟨roster,⟨external⟩⟩:=WilsonIndependentMovingRosterAllFineSeats.roster sold arms Q entered far
  let δ:=max 0 (R.tempC m m)
  have stipend:Sitting arms (fun j=>fee (arms j) e (X j)) e δ X X:=
    ⟨fun j=>Finset.sum_nonneg fun _ _=>Finset.sum_nonneg fun _ _=>norm_nonneg _,
     fun j=>WilsonSeparatedPrefixMovingMiddleIncome.own (arms j) e (X j) δ (le_max_left ..)⟩
  obtain ⟨Y,hl,hv,realm,cutoff,first,span,actual,income,report,stable,hear⟩:=
    issued torch choir same roster (sold.spring _ _ _ (by omega) rank derivatives)
      (sold.dorm (capP arms) (u+a) (by omega) derivatives) t s m N gate formed cut covered φ X _ B Z δ
      clock seatsNear (le_max_right ..) stipend ω bill
  refine ⟨Y,hl,hv,realm,cutoff,first,span,actual,income,report,stable,?_⟩
  have mark:PassportC H Y.vesselsC Q C C:=realm.symm ▸ external
  have sale:Elected M Y.vesselsC height seats:=realm.symm ▸ sold
  dsimp only [Paid]
  intro older gate' stop
  exact hear mark (sale.spring (k+Q.h) u a (by omega) (by omega) (by omega))
    (sale.dorm (k+Q.h) u (by omega) (by omega)) (sale.dorm (k+Q.h) (u+a) (by omega) derivatives)
    older gate' stop le_rfl

end YM.Integration.WilsonSeparatedPrefixMovingMomentMaster
