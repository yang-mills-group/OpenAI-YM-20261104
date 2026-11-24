import YM.Integration.WilsonSeparatedPrefixMovingMomentCut
import YM.Integration.WilsonSeparatedPrefixMovingBooking

/-! Every bounded common position moment receives its own true complete
counterterm on the same paid board. Its remaining product with the
previously enrolled exterior retains the full fixed-order separation gain. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingMomentBooking
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonSeparatedPrefixMovingCalendar (epoch)
open WilsonSeparatedPrefixMovingLateLaw (whole)
open WilsonSeparatedPrefixMovingWages (coupon)
open scoped BigOperators Topology Classical

variable {G:Gauge}{h D k n:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}

open WilsonSeparatedPrefixMovingBooking (Hearing)
open WilsonSeparatedPrefixMovingMomentCut (reported)
open WilsonSeparatedPrefixMovingCenterMoments (captured)

theorem original (H:Hol G)(T:SectionData F)(p:h<D)(arms:Fin (n+1) → SealR G)(Q:SealR G)
    (a u extra k' e:ℕ)(v:Rails h k (u+a) e)(E W K U V V' L L' Wn Ln:Credit)(order:a=h+Q.h+extra):
    ∃capture C₀ C₁ C₂:Credit,∀(torch:Torch H T p v E W K)(choir:ChorusLine H T p e E W U)
      (_same:choir.arch=torch.L),let R:=torch.L.V
      ∀(_arms:HorizonP H R W V' arms)(_near:SpringD R (capP arms) (u+a) (capP arms+2) Wn)
      (_dorm:Dormitory R (capP arms) (u+a) Ln)(t s m N:ℕ),
      R.anchor  ≤  t  →  t+s  ≤  m  →  m  ≤  N  →  capP arms  ≤  k  → 
      ∀(φ:Wilt arms)(X:Herit arms)(fees B:Fin (n+1) → ℝ)(Z δ:ℝ),
      PadRank R (t+s) m Z  →  Bough arms φ (paceT R.draws.S m (t+s)) Z B  → 
      R.tempC m m  ≤  δ  →  Sitting arms fees e δ X X  →  ∀ (ω:Lounge), (∀z:CellR,|ω z|  ≤  1)  → 
      let genuine:=captured R.draws R.paid φ X m (t+s) N D ω
      ∃Y:CutsP H T p v E W K U,
        Y.L=torch ∧ Y.L'=choir ∧ Y.vesselsC=R ∧ Y.N=N ∧ Y.m=t ∧ Y.i=s ∧ Y.pt=genuine ∧
        Y.fuel=max 0 (capture.buy Z*∏i,B i*fees i) ∧
        reported R.draws R.paid T p genuine m (t+s) t N k=
          (paceT R.draws.S m (t+s))^h • steep R.draws R.paid T p N (t+s) (m-(t+s)) Y.tileP ∧
        Y.springP s=genuine-Shrine Y.Ntop Y.tileP ∧
        Hearing (k':=k') Y Q V V' L L' C₀ C₁ C₂:=by
  obtain ⟨capture,_,enter⟩:=WilsonSeparatedPrefixMovingMomentCut.original H T p v E W K U V' Wn Ln arms
  obtain ⟨C₀,C₁,C₂,older⟩:=WilsonSeparatedPrefixMovingCapturedResidual.original H T p Q a u extra k' e
    v E W K U V V' L L' order
  refine ⟨capture,C₀,C₁,C₂,?_⟩
  intro torch choir same R roster spring dorm t s m N gate formed cutoff rank φ X fees B Z δ clock early fit claims ω bill
    genuine
  obtain ⟨Y,auth,quiet,cap,tm,si,pt,wage,reports,stable,_⟩:=enter torch choir same roster spring dorm t s m N
    gate formed cutoff rank φ X fees B Z δ clock early fit claims ω bill
  have eq:Y.vesselsC=R:=by change Y.L.L.V=torch.L.V;rw [auth]
  exact ⟨Y,auth,quiet,eq,cap,tm,si,pt,wage,reports,stable,older Y⟩

end YM.Integration.WilsonSeparatedPrefixMovingMomentBooking
