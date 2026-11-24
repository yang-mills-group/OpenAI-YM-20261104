import YM.Integration.WilsonSeparatedPrefixMovingCenterMoments

/-! A positioned common-cell moment is a paid full tower on the original
captured course, with its complete projection, normalization and stable
residual. The common phase is tested before projection. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingMomentCut
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open scoped BigOperators Topology Classical

variable {G:Gauge}{d D k u e n:ℕ}{F:Labels.Frame G d}{H:Hol G}{T:SectionData F}{p:d<D}
    {v:Rails d k u e}{E W K U:Credit}

open WilsonSeparatedPrefixMovingCenterMoments (captured ink)

def reported (A:Levels G)(Ñ:ChartRatio G)(T:SectionData F)(p:d<D)(P:TowerS G D)
    (m b t N k:ℕ):Verse F:=
  (paceT A.S m b)^d • steep A Ñ T p N t (m-t) (opal F (spools A Ñ N k d t (b-t) P))

theorem report (L:Torch H T p v E W K){m b t N:ℕ}(P:TowerS G D)(bought:On k P)
    (gate:L.L.V.anchor  ≤  t)(tb:t  ≤  b)(bm:b  ≤  m)(mn:m  ≤  N):
    let A:=L.L.V.draws;let Ñ:=L.L.V.paid
    reported A Ñ T p P m b t N k=(paceT A.S m b)^d •
      steep A Ñ T p N b (m-b) (tallyV A Ñ T p N k b t P):=by
  intro A Ñ
  have hp:=TallOracle (N:=N) (i:=b-t) L gate (by omega) P bought
  have hh:t+(b-t)=b:=by omega
  dsimp only at hp
  rw [hh] at hp
  unfold reported
  rw [show opal _ (spools A Ñ N k d t (b-t) P)=street A Ñ T p N t (b-t)
    (tallyV A Ñ T p N k b t P) from hp,show m-t=b-t+(m-b) by omega,
    Street_refund L.L _ gate (by omega),hh]

theorem original (H:Hol G)(T:SectionData F)(p:d<D)(v:Rails d k u e)
    (E W K U V' W' L':Credit)(Q:Fin (n+1) → SealR G):
    ∃ C₀ C₁:Credit,∀(L:Torch H T p v E W K)(S:ChorusLine H T p e E W U)
      (_same:S.arch=L.L),let R:=L.L.V
      ∀(_home:HorizonP H R W V' Q),SpringD R (capP Q) u (capP Q+2) W'  → 
      Dormitory R (capP Q) u L'  →  ∀ j s m N,R.anchor  ≤  j  →  j+s ≤ m  →  m ≤ N  → 
      capP Q ≤ k  →  ∀(φ:Wilt Q)(X:Herit Q)(a b:Fin (n+1) → ℝ)(Z δ:ℝ),
      PadRank R (j+s) m Z  →  Bough Q φ (paceT R.draws.S m (j+s)) Z b  → 
      R.tempC m m ≤ δ  →  Sitting Q a e δ X X  →  ∀ (ω:Lounge), (∀z:CellR,|ω z| ≤ 1)  → 
      let top:=captured R.draws R.paid φ X m (j+s) N D ω
      let wage:=max 0 (C₀.buy Z* ∏i,b i*a i)
      ∃Y:CutsP H T p v E W K U,
        Y.L=L ∧ Y.L'=S ∧ Y.N=N ∧ Y.m=j ∧ Y.i=s ∧ Y.pt=top ∧ Y.fuel=wage ∧
        reported R.draws R.paid T p top m (j+s) j N k=
          (paceT R.draws.S m (j+s))^d • steep R.draws R.paid T p N (j+s) (m-(j+s)) Y.tileP ∧
        Y.springP s=top-Shrine Y.Ntop Y.tileP ∧
        (∀i<s,Spout R.draws R.paid N (j+i) d k (Y.springP (i+1))=Y.springP i) ∧
        ∀ lag ≤ e,∀i ≤ s,∀r:ℕ,Fruit 0 1 u ((Y.springP i).2 lag r)
          (C₁.buy Y.Age*Real.exp (-(R.draws.S.scale (j+s)-R.draws.S.scale (j+i))/4)*wage):=by
  obtain ⟨C₀,incoming⟩:=WilsonSeparatedPrefixMovingCenterMoments.original H Q E W V' W' L' e u D
  obtain ⟨C₁,pass⟩:=WilsonIndependentMatchedKernelResidual.original H T p v E W K U
  refine ⟨C₀,C₁,?_⟩
  intro L S same R home spring dorm j s m N jLive formed topAge allowed φ X a b Z δ room shape quiet dose ω fee top wage
  have nb:j ≤ j+s:=Nat.le_add_right .. 
  have bj:R.anchor ≤ j+s:=jLive.trans nb
  have endowment:=incoming R home spring dorm m (j+s) m N N φ X X a b Z δ
    bj formed le_rfl topAge topAge room shape quiet dose ω fee
  have ba:=formed.trans topAge
  have auth:=cruising R.draws R.hG R.green ba le_rfl
    (Hearth_enter home φ X (bj.trans ba) le_rfl (m:=m) (y:=paceT R.draws.S m (j+s)))
  have native:On k top:=Auth_on ((auth.tuft (ink D ω)).tall allowed)
  let Y:=WilsonIndependentMatchedKernelResidual.diagonal L S same j s N jLive (formed.trans topAge)
    top native wage (le_max_left _ _) fun w r hw=>(endowment w hw r).wax.more (le_max_right _ _)
  have reg:=pass Y
  refine ⟨Y,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_,reg.1,reg.2.1,reg.2.2⟩
  exact report L top native jLive nb formed topAge


end YM.Integration.WilsonSeparatedPrefixMovingMomentCut
