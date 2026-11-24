import YM.Integration.WilsonIndependentConditionedPairProbeInput
import YM.Integration.WilsonIndependentConditionedPairProbeHearings

/-! Two literal, independently specified finite-section fields on the original elected hierarchy. Their complete basis salaries and chronological credits are chosen before the common ultraviolet cutoff and before all placements. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedPairFiledSemester
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open RG.Supply Next.Foundations WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Bank.Ticket
open PhysicalNext.Repeat.Legato XSpace.Rose XSpace.Cirrus XSpace
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonIndependentConditionedPairProbeSemester (Home)
open WilsonIndependentConditionedPairProbes (Prices charge)
open WilsonIndependentConditionedBankAxes (Cuts)
open WilsonIndependentMatchedPivotSeat (film)
open WilsonIndependentMatchedCoveredSeats (seat)
open WilsonIndependentMatchedPivotStop (Hearing)
open WilsonIndependentMatchedFiledIncome (plate)
open WilsonIndependentMatchedNamedPair (sectionAt)
open scoped BigOperators Topology Classical
variable {G:Gauge}{h D e k u u₀:ℕ}
local notation "J" => Fin 2
local notation "C" => Credit.leanC

def Tested (Q:J→SealR G)(own:∀i,Rails (Q i).h k u₀ e)(V:Realm G (e+1) C)
    (X:Cuts (H:=hol G) Q own C C C C)(coins:Prices)(u b host m K:ℕ):Prop:=
  ∀(ζ:ℝ)(a:J→ℝ)(_base:(s:J)→Alma (Q s).F)(φ:(s:J)→Rarity (Q s).D)
    (y t z:ℝ)(o:CellR)(B:J→ℝ),
    ζ ≤ 1/4 → ((∑s,(Q s).h:ℕ):ℝ)+ζ < b → 0<t →
    (∀s s',s≠s'→ClearDay (φ s) (φ s') t) → (∀s,radiusH (φ s) 1 y ≤ z) →
    (∀s,Amplitude (φ s) (B s)) →
    let Δ:=fun s:J=>seat (X s) (a s) (φ s) y o (X s).i
    let P:=fun (s:J)(j:Alma (Q s).F)=>film (X s) j 0 (φ s) y o (X s).i
    let fee:=charge Q own C C C C V X coins u b host m K ζ a B t z
    Hearing (X 0) (Δ 0) (Δ 1) host u (fee (true,true)) ∧
      (∀j,Hearing (X 1) (Δ 0) (P 1 j) host u (fee (true,false))) ∧
      (∀j,Hearing (X 0) (P 0 j) (Δ 1) host u (fee (false,true)))

theorem original (R:Run G)(simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (p:h<D)(rails:Rails h (2*k) u e)(l d:J→ℕ)(admit:∀i,l i<d i)
    (own:∀i,Rails (l i) k u₀ e)(b:ℕ)(reserve:u+b ≤ u₀)(depth:2*k ≤ b)
    (I:Initialize G)(survey:J→Bool):
    let Q:=deck (G:=G) l d admit
    let S:SectionData ((primes G).F h):=(primes G).T h
    ∃(coins:Prices)(A:(i:J)→Alma (R.family.labels.level (l i))→ℝ),
      (∀i s,0 ≤ A i s) ∧ ∀ᶠ j:ℕ in atTop,
        ∃(W:ChorusLine (hol G) S p e C C C)(Y:Torch (hol G) S p rails C C C)
          (port:(s:J)→Home R (Q s) (own s) j),
          W.arch=Y.L ∧ Y.L.V.draws=R.family.path.levels ∧ Y.L.V.paid=R.metals.O ∧
          Y.L.V.y=zz R.family.path.levels ∧ Y.L.V.anchor=j ∧
          FramesR (hol G) Y.L.V C C Q C ∧ HorizonP (hol G) Y.L.V C C Q ∧
          ∀(host m K N:ℕ),j ≤ host → host ≤ m → m ≤ K → K ≤ N →
          ∀c:(s:J)→Verse (R.family.labels.level (l s)),
            ∃X:Cuts (H:=hol G) Q own C C C C,
              (∀s,(X s).L=(port s).source ∧ (X s).L'=(port s).origin ∧
                (X s).ax=Y.L.V.draws ∧ (X s).tx=Y.L.V.paid ∧
                (X s).m=m ∧ (X s).ceilC=K ∧ (X s).N=N ∧ (X s).M=N ∧ (X s).b=K ∧
                (X s).pt=Shrine (plate (sectionAt R I (survey s) (l s)) (admit s)) (c s) ∧
                (X s).pt'=(X s).pt ∧ (X s).fuel=WilsonIndependentMatchedFiledIncome.charge e (c s) (A s)) ∧
              Tested Q own Y.L.V X coins u b host m K:=by
  classical
  intro Q S
  choose A nn salary using fun s:J=>WilsonIndependentConditionedPairProbeInput.named R I (survey s)
    (l s) (d s) (admit s) (own s)
  obtain ⟨coins,original⟩:=WilsonIndependentConditionedPairProbeSemester.original R simple v funded
    p rails l d admit own b reserve depth
  refine ⟨coins,A,nn,?_⟩
  filter_upwards [original] with j lane
  obtain ⟨W,Y,level,reset,age,anchor,one,_,frame,horizon,ports,received⟩:=lane
  let port:=fun s:J=>(ports s).some
  refine ⟨W,Y,port,one,level,reset,age,anchor,frame,horizon,?_⟩
  intro host m K N live older cut vac c
  choose X xTorch xCh xLevel xReset home birth top comparison near field field' amount using fun s:J=>
    salary s j m K N (port s) (live.trans older) cut vac (c s)
  have draw (s:J):(X s).ax=Y.L.V.draws:=(xLevel s).trans level.symm
  have stamp (s:J):(X s).tx=Y.L.V.paid:=(xReset s).trans reset.symm
  refine ⟨X,fun s=>⟨xTorch s,xCh s,draw s,stamp s,home s,birth s,top s,comparison s,near s,
    field s,field' s,amount s⟩,?_⟩
  intro ζ a base φ y t z o B gain room ht clearance sizes bounds
  exact WilsonIndependentConditionedPairProbeHearings.original Q own C C C C Y.L.V coins u b received
    X host m K N (anchor.le.trans live) older cut vac draw stamp home birth top
    ζ a base φ y t z o B gain room ht clearance sizes bounds

end YM.Integration.WilsonIndependentConditionedPairFiledSemester
