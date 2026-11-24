import YM.Integration.WilsonIndependentConditionedPairFiledSemester

/-! Each arm's prescribed cutoff alternatives stay on one torch. Every left/right combination has the same conditional vacuum, public board and stop. The relative pivot salary is issued on each actual source Realm. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 450000
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedPairFour
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open RG.Supply Next.Foundations WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Bank.Mosaic PhysicalNext.Repeat.Legato XSpace.Rose XSpace.Cirrus XSpace
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonIndependentConditionedPairProbeSemester (Home)
open WilsonIndependentConditionedPairProbes (Prices)
open WilsonIndependentConditionedPairFiledSemester (Tested)
open WilsonIndependentMatchedFiledIncome (plate charge)
open WilsonIndependentMatchedNamedPair (sectionAt)
open scoped BigOperators Topology Classical
variable {G:Gauge}{h D e k u u₀:ℕ}
local notation "J" => Fin 2
local notation "C" => Credit.leanC

structure Assigned (R:Run G)(Q:J→SealR G)(own:∀s,Rails (Q s).h k u₀ e)
    (V:Realm G (e+1) C)(coins:Prices)(j:ℕ)(port:∀s,Home R (Q s) (own s) j)
    (ι:J→Type*)(submitted:(s:J)→ι s→TowerS G (Q s).D)(fare:(s:J)→ι s→ℝ)(u b host m K N:ℕ) where
  cuts (s:J) : ι s→CutsP (hol G) (Q s).ans (Q s).path (own s) C C C C
  lantern s i : (cuts s i).L=(port s).source
  chorus s i : (cuts s i).L'=(port s).origin
  levels s i : (cuts s i).ax=V.draws
  reset s i : (cuts s i).tx=V.paid
  home s i : (cuts s i).m=m
  birth s i : (cuts s i).ceilC=K
  vacuum s i : (cuts s i).N=N
  copy s i : (cuts s i).M=N
  marked s i : (cuts s i).b=K
  input s i : (cuts s i).pt=submitted s i
  same s i : (cuts s i).pt'=(cuts s i).pt
  price s i : (cuts s i).fuel=fare s i
  ahead s i : AheadT (hol G) (cuts s i).vesselsC C C (Q s) C
  heard (choose:(s:J)→ι s) : Tested Q own V (fun s=>cuts s (choose s)) coins u b host m K

theorem preparation (R:Run G)(simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (l d:J→ℕ)(admit:∀i,l i<d i)(e:ℕ):
    let Q:=deck (G:=G) l d admit
    ∀ᶠ j:ℕ in atTop,∀V:Realm G (e+1) C,V.draws=R.family.path.levels → V.paid=R.metals.O →
      V.y=zz R.family.path.levels → V.anchor=j → FramesR (hol G) V C C Q C:=by
  intro Q
  obtain ⟨chart,floors,_,fees,_⟩:=funded
  have awards:=reported (hol G) (primes G) floors fees
  filter_upwards [ambassadors simple (chart_ok G) R.alloy.B.valid awards tendsto_id e Q (fun _=>rfl)]
    with j fundedRooms
  intro V files clock age anchor
  exact fundedRooms V files (clock.trans chart) age anchor

theorem original (R:Run G)(simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (p:h<D)(rails:Rails h (2*k) u e)(l d:J→ℕ)(admit:∀i,l i<d i)
    (own:∀s,Rails (l s) k u₀ e)(b:ℕ)(reserve:u+b ≤ u₀)(depth:2*k ≤ b)
    (I:Initialize G)(ι:J→Type*)(survey:(s:J)→ι s→Bool):
    let Q:=deck (G:=G) l d admit
    let S:SectionData ((primes G).F h):=(primes G).T h
    ∃(coins:Prices)(A:(s:J)→ι s→Alma (R.family.labels.level (l s))→ℝ),
      (∀s i t,0 ≤ A s i t) ∧ ∀ᶠ j:ℕ in atTop,
        ∃(W:ChorusLine (hol G) S p e C C C)(Y:Torch (hol G) S p rails C C C)
          (port:(s:J)→Home R (Q s) (own s) j),
          W.arch=Y.L ∧ Y.L.V.draws=R.family.path.levels ∧ Y.L.V.paid=R.metals.O ∧
          Y.L.V.y=zz R.family.path.levels ∧ Y.L.V.anchor=j ∧
          FramesR (hol G) Y.L.V C C Q C ∧ HorizonP (hol G) Y.L.V C C Q ∧
          ∀(host m K N:ℕ),j ≤ host → host ≤ m → m ≤ K → K ≤ N →
          ∀c:(s:J)→ι s→Verse (R.family.labels.level (l s)),
            Nonempty (Assigned R Q own Y.L.V coins j port ι
              (fun s i=>Shrine (plate (sectionAt R I (survey s i) (l s)) (admit s)) (c s i))
              (fun s i=>charge e (c s i) (A s i)) u b host m K N):=by
  classical
  intro Q S
  choose A nn salary using fun (s:J)(i:ι s)=>WilsonIndependentConditionedPairProbeInput.named R I (survey s i)
    (l s) (d s) (admit s) (own s)
  obtain ⟨coins,semester⟩:=WilsonIndependentConditionedPairProbeSemester.original R simple v funded
    p rails l d admit own b reserve depth
  refine ⟨coins,A,nn,?_⟩
  filter_upwards [semester,preparation R simple v funded l d admit e] with j lane insurance
  obtain ⟨W,Y,level,reset,age,anchor,one,_,frame,horizon,ports,received⟩:=lane
  let port:=fun s:J=>(ports s).some
  refine ⟨W,Y,port,one,level,reset,age,anchor,frame,horizon,?_⟩
  intro host m K N live older cut vac c
  choose X torch choir files stamps home birth top compare upper field same amount using fun (s:J)(i:ι s)=>
    salary s i j m K N (port s) (live.trans older) cut vac (c s i)
  have draw (s:J)(i:ι s):(X s i).ax=Y.L.V.draws:=(files s i).trans level.symm
  have clock (s:J)(i:ι s):(X s i).tx=Y.L.V.paid:=(stamps s i).trans reset.symm
  refine ⟨⟨X,torch,choir,draw,clock,home,birth,top,compare,upper,field,same,amount,?_,?_⟩⟩
  · intro s i
    have reach:=insurance (port s).source.L.V (port s).levels (port s).reset (port s).age (port s).anchor s
    change AheadT (hol G) (X s i).L.L.V C C (Q s) C
    rw [torch]
    exact reach.some
  · intro pick ζ a base φ y t z o B gain room ht clearance sizes bounds
    exact WilsonIndependentConditionedPairProbeHearings.original Q own C C C C Y.L.V coins u b received
      (fun s=>X s (pick s)) host m K N (anchor.le.trans live) older cut vac
      (fun s=>draw s _) (fun s=>clock s _) (fun s=>home s _) (fun s=>birth s _) (fun s=>top s _)
      ζ a base φ y t z o B gain room ht clearance sizes bounds

end YM.Integration.WilsonIndependentConditionedPairFour
