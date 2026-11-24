import YM.Integration.WilsonPositionProgramTrialPublicJointCapArrival

/-! The same signed high-on-low survey entrance on the already funded registered course. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialPublicJointCapRegistered
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Bank.PathCost
open WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider Source Source.Drops Labels XSpace
open WilsonSurveyedEquationFrameInlet (bank master loan price)
open WilsonIndependentMatchedFiledIncome (plate charge)
open WilsonMarkedIndependentNormalizedElection (deck)
open scoped Topology BigOperators Classical
variable {G : Gauge} (R : Run G) (W : Initialize G) {h hi D k u e : ℕ}
local notation "L" => R.family.path.levels
local notation "O" => R.metals.O
local notation "CC" => Credit.leanC


open WilsonIndependentMatchedReportedProxy (sectionSeal)
open WilsonIndependentMatchedFreshWhole (projected)
open WilsonPositionProgramTrialReverseLens (received)
open WilsonPositionProgramTrialFittedLens (matrix)
open WilsonPositionProgramTrialPublicJointCapFiling (sectionAt)
open WilsonSurveyedEquationFrameStability (course)

open WilsonPositionProgramTrialPublicJointCapArrival (high own linear)

theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (le:h≤hi)(fit:h<D)(rails:Rails h k u e)
    (capacity:capP (deck (G:=G) (fun _:Fin 1=>h) (fun _=>D) (fun _=>fit))≤k)(height:h≤k):
    ∃(C:Credit)(A B:Alma (R.family.labels.level h)→ℝ),(∀i,0≤A i) ∧ (∀i,0≤B i) ∧
      ∀ᶠ j:ℕ in atTop,∀m K,j ≤ m → m ≤ K → ∀c:Verse (R.family.labels.level h),
        let S:=sectionSeal (R.family.localSection h) fit
        let P:=high R W le fit c
        let Q:=own R W fit c
        let b:=projected L O S m K k P-projected L O S m K k Q
        ∃X:CutsP (hol G) (R.family.localSection h) fit rails CC CC CC CC,
          X.ax=L ∧ X.tx=O ∧ X.m=m ∧ X.ceilC=K ∧ X.N=K ∧ X.pt=P-Q ∧
          X.fuel=charge e c A + charge e c B ∧
          received L O S m K K b=X.tileP ∧
          X.springP X.i=P-Q-Shrine (plate (R.family.localSection h) fit) X.tileP ∧
          (∀i<X.i,Spout L O K (m+i) h k (X.springP (i+1))=X.springP i) ∧
          ∀t≤e,∀i≤X.i,∀r:ℕ,Fruit 0 1 u ((X.springP i).2 t r)
            (C.buy X.Age*Real.exp (-((L).S.scale K-(L).S.scale (m+i))/4)*
              (charge e c A + charge e c B)):=by
  obtain ⟨C,stable⟩:=WilsonIndependentMatchedKernelResidual.original
    (hol G) (R.family.localSection h) fit rails CC CC CC CC
  have sh:=WilsonPositionProgramTrialPublicJointCapFiling.issued R W le
  have sl:=WilsonOriginalPivotWardSurvey.issued R W h
  obtain ⟨A,an,top⟩:=WilsonIndependentMatchedFiledIncome.original _ fit W.hol sh.1 sh.2.1 height e u
  obtain ⟨B,bn,low⟩:=WilsonIndependentMatchedFiledIncome.original _ fit W.hol sl.1 sl.2.1 height e u
  refine ⟨C,A,B,an,bn,?_⟩
  filter_upwards [WilsonMarkedIndependentNormalizedElection.original R simple v funded fit rails
    (fun _:Fin 1=>h) (fun _=>D) (fun _=>fit) capacity] with j desk
  obtain ⟨a,l,levels,clock,_,start,joint,_⟩:=desk
  intro m K late before c S P Q b
  have p:=top c
  have q:=low c
  have full:On k (P-Q):=p.1.diff q.1
  let X:=WilsonIndependentMatchedKernelResidual.diagonal l a joint m (K-m) K
    (start.le.trans late) (by omega) (P-Q) full (charge e c A+charge e c B)
    (add_nonneg p.2.1 q.2.1) (fun t r ht=>(p.2.2 t r ht).diff (q.2.2 t r ht) zero_le_one)
  have date:X.ceilC=K:=Nat.add_sub_of_le before
  have timed:X.N=X.m+X.i:=date.symm
  have print:X.Ntop=plate (R.family.localSection h) fit:=by
    change Peaks l.L.V.draws l.L.V.paid (R.family.localSection h) fit K X.ceilC=_
    rw [date,Peak_initial]
    rfl
  have axes:X.ax=L:=levels
  have reals:X.tx=O:=clock
  have fm:X.m=m:=rfl
  have fn:X.N=K:=rfl
  have field:X.pt=P-Q:=rfl
  have nets:=linear X P Q p.1 q.1
  change projected X.ax X.tx S X.m X.ceilC k (P-Q)=
    projected X.ax X.tx S X.m X.ceilC k P-projected X.ax X.tx S X.m X.ceilC k Q at nets
  rw [axes,reals,fm,date] at nets
  have vote:received L O S m K K b=X.tileP:=by
    have quoted:received X.ax X.tx S X.m X.N X.N (projected X.ax X.tx S X.m X.N k X.pt)=X.tileP:=
      (WilsonSurveyedEquationFrameMeasured.fitted X timed).2
    rwa [axes,reals,fm,fn,field,nets] at quoted
  obtain ⟨dropped,next,bill⟩:=stable X
  have reissued:Shrine X.Ntop X.tileP=Shrine (plate (R.family.localSection h) fit) X.tileP:=
    congrArg (fun A=>Shrine A X.tileP) print
  have held:=dropped.trans (congrArg₂ (fun a b:TowerS G D=>a-b) field reissued)
  refine ⟨X,axes,reals,fm,date,fn,field,rfl,vote,held,?_,?_⟩
  · intro i ix
    have go:=next i ix
    rwa [axes,reals,fn,fm] at go
  · intro t te i ix r
    have fee:=bill t te i ix r
    change Fruit 0 1 u _ (C.buy X.Age*Real.exp (-(l.L.V.draws.S.scale X.ceilC-
      l.L.V.draws.S.scale (m+i))/4)*(charge e c A+charge e c B)) at fee
    rwa [levels,date] at fee

end YM.Integration.WilsonPositionProgramTrialPublicJointCapRegistered
