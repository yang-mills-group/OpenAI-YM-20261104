import YM.Integration.WilsonPositionProgramTrialPublicJointCapGround

/-! On the funded registered appointment the leading positive addresses of the
signed lower-grade change have the native quarter-power bound. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialPublicJointCapGroundFare
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


open PowerSeries Matrix WilsonCoeffUV.Bank.Carp

theorem course (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (fit:h<D)(rails:Rails h k u e)
    (capacity:capP (deck (G:=G) (fun _:Fin 1=>h) (fun _=>D) (fun _=>fit)) ≤ k):
    ∀ᶠj:ℕ in atTop,∃(l:Torch (hol G) (R.family.localSection h) fit rails CC CC CC)
      (a:ChorusLine (hol G) (R.family.localSection h) fit e CC CC CC),
      a.arch=l.L ∧ Weston l.L CC ∧ l.L.V.draws=L ∧ l.L.V.paid=O ∧ l.L.V.y=zz L ∧ l.L.V.anchor=j:=by
  obtain ⟨chartEq,floor,_,fees,_⟩:=funded
  let P:=deck (G:=G) (fun _:Fin 1=>h) (fun _=>D) (fun _=>fit)
  have awards:=reported (hol G) (primes G) floor fees
  filter_upwards [PortsTogether simple (chart_ok G) R.alloy.B.valid awards tendsto_id fit rails P
    (fun _=>rfl) capacity] with j campus
  obtain ⟨a,l,levels,ratio,clock,start,west,eq,_⟩:=campus
  refine ⟨l,a,eq,?_,?_,?_,?_,?_⟩
  · rwa [←eq]
  · exact eq ▸ levels
  · exact eq ▸ ratio.trans chartEq.symm
  · exact eq ▸ clock
  · exact eq ▸ start

open WilsonPositionProgramTrialFittedLens (ticket)
theorem ticketGround {H:Hol G}(Q:SealR G){A B:Credit}(T:Theatre H Q.ans Q.path e A B)(simple:G.Simple)
    (four:Q.h=4)(m K N:ℕ)(book:T.V.anchor ≤ m)(before:m ≤ K)(live:K ≤ N)(c:Verse Q.F)
    (i:Alma Q.F)(active:sheet Q.F i≠0):
    coeff 0 (ticket T.V.draws T.V.paid Q N m K c i)=coeff 0 (c i):=by
  let a:=street T.V.draws T.V.paid Q.ans Q.path N m (K-m) c
  have atGround (M:Wall Q.F):coeff 0 (matrix M a i)=(M*ᵥfun j=>coeff 0 (a j)) i:=by
    simp [matrix,Matrix.mulVec,dotProduct]
  change coeff 0 (matrix _ a i)=_
  rw [atGround,WilsonPhysicalSixWickRows.nonunit T (by omega) simple (before.trans live) book i active]
  exact WilsonPositionProgramTrialPublicJointFourGroundVote.written Q T simple four book before live c i active

open WilsonPositionProgramTrialStationHome (age)
def net (le:h ≤ hi)(fit:h<D)(m K k:ℕ)(c:Verse (R.family.labels.level h)):Verse (R.family.labels.level h):=
  projected L O (sectionSeal (R.family.localSection h) fit) m K k (high R W le fit c)-
    projected L O (sectionSeal (R.family.localSection h) fit) m K k (own R W fit c)

theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (size:h ≤ 6)(le:h ≤ hi)(fit:h<D)(rails:Rails h k u e)
    (capacity:capP (deck (G:=G) (fun _:Fin 1=>h) (fun _=>D) (fun _=>fit)) ≤ k):
    ∃(C:Credit)(A B:Alma (R.family.labels.level h)→ℝ),(∀i,0 ≤ A i) ∧ (∀i,0 ≤ B i) ∧
      ∀ᶠj:ℕ in atTop,∀m K,j ≤ m → m ≤ K → ∀(c:Verse (R.family.labels.level h))
        (i:Alma (R.family.labels.level h)),sheet (R.family.labels.level h) i≠0 →
        let S:=sectionSeal (R.family.localSection h) fit
        let b:=net R W le fit m K k c
        let fee:=C.buy (age L m K)*trailC (L).S m K*(charge e c A+charge e c B)
        ‖coeff 0 (received L O S m K K b i)‖ ≤ fee ∧ (h=4 → ‖coeff 0 (b i)‖ ≤ fee):=by
  obtain ⟨C,small⟩:=WilsonPositionProgramTrialPublicJointCapGround.written R W
    (H:=hol G) (R.family.localSection h) simple size fit le rails CC CC CC CC CC
  have sh:=WilsonPositionProgramTrialPublicJointCapFiling.issued R W le
  have sl:=WilsonOriginalPivotWardSurvey.issued R W h
  obtain ⟨A,an,top⟩:=WilsonIndependentMatchedFiledIncome.original _ fit W.hol sh.1 sh.2.1 rails.hk e u
  obtain ⟨B,bn,low⟩:=WilsonIndependentMatchedFiledIncome.original _ fit W.hol sl.1 sl.2.1 rails.hk e u
  refine ⟨C,A,B,an,bn,?_⟩
  filter_upwards [course R simple v funded fit rails capacity] with j desk
  obtain ⟨l,a,same,west,levels,reals,clock,start⟩:=desk
  intro m K late before c i active S b fee
  let P:=high R W le fit c
  let Q:=own R W fit c
  let X:=WilsonIndependentMatchedKernelResidual.diagonal l a same m (K-m) K (start.le.trans late)
    (by omega) (P-Q) ((top c).1.diff (low c).1) (charge e c A+charge e c B)
    (add_nonneg (top c).2.1 (low c).2.1)
    (fun t r ht=>((top c).2.2 t r ht).diff ((low c).2.2 t r ht) zero_le_one)
  have fdate:X.ceilC=K:=Nat.add_sub_of_le before
  have live:X.N=X.m+X.i:=fdate.symm
  have fa:X.ax=L:=levels
  have fo:X.tx=O:=reals
  have ff:X.m=m:=rfl
  have fn:X.N=K:=rfl
  have fp:X.pt=P-Q:=rfl
  have fv:Weston X.L.L CC:=west
  have fuel:X.fuel=charge e c A+charge e c B:=rfl
  have amount:=small X fv c fp i active
  have ages: X.Age=age L m K:=(WilsonPositionProgramTrialStationHome.dates (Q:=S) X L m K fa clock ff fdate).2
  have rate:X.ρ=trailC (L).S m K:=by change trailC X.ax.S X.m X.ceilC=_;rw [fa,ff,fdate]
  rw [ages,rate,fuel] at amount
  have difference:=linear X P Q (top c).1 (low c).1
  change projected X.ax X.tx S X.m X.ceilC k (P-Q)=
    projected X.ax X.tx S X.m X.ceilC k P-projected X.ax X.tx S X.m X.ceilC k Q at difference
  rw [fa,fo,ff,fdate] at difference
  have registered:projected L O S m K k (P-Q)=b:=difference
  have eq:=WilsonSurveyedEquationFrameMeasured.fitted X live
  change projected X.ax X.tx S X.m X.N k X.pt=ticket X.ax X.tx S X.N X.m X.N X.tileP ∧
    received X.ax X.tx S X.m X.N X.N (projected X.ax X.tx S X.m X.N k X.pt)=X.tileP at eq
  rw [fa,fo,ff,fn,fp,registered] at eq
  refine ⟨by rwa [eq.2],?_⟩
  intro four
  have read:=ticketGround S l.L simple four m K K (start.le.trans late) before le_rfl X.tileP i active
  rw [levels,reals,←eq.1] at read
  rwa [read]

end YM.Integration.WilsonPositionProgramTrialPublicJointCapGroundFare
