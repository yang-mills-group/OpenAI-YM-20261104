import YM.Integration.WilsonPositionProgramTrialNativeHome

/-! A numerical salary for the complete home vector at fixed m and K, before N or period. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialStationHome
open Function Filter Finset Matrix Lattice Wilson RG RG.Supply Precision Source Labels Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato XSpace PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Power WilsonCoeffUV.Embroider
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank.PathCost
open WilsonPositionProgramTrialHomeDose (publicDose)
open WilsonPositionProgramTrialNativeHome (reporter)
open WilsonIndependentMatchedFiledIncome (charge plate)
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonOriginalPublicPlantedStableCredit (span)
open scoped BigOperators Topology Classical
variable {G:Gauge}{h D k u e:ℕ}
local notation "C" => Credit.leanC

def elapsed (L:Levels G)(m K:ℕ):ℝ:=L.S.scale K-L.S.scale m
def age (L:Levels G)(m K:ℕ):ℝ:=zz L m+elapsed L m K+(K-m:ℕ)

def chargeAt (L:Levels G)(Q:SealR G)(e:ℕ)(B Z:Credit)(m K:ℕ):ℝ:=
  (Fintype.card (Alma Q.F):ℝ)*(e+1)*(Fintype.card (Alma Q.F):ℝ)*B.buy (zz L m)*
    ((Real.exp (elapsed L m K))^Q.h*Z.buy (age L m K))

def mass (Q:SealR G)(e:ℕ)(b:Alma Q.F→PowerSeries ℝ):ℝ:=
  ∑s:Alma Q.F,∑j:Fin (e+1),‖coeff j.val (b s)‖

theorem dates {Q:SealR G}{w:Rails Q.h k u e}{H:Hol G}(X:CutsP H Q.ans Q.path w C C C C)
    (L:Levels G)(m K:ℕ)(levels:X.ax=L)(clock:X.vesselsC.y=zz L)(start:X.m=m)(stop:X.ceilC=K):
    span X X.i=elapsed L m K ∧ X.Age=age L m K:=by
  have duration:X.i=K-m:=by
    have day:X.m+X.i=K:=stop
    omega
  have delta:span X X.i=elapsed L m K:=by
    change X.ax.S.scale X.ceilC-X.ax.S.scale X.m=_
    rw [levels,start,stop]
    rfl
  refine ⟨delta,?_⟩
  change X.vesselsC.y X.m+span X X.i+(X.i:ℝ)=_
  rw [clock,start,delta,duration]
  rfl

def Seated (R:Run G)(Q:SealR G)(w:Rails Q.h k u e)(m K N:ℕ)
    (Y:TowerS G Q.D)(fuel:ℝ)(X:CutsP (hol G) Q.ans Q.path w C C C C):Prop:=
  X.ax=R.family.path.levels ∧ X.tx=R.metals.O ∧ X.m=m ∧ X.ceilC=K ∧ X.N=N ∧
    X.vesselsC.y=zz R.family.path.levels ∧ X.pt=Y ∧ X.fuel=fuel

theorem original (R:Run G)(W:Initialize G)(simple:G.Simple)(v:ℕ→Gear G→ℝ)
    (funded:FundedMarkedCoverRows.prices v R.kit)(fit:h<D)(rails:Rails h k u e)
    (d:ℕ)(kind:Bool)(dim:d<D)(cap:d≤k):
    let Q:=reporter (G:=G) fit
    let L:=R.family.path.levels
    ∃α:Alma (R.family.labels.level d)→ℝ,(∀i,0≤α i) ∧ ∃Z B:Credit,
    ∀ᶠ j:ℕ in atTop,∀m K N,j ≤ m → m ≤ K → K ≤ N →
    ∀(c:Verse (R.family.labels.level d))(s:ℝ),
    ∃X:CutsP (hol G) Q.ans Q.path rails C C C C,
      Seated R Q rails m K N (s • Shrine (plate (sectionAt R W kind d) dim) c) (|s| * charge e c α) X ∧
      ∀a:ℝ,(a • X.pt=centralL L R.metals.O N m K Q
          (PermuteLens L R.metals.O Q N m (publicDose Q X a))+a • X.springP X.i) ∧
        mass Q e (publicDose Q X a) ≤ chargeAt L Q e B Z m K*(|a| *(|s| *charge e c α)):=by
  intro Q L
  obtain ⟨α,nα,Z,B,sale⟩:=WilsonPositionProgramTrialNativeHome.original R W simple v funded fit rails
    d kind dim cap
  refine ⟨α,nα,Z,B,?_⟩
  filter_upwards [sale] with j source
  intro m K N jm mk kN c s
  obtain ⟨X,levels,chart,start,stop,top,clock,group,fuel,read,paid⟩:=source m K N jm mk kN c s
  obtain ⟨width,number⟩:=dates (Q:=Q) (w:=rails) X L m K levels clock start stop
  refine ⟨X,⟨levels,chart,start,stop,top,clock,group,fuel⟩,fun a=>⟨read a,?_⟩⟩
  let E:= (Fintype.card (Alma Q.F):ℝ)*B.buy (zz L m)*
    ((Real.exp (elapsed L m K))^h*Z.buy (age L m K)*(|a| *(|s| *charge e c α)))
  calc
    mass Q e (publicDose Q X a) ≤ ∑_s:Alma Q.F,∑_t:Fin (e+1),E:=
      Finset.sum_le_sum fun i _=>Finset.sum_le_sum fun t _=>by
        simpa only [E,width,number] using paid a t.val (Nat.le_of_lt_succ t.isLt) i
    _=chargeAt L Q e B Z m K*(|a| *(|s| *charge e c α)):=by
      simp [E,chargeAt,Q,reporter]
      ring

end YM.Integration.WilsonPositionProgramTrialStationHome
end
