import YM.Integration.WilsonPositionProgramTrialNativeHome

/-! Both compact source presentations enter the previously commissioned reporter on its fresh vacuum. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialPublicJointSourceFaculty
open Function Finset Matrix Lattice Wilson RG Precision Source Labels PhysicalNext.Repeat.Legato XSpace
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Power WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel.Mark
open WilsonPositionProgramTrialFittedLens (matrix)
open WilsonPositionProgramTrialAccrued (home)
open WilsonPositionProgramTrialReverseLens (received)
open WilsonIndependentMatchedFiledIncome (plate charge)
open WilsonIndependentMatchedNamedPair (sectionAt)
open scoped BigOperators Classical

variable {G:Gauge}{k u e d:ℕ}{H:Hol G}(Q:SealR G){w:Rails Q.h k u e}{E W B V:Credit}
variable (X:CutsP H Q.ans Q.path w E W B V)
local notation "L" => X.ax
local notation "O" => X.tx
local notation "K" => X.ceilC

def coordinate (P:TowerS G Q.D):Q.Rider:=
  tallyV L O Q.ans Q.path K k K X.m P

def measured (P:TowerS G Q.D):Q.Rider:=
  matrix (Wray L O Q.ans Q.path K X.m) (opal Q.F (spools L O K k Q.h X.m X.i P))

theorem inlet (R:Run G)(W':Initialize G)(s:Bool)(fit:d<Q.D)(c:Verse (R.family.labels.level d)):
    opal (R.family.labels.level d) (Shrine (plate (sectionAt R W' s d) fit) c)=c:=by
  cases s with
  | false => exact Shrine_read _ _ (freshly _ _ fit (R.makes.sections d) (FVAAlt2.Block.clothes R d))
  | true =>
    have a:=WilsonOriginalPivotWardSurvey.issued R W' d
    exact Shrine_read _ _ (freshly _ W'.hol fit a.1 a.2.1)

theorem original (R:Run G)(W':Initialize G)(s:Bool)(fit:d<Q.D)(cap:d≤k):
    ∃A:Alma (R.family.labels.level d)→ℝ,(∀i,0≤A i) ∧ ∃C:Credit,
      ∀c:Verse (R.family.labels.level d),
        let P:=Shrine (plate (sectionAt R W' s d) fit) c
        ∃Y:CutsP H Q.ans Q.path w E W B V,
          Y.L=X.L ∧ Y.L'=X.L' ∧ Y.m=X.m ∧ Y.i=X.i ∧ Y.N=K ∧ Y.pt=P ∧
          Y.fuel=charge e c A ∧ Y.tileP=coordinate Q X P ∧ home Q Y=measured Q X P ∧
          coordinate Q X P=opal Q.F P+boot L O Q.ans Q.path K k K X.m X.i
            (Silt Y.Ntop P) ∧
          received L O Q X.m K K (measured Q X P)=coordinate Q X P ∧
          P=centralL L O K X.m K Q (PermuteLens L O Q K X.m (measured Q X P))+
            Y.springP Y.i ∧
          (∀j<X.i,Spout L O K (X.m+j) Q.h k (Y.springP (j+1))=Y.springP j) ∧
          ∀t≤e,∀j≤X.i,∀r,Fruit 0 1 u ((Y.springP j).2 t r)
            (C.buy Y.Age*Real.exp (-(X.ax.S.scale K-X.ax.S.scale (X.m+j))/4)*charge e c A):=by
  obtain ⟨A,nn,initial⟩:=WilsonIndependentMatchedFiledIncome.named R W' s d fit cap e u
  obtain ⟨C,stable⟩:=WilsonPositionProgramTrialAccrued.issued H Q w E W B V
  refine ⟨A,nn,C,?_⟩
  intro c P
  obtain ⟨law,fare,roots⟩:=initial c
  let Y:=WilsonIndependentMatchedKernelResidual.diagonal X.L X.L' X.he X.m X.i K
    X.ha le_rfl P law (charge e c A) fare roots
  obtain ⟨coord,ret,born,step,wage⟩:=stable Y
  exact ⟨Y,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,coord,ret,born,step,wage⟩

end YM.Integration.WilsonPositionProgramTrialPublicJointSourceFaculty
