import YM.Integration.WilsonMatrixOriginalCurvatureExperiments
import YM.Integration.ActualOriginalFeeGrowth

/-! All thermal orders of the prescribed two curvature sources on their actual common gauge field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingMeasuredWardFees
open Function Finset MeasureTheory Lattice RG Wilson Precision Source
open PhysicalNext.Repeat.Legato MS MS.Land MS.Menus MS.Local.Physical MS.Theater
open WilsonReportingPrescribedOldFreeArms WilsonReportingPrescribedOldWardWallet
open WilsonMatrixOriginalCurvatureStock ActualOriginalDictionary
open WilsonMatrixTicketLanesNativePrices
open private continuous_operand from YM.Integration.WilsonReportingPrescribedOldWardPanel
open private null_grade from YM.Integration.WilsonMatrixOriginalIndependentCentering
open private phase pair from YM.Integration.WilsonMatrixOriginalCurvatureExperiments
open scoped Classical BigOperators
variable {G:Gauge} {B:Deck G} (R:Run G) (Q:Prescription B)
local notation "I" => B.BIndex (4:ℤ) 2

def matrix (clock:ℝ) (k:ℕ) (i j:I):ℂ :=
  oil (Q.fees 4 (WilsonReportingPrescribedOldAction.label B i).item) (curvature B j) k clock

def projected (clock:ℝ) (k:ℕ) (z:Stock B):Stock B :=
  (0,fun j=>∑i:I,z.2 i*matrix Q clock k i j)

private def value (i:I) (n:Side) (o:Site n) (U:Config G n) : ℂ :=
  ((dictionary R B).cylinder 4 2 i).O n o U

theorem column (simple:G.Simple) (i:I) (clock:ℝ) (k:ℕ) (n:Side) (o:Site n) (U V:Config G n) :
    let u:=WilsonReportingPrescribedOldAction.label B i
    ActualOriginalCalibratedColumns.weightedObservable R B Q u clock n o U k-
      ActualOriginalCalibratedColumns.weightedObservable R B Q u clock n o V k=
        ∑j:I,matrix Q clock k i j*(value R j n o U-value R j n o V) := by
  intro u
  let atom (g:Glyph B 4) (A:Config G n):ℂ:=((dictionary R B).cylinder g.size g.grade g.2.2).O n o A
  have expand (A:Config G n): ActualOriginalCalibratedColumns.weightedObservable R B Q u clock n o A k=
      ∑g:Glyph B 4,oil (Q.fees 4 u.item) g k clock*atom g A := by
    unfold ActualOriginalCalibratedColumns.weightedObservable WilsonComparison.Finite.Dictionary.calibrated
    rw [List.map_map,←Multiset.sum_coe,←Multiset.map_coe,Finset.coe_toList,←Finset.sum]
    rfl
  rw [expand U,expand V,←sum_sub_distrib]
  simp_rw [←mul_sub]
  apply WilsonMatrixOriginalCurvatureStock.sum B simple
  intro g low
  have s:g.grade=0:=congrArg Prod.snd (WilsonMatrixOriginalIndependentUnit.degree B (warehouse R) simple g low)
  have same:atom g U=atom g V:=congrArg Complex.ofReal (null_grade R B g.2.2 s n o U V)
  rw [same,sub_self,mul_zero]

theorem centered (simple:G.Simple) (z:Stock B) (clock:ℝ) (k:ℕ) (n:Side) (o:Site n) (U V:Config G n) :
    operand R Q z clock k n o U-operand R Q z clock k n o V=
    WilsonReportingPrescribedOldWardTree.stencil R (projected Q clock k z) n o U-
      WilsonReportingPrescribedOldWardTree.stencil R (projected Q clock k z) n o V := by
  unfold operand WilsonReportingPrescribedOldWardTree.stencil
  rw [add_sub_add_left_eq_sub,←sum_sub_distrib,←sum_sub_distrib]
  simp_rw [←mul_sub,column R Q simple]
  change (∑i:I,z.2 i*(∑j:I,matrix Q clock k i j*(value R j n o U-value R j n o V)))=
    ∑j:I,(∑i:I,z.2 i*matrix Q clock k i j)*(value R j n o U-value R j n o V)
  simp_rw [mul_sum,sum_mul,mul_assoc]
  exact sum_comm

theorem connected {N per:ℕ} (ν:Measure (Config G (R.family.side N per))) [IsProbabilityMeasure ν]
    (simple:G.Simple) (s t:Stock B) (clock:ℝ) (k l:ℕ) (o x:Site (R.family.side N per)) (χ:ℂ→L[ℝ]ℝ) :
    WilsonReportingPrescribedOldWardTree.moment R ν (fun U=>(operand R Q s clock k _ o U).re) (fun U=>χ (operand R Q t clock l _ x U))=
    WilsonReportingPrescribedOldWardTree.moment R ν
      (fun U=>(WilsonReportingPrescribedOldWardTree.stencil R (projected Q clock k s) _ o U).re)
      (fun U=>χ (WilsonReportingPrescribedOldWardTree.stencil R (projected Q clock l t) _ x U)) := by
  let n:=R.family.side N per
  have observed (z:Stock B) (h:ℕ) (y:Site n) (f:ℂ→L[ℝ]ℝ):
      let q:=projected Q clock h z
      (fun U=>f (operand R Q z clock h n y U))=fun U=>1*f (operand R Q q clock 0 n y U)+
        (f (operand R Q z clock h n y 1)-1*f (operand R Q q clock 0 n y 1)) := by
    intro q
    apply phase
    intro U
    rw [Complex.ofReal_one,one_mul]
    exact (centered R Q simple z clock h n y U 1).trans
      (WilsonReportingPrescribedOldWardTree.centered R Q simple q clock n y U 1).symm
  let a:=projected Q clock k s
  let b:=projected Q clock l t
  rw [show (fun U=>(operand R Q s clock k n o U).re)=_ from observed s k o Complex.reCLM,observed t l x χ]
  have ca:=Complex.continuous_re.comp (continuous_operand R Q a clock 0 o)
  have cb:=χ.continuous.comp (continuous_operand R Q b clock 0 x)
  calc
    _=(1:ℝ)^2*WilsonReportingPrescribedOldWardTree.moment R ν (fun U=>(operand R Q a clock 0 n o U).re)
        (fun U=>χ (operand R Q b clock 0 n x U)):=pair R N per ν _ _ ca cb 1 _ _
    _=_:=by rw [one_pow,one_mul]; exact WilsonReportingPrescribedOldWardTree.connected R Q ν simple a b clock o x χ

end YM.Integration.WilsonReportingMeasuredWardFees
