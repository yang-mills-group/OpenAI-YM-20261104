import YM.Integration.WilsonMeasuredCompanionTransport
import YM.Integration.WilsonThermometerOccupiedLinear
/-! Integration of a whole finite signed collection with its one original
Wilson denominator. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceFlatLine
open MeasureTheory Lattice RG Wilson PhysicalNext PhysicalNext.Repeat Legato
open WilsonThermometerUnitFilingCoarse
open private scale from YM.Integration.WilsonThermometerOccupiedLinear
open scoped Classical

def films (G:Gauge)(n:Side):Submodule ℂ (Config G n→ℂ) where
  carrier:=fun F=>Integrable F (prior G n)
  zero_mem':=integrable_zero ..
  add_mem' hf hg:=hf.add hg
  smul_mem' c F h:=show Integrable (c • F) (prior G n) from (show Integrable F (prior G n) from h).smul c

def ear {G:Gauge}(R:Run G)(N p f b:ℕ)(bf:b≤f):films G (R.family.side f p) →ₗ[ℂ] ℂ where
  toFun F:=reading R (N:=N) F.val b bf
  map_add' F K:=by
    have row:=WilsonMeasuredCompanionTransport.subtract R (N:=N) (F.val+K.val) K.val
      (F.property.add K.property) K.property bf
    have clean:(fun U=>(F.val+K.val) U-K.val U)=F.val:=by funext U;simp
    rw [clean] at row
    change reading R (N:=N) (F.val+K.val) b bf=_
    linear_combination -row
  map_smul' c F:=by
    change reading R (N:=N) (c • F.val) b bf=c*reading R (N:=N) F.val b bf
    unfold reading
    rw [scale R c F.val F.property bf]
    simp only [Pi.smul_apply,smul_eq_mul]
    ring

theorem assembled {G:Gauge}(R:Run G)(N p f b:ℕ)(bf:b≤f){I:Type*}(xs:List I)
    (S:I→films G (R.family.side f p))(F:Config G (R.family.side f p)→ℂ)
    (whole:∀U,F U=(xs.map (fun i=>(S i).val U)).sum):
    Integrable F (prior G _) ∧ reading R (N:=N) F b bf=(xs.map (fun i=>ear R N p f b bf (S i))).sum:=by
  have applied (ys:List I)(U:Config G (R.family.side f p)):
      ((ys.map S).sum).val U=(ys.map (fun i=>(S i).val U)).sum:=by
    induction ys with
    | nil=>rfl
    | cons i ts ih=>simp only [List.map_cons,List.sum_cons,Submodule.coe_add,Pi.add_apply,ih]
  have grouping:((xs.map S).sum).val=F:=funext fun U=>(applied xs U).trans (whole U).symm
  refine ⟨grouping ▸ (xs.map S).sum.property,?_⟩
  rw [←grouping]
  change (ear R N p f b bf) ((xs.map S).sum)=_
  rw [map_list_sum,List.map_map]
  rfl

end YM.Integration.WilsonMeasuredPublicEntranceFlatLine
end
