import YM.Integration.WilsonMeasuredPublicEntranceFlatLine
import YM.Integration.WilsonSeparatedPrefixCanonicalClearConvolution

/-! A single finite line of original prior-denominated integrals at the actual held field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceHeldLine
open Finset MeasureTheory Lattice RG Wilson PhysicalNext PhysicalNext.Repeat Legato
open WilsonMeasuredPublicEntranceFlatLine (films)
open WilsonSeparatedPrefixCanonicalClearConvolution (readingAt)
open private plus scale from YM.Integration.WilsonThermometerOccupiedLinear
open scoped Classical

def ear {G:Gauge}(R:Run G)(N p f b:ℕ)(bf:b≤f)(W:Config G (R.family.side b p)):
    films G (R.family.side f p) →ₗ[ℂ] ℂ where
  toFun F:=readingAt R (N:=N) F.val bf W
  map_add' F K:=by
    change readingAt R (N:=N) (F.val+K.val) bf W=_
    unfold readingAt
    rw [plus R F.val K.val F.property K.property bf]
    exact mul_add .. 
  map_smul' c F:=by
    change readingAt R (N:=N) (c • F.val) bf W=c*readingAt R (N:=N) F.val bf W
    unfold readingAt
    rw [scale R c F.val F.property bf]
    change _*(c*_)=c*(_*_)
    ring

theorem original {G:Gauge}(R:Run G)(N p f b:ℕ)(bf:b≤f)(W:Config G (R.family.side b p)){I:Type*}(xs:List I)
    (S:I→films G (R.family.side f p))(F:Config G (R.family.side f p)→ℂ)
    (whole:∀U,F U=(xs.map (fun i=>(S i).val U)).sum):
    Integrable F (prior G _) ∧ readingAt R (N:=N) F bf W=(xs.map (fun i=>ear R N p f b bf W (S i))).sum:=by
  have applied (ys:List I)(U:Config G (R.family.side f p)):
      ((ys.map S).sum).val U=(ys.map (fun i=>(S i).val U)).sum:=by
    induction ys with
    | nil=>rfl
    | cons i ts ih=>simp only [List.map_cons,List.sum_cons,Submodule.coe_add,Pi.add_apply,ih]
  have grouping:((xs.map S).sum).val=F:=funext fun U=>(applied xs U).trans (whole U).symm
  refine ⟨grouping ▸ (xs.map S).sum.property,?_⟩
  rw [←grouping]
  change (ear R N p f b bf W) ((xs.map S).sum)=_
  rw [map_list_sum,List.map_map]
  rfl

end YM.Integration.WilsonOriginalMicroscopicEntranceHeldLine
end
