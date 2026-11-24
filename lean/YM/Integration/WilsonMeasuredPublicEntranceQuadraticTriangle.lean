import YM.Integration.WilsonMeasuredPublicEntranceQuadraticBonds

/-! Each connected trilinear measurement uses the same colour on all three quadratic
insertions. The scalar is the original Lie dimension, including on repeated legs. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceQuadraticTriangle
open Maxwell Maxwell.Free Maxwell.Wick
open WilsonMeasuredPublicEntranceQuadraticGrid WilsonMeasuredPublicEntranceMarkedQuadratics
open WilsonMeasuredPublicEntranceQuadraticKernel WilsonMeasuredPublicEntranceQuadraticBonds
open WilsonMeasuredPublicEntranceQuadraticWick
open scoped Classical BigOperators
variable {G:Gauge}{d:ℕ}

theorem original {x y z:E4}(a b:Axis){s t u:ℝ}(hs:s≠0)(ht:t≠0)(hu:u≠0)
    (xy:x-y=s • ray a b)(xz:x-z=t • ray a b)(yz:y-z=u • ray a b)
    (hd:4≤d)(i i' j j' k k':Six):
    triangle G x y z (tile hd i i').val (tile hd j j').val (tile hd k k').val=
      (G.lieDim:ℂ)*cycle (beamK a b x y) (beamK a b x z) (beamK a b y z) i i' j j' k k':=by
  have hx:x≠y:=fun h=>(smul_ne_zero hs (nonzero a b)) (xy.symm.trans (sub_eq_zero.mpr h))
  have hy:x≠z:=fun h=>(smul_ne_zero ht (nonzero a b)) (xz.symm.trans (sub_eq_zero.mpr h))
  have hz:y≠z:=fun h=>(smul_ne_zero hu (nonzero a b)) (yz.symm.trans (sub_eq_zero.mpr h))
  change triangle G x y z (∑n:G.ColorIndex,letter (factor n i)*letter (factor n i'))
    (∑n:G.ColorIndex,letter (factor n j)*letter (factor n j'))
    (∑n:G.ColorIndex,letter (factor n k)*letter (factor n k'))=_
  simp only [map_sum,LinearMap.sum_apply,WilsonMeasuredPublicEntranceQuadraticWick.original hx hy hz]
  have column (v w r:G.ColorIndex):
      cycle (fun l m=>linkEntry (x,l) (y,m)) (fun l m=>linkEntry (x,l) (z,m))
        (fun l m=>linkEntry (y,l) (z,m)) (factor v i) (factor v i') (factor w j)
        (factor w j') (factor r k) (factor r k')=
      if v=w then (if v=r then cycle (beamK a b x y) (beamK a b x z) (beamK a b y z)
        i i' j j' k k' else 0) else 0:=by
    by_cases h:v=w
    · subst w
      by_cases eq:v=r <;> simp [cycle,WilsonMeasuredPublicEntranceQuadraticBonds.edge a b hs xy,
        WilsonMeasuredPublicEntranceQuadraticBonds.edge a b ht xz,WilsonMeasuredPublicEntranceQuadraticBonds.edge a b hu yz,eq]
    simp [cycle,WilsonMeasuredPublicEntranceQuadraticBonds.edge a b hs xy,h]
  simp [column,Gauge.ColorIndex]
end YM.Integration.WilsonMeasuredPublicEntranceQuadraticTriangle

