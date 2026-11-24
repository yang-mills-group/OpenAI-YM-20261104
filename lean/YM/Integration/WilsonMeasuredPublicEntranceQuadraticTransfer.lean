import YM.Integration.WilsonMeasuredPublicEntranceQuadraticVacuum
import YM.Integration.WilsonMeasuredPublicEntranceQuadraticSeparation
import YangMills.WilsonProof.NativeSupport.YM.XSpace.Influence

/-! A unit-preserving transfer on the true fourth engineering sector must carry each
directional quadratic contraction of two fixed fields. Only the actual second and
third moments at the indicated sites are tested. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceQuadraticTransfer
open Function Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Stab
open WilsonMeasuredPublicEntranceQuadraticGrid WilsonMeasuredPublicEntranceQuadraticSpan
open WilsonMeasuredPublicEntranceMarkedQuadratics WilsonMeasuredPublicEntranceQuadraticProducts
open WilsonMeasuredPublicEntranceQuadraticContraction
open scoped Classical BigOperators
variable {G:Gauge}

theorem positive {x y:E4}(apart:x≠y):strength x y≠0:=by
  apply Complex.ofReal_ne_zero.mpr
  have hn:0<‖x-y‖:=norm_pos_iff.mpr (sub_ne_zero.mpr apart)
  have h:=normal_pos
  positivity

theorem onto {T:Module.End ℂ (HFields G 4)}{x y:E4}(apart:x≠y)
    (P:∀l r:HFields G 4,bond G x y (T l).val (T r).val=bond G x y l.val r.val):
    Surjective T:=by
  apply LinearMap.injective_iff_surjective.mp
  intro l r eq
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply WilsonMeasuredPublicEntranceQuadraticSeparation.original apart (Submodule.sub_mem _ l.property r.property)
  intro q hq
  let v:HFields G 4:=⟨q,hq⟩
  change bond G x y (l.val-r.val) v.val=0
  rw [map_sub,LinearMap.sub_apply,←P l v,←P r v,eq,sub_self]

theorem original (simple:G.Simple)(T:Module.End ℂ (HFields G 4))
    (unit:T (leaf G 4)=leaf G 4)(a b:Axis)
    (U V:Plane ℝ)(sU:U.transpose=U)(sV:V.transpose=V)
    (heldU:T (marked G le_rfl U)=marked G le_rfl U)
    (heldV:T (marked G le_rfl V)=marked G le_rfl V)
    (P:∀x y:E4,x≠y→∀l r:HFields G 4,bond G x y (T l).val (T r).val=bond G x y l.val r.val)
    (M:∀x y z:E4,x≠y→x≠z→y≠z→∀l r w:HFields G 4,
      triangle G x y z (T l).val (T r).val (T w).val=triangle G x y z l.val r.val w.val):
    T (marked G le_rfl (product (lift (exterior a b)) U V))=
      marked G le_rfl (product (lift (exterior a b)) U V):=by
  let y:=WilsonMeasuredPublicEntranceQuadraticKernel.ray a b
  let x:=(2:ℝ) • y
  have y0:y≠0:=WilsonMeasuredPublicEntranceQuadraticKernel.nonzero a b
  have x0:x≠0:=smul_ne_zero (by norm_num: (2:ℝ)≠0) y0
  have xy:x-y=(1:ℝ) • y:=by simp [x,two_smul]
  have apart:x≠y:=by
    intro eq
    apply y0
    simpa only [one_smul] using xy.symm.trans (sub_eq_zero.mpr eq)
  let D:=lift (exterior a b)
  let A:=marked G (le_refl 4) U
  let B:=marked G (le_refl 4) V
  let Z:=marked G (le_refl 4) (product D U V)
  let L:=WilsonMeasuredPublicEntranceQuadraticVacuum.remainder (G:=G) (le_refl 4) x y 0 D U V
  let c:=2*strength x y*strength x 0
  have price:c≠0:=mul_ne_zero (mul_ne_zero (by norm_num) (positive apart)) (positive x0)
  have vac(w:HFields G 4):L w.val=L 1*bond G y 0 1 w.val:=by
    apply WilsonMeasuredPublicEntranceQuadraticVacuum.original simple a b one_ne_zero
      (by norm_num:(2:ℝ)≠0) one_ne_zero xy (by simp [x,y]) (by simp [y]) le_rfl U V sU sV _ w.property
  have current(w:HFields G 4):bond G y 0 Z.val (T w).val=bond G y 0 Z.val w.val:=by
    have measured:=M x y 0 apart x0 y0 A B w
    change T A=A at heldU
    change T B=B at heldV
    rw [heldU,heldV] at measured
    have neutral:=P y 0 y0 (leaf G 4) w
    rw [unit] at neutral
    have ledger:L (T w).val=L w.val:=by
      rw [vac (T w),vac w]
      exact congrArg (fun k:ℂ=>L 1*k) neutral
    change strength y 0*triangle G x y 0 A.val B.val (T w).val-c*bond G y 0 Z.val (T w).val=
      strength y 0*triangle G x y 0 A.val B.val w.val-c*bond G y 0 Z.val w.val at ledger
    rw [measured] at ledger
    exact mul_left_cancel₀ price (by linear_combination -ledger)
  change T Z=Z
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply WilsonMeasuredPublicEntranceQuadraticSeparation.original y0 (Submodule.sub_mem _ (T Z).property Z.property)
  intro w hw
  obtain ⟨v,ev⟩:=onto y0 (P y 0 y0) (⟨w,hw⟩:HFields G 4)
  change bond G y 0 ((T Z).val-Z.val) (⟨w,hw⟩:HFields G 4).val=0
  rw [←ev,map_sub,LinearMap.sub_apply,P y 0 y0,current,sub_self]
end YM.Integration.WilsonMeasuredPublicEntranceQuadraticTransfer

