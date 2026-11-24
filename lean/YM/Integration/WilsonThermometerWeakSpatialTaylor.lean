import YM.Integration.WilsonThermometerWeakProbeTest

/-! A quantitative Taylor remainder for the continuum profile along each
actual displacement of a compact joint test. Its constants only use the indicated
finite derivative on the swept segment. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakSpatialTaylor
open Set Filter Function MeasureTheory Spec
open scoped Classical Topology ContDiff BigOperators
variable {E Y:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem line (F:E→Y){U:Set E}(openU:IsOpen U)(smooth:ContDiffOn ℝ ∞ F U)
    {z y:E}{t:ℝ}(inside:z+t • y∈U)(j:ℕ):
    iteratedDeriv j (fun s:ℝ=>F (z+s • y)) t =
      iteratedFDeriv ℝ j F (z+t • y) (fun _=>y):=by
  let a:E→Y:=fun x=>F (z+x)
  let V: Set E := (fun x:E=>z+x)⁻¹' U
  let L:ℝ→L[ℝ] E:=ContinuousLinearMap.toSpanSingleton ℝ y
  have hv:IsOpen V:=openU.preimage (by fun_prop)
  have ha:ContDiffOn ℝ ∞ a V:=smooth.comp (contDiff_const.add contDiff_id).contDiffOn (fun _ h=>h)
  have ht:L t∈V:=inside
  have hp:=hv.preimage L.continuous
  have left:=(iteratedFDerivWithin_of_isOpen (𝕜:=ℝ) (f:=a ∘ L) j hp) ht
  have right:=(iteratedFDerivWithin_of_isOpen (𝕜:=ℝ) (f:=a) j hv) ht
  have comp:=L.iteratedFDerivWithin_comp_right ha hv.uniqueDiffOn hp.uniqueDiffOn ht
    (i:=j) (WithTop.coe_le_coe.mpr le_top)
  rw [iteratedDeriv_eq_iteratedFDeriv]
  change iteratedFDeriv ℝ j (a ∘ L) t (fun _=>1)=_
  rw [←left,comp,right,ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have one:L 1=y:=one_smul ℝ y
  simp only [one]
  change iteratedFDeriv ℝ j (fun x:E=>F (z+x)) (t • y) _=_
  rw [iteratedFDeriv_comp_add_left]

def polynomial (F:E→Y)(z:E)(h:ℝ)(M:ℕ)(y:E):Y:=
  ∑k∈Finset.range (M+1),((k.factorial:ℝ)⁻¹*h^k) • iteratedFDeriv ℝ k F z (fun _=>y)

theorem remainder (F:E→Y){U:Set E}(openU:IsOpen U)(smooth:ContDiffOn ℝ ∞ F U)
    (M:ℕ){z y:E}{h:ℝ}(pos:0<h)(safe:∀t∈Icc (0:ℝ) h,z+t • y∈U)
    {B:ℝ}(deriv:∀t∈Icc (0:ℝ) h,‖iteratedFDeriv ℝ (M+1) F (z+t • y)‖≤B):
    ‖F (z+h • y)-polynomial F z h M y‖≤B*‖y‖^(M+1)*h^(M+1)/(M.factorial:ℝ):=by
  let g:ℝ→Y:=fun t=>F (z+t • y)
  have atg (t)(inside:t∈Icc (0:ℝ) h):ContDiffAt ℝ ∞ g t:=
    ((smooth _ (safe t inside)).contDiffAt (openU.mem_nhds (safe t inside))).comp t
      (show ContDiff ℝ ∞ (fun t:ℝ=>z+t • y) by fun_prop).contDiffAt
  have hd (k:ℕ)(t)(inside:t∈Icc (0:ℝ) h):
      iteratedDerivWithin k g (Icc 0 h) t=iteratedFDeriv ℝ k F (z+t • y) (fun _=>y):=
    (iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc pos) ((atg t inside).of_le
      (WithTop.coe_le_coe.mpr le_top)) inside).trans (line F openU smooth (safe t inside) k)
  have top (t)(inside:t∈Icc (0:ℝ) h):‖iteratedDerivWithin (M+1) g (Icc 0 h) t‖≤B*‖y‖^(M+1):=by
    rw [hd _ _ inside]
    have pay:=(iteratedFDeriv ℝ (M+1) F (z+t • y)).le_opNorm (fun _=>y)
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at pay
    exact pay.trans (mul_le_mul_of_nonneg_right (deriv _ inside) (by positivity))
  have cost:=taylor_mean_remainder_bound (a:=0) (b:=h) (x:=h) (n:=M) (f:=g) pos.le
    (fun t ht=>((atg t ht).of_le (by exact_mod_cast (WithTop.coe_le_coe.mpr le_top :
       (↑(M+1 : ℕ∞) : WithTop ℕ∞) ≤ ∞))).contDiffWithinAt)
    (right_mem_Icc.mpr pos.le) top
  have poly:taylorWithinEval g M (Icc 0 h) 0 h=polynomial F z h M y:=by
    rw [taylor_within_apply,polynomial]
    apply Finset.sum_congr rfl
    intro k _;rw [hd k 0 (left_mem_Icc.mpr pos.le)]
    simp
  simpa only [poly,sub_zero,g] using cost

end YM.Integration.WilsonThermometerWeakSpatialTaylor
end
