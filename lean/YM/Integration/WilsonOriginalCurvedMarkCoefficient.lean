import YM.Integration.WilsonOriginalProjectedTaylor
import YM.Comparison.RG02.Moving.Melt

/-! Read the full curved coefficient of a declared marked group field. -/
noncomputable section
namespace YM.Integration.WilsonOriginalCurvedMarkCoefficient
open Function Filter Comparison.RG02 Assembly Adjacent Moving Moving.Path Moving.Shift Work.G05
open scoped Topology BigOperators Classical ContDiff
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem smooth (F:ℝ×E→ℂ) (m r:ℕ) (C:UnitCost) (B:E):
    ContDiffAt ℝ ω (fun t=>ages (fun i x=>jet F (m+i) (1,x)) 0 r t (C.rating t) B) 0:=by
  have rating:C.rating 0≠0:=C.origin.trans_ne one_ne_zero
  have leg:ContDiffAt ℝ ω (fun t=>((1:ℝ),(C.rating t)⁻¹ • B)) 0:=
    contDiffAt_const.prodMk ((C.smooth.inv rating).smul contDiffAt_const)
  simp only [ages,cover,zpow_zero,Complex.ofReal_one,one_mul]
  apply ContDiffAt.sum
  intro i _
  exact ((Complex.ofRealCLM.contDiff.contDiffAt.comp _ C.here).pow i).mul
    ((Tensor.diag_smooth (Tensor.coeff F (m+i) 0) ω).contDiffAt.comp 0 leg)

theorem original (F:ℝ×E→ℂ) (m r:ℕ) (grade:GradeAt m F) (C:UnitCost) (e:ℕ) (he:e≤r) (B:E):
    motion (fun t=>(↑((C.rating t)^m)⁻¹:ℂ)*F (C.enter t,t • B)) (m+e)=
      born (fun i x=>jet F (m+i) (1,x)) C 0 r e B:=by
  let p:ℝ→ℝ×E:=fun t=>(C.enter t,t • B)
  let lin:ℝ→L[ℝ]E:=(ContinuousLinearMap.id ℝ ℝ).smulRight B
  have path:ContDiffAt ℝ ω p 0:=C.here.prodMk lin.contDiff.contDiffAt
  have origin:p 0=0:=Prod.ext C.borne (zero_smul ℝ B)
  let a:ℝ→ℂ:=fun t=>↑((C.rating t)^m)⁻¹
  have da:ContDiffAt ℝ ω a 0:=Complex.ofRealCLM.contDiff.contDiffAt.comp 0
    ((C.smooth.pow m).inv (pow_ne_zero m (C.origin.trans_ne one_ne_zero)))
  let cut:=blockTaylor (m+r) F
  let err:=a*((F-cut) ∘ p)
  have az:GradeAt 0 a:=⟨da,fun i hi=>by omega⟩
  have rest:=WilsonOriginalProjectedTaylor.remainder F (m+r) grade.smooth
  have tail:GradeAt (m+r+1) err:=by simpa only [zero_add] using az.mul (rest.coarse path origin)
  have dc:ContDiffAt ℝ ω (fun t=>a t*cut (p t)) 0:=
    da.mul ((blockTaylor_contDiff (m+r) F ω).contDiffAt.comp 0 path)
  have whole:(fun t=>(↑((C.rating t)^m)⁻¹:ℂ)*F (C.enter t,t • B))=
      fun t=>err t+a t*cut (p t):=by
    funext t
    change a t * F (p t) = a t * (F (p t)-cut (p t))+a t * cut (p t)
    ring
  rw [whole,madd tail.smooth dc]
  have flat:motion err (m+e)=0:=tail.jet_z (1:ℝ) (by omega)
  rw [flat,zero_add]
  let value:=fun t=>ages (fun i x=>jet F (m+i) (1,x)) 0 r t (C.rating t) B
  have eq:(fun t=>a t*cut (p t))=ᶠ[𝓝 0] fun t=>(t:ℂ)^m*value t:=by
    filter_upwards [C.bright] with t ht
    exact WilsonOriginalProjectedTaylor.ages F m r grade B t (C.rating t) ht.ne'
  rw [mgerm eq,mono_price (smooth F m r C B),if_pos (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rfl

end YM.Integration.WilsonOriginalCurvedMarkCoefficient
end
