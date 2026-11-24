import YM.Integration.WilsonCapturedOriginalGrantClock
import YM.Integration.WilsonPositionProgramDatedClockBill

noncomputable section
namespace YM.Integration.WilsonCapturedOriginalClockUntiming
open Filter Function Finset PowerSeries Comparison.RG02 Comparison.RG02.Adjacent
open Comparison.RG02.Moving.Path Comparison.RG02.Valence PertExtension.Series
open RegulatorIR RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Booth
open RegulatorIR.Prim WilsonCapturedOriginalClockTaylor
open scoped BigOperators Classical Topology ContDiff
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def raw (F:ℝ×E→ℝ):Display E:=fun i x=>((Assembly.jet F (i+2) ((1:ℝ),x):ℝ):ℂ)

def observed (C:UnitCost)(F:ℝ×E→ℝ):Display E:=fun i x=>
  ((Assembly.jet (fun t=>Ribbon.fees C t*F (ray C x t)) (i+2) (1:ℝ):ℝ):ℂ)

private theorem affine {X Y:Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {k:ℤ}{f:X→Y}(df:Level k f)
    (L:E→L[ℝ] X)(a:X):Level k (fun x=>f (a+L x)):=by
  let g:X→Y:=fun x=>f (a+x)
  have hg:ContDiff ℝ ω g:=df.smooth.comp (contDiff_const.add contDiff_id)
  refine ⟨hg.comp L.contDiff,?_⟩
  intro j hj x
  change iteratedFDeriv ℝ j (g ∘ L) x=0
  rw [L.iteratedFDeriv_comp_right hg x (by exact_mod_cast le_top)]
  have hh:iteratedFDeriv ℝ j g (L x)=0:=by
    change iteratedFDeriv ℝ j (fun y=>f (a+y)) (L x)=0
    rw [iteratedFDeriv_comp_add_left,df.high j hj]
  rw [hh]
  ext v
  simp

theorem charges (F:ℝ×E→ℝ)(smooth:ContDiffAt ℝ ω F 0)(r:ℕ):
    Charge r (fun i=>(i+2:ℕ)) (raw F):=by
  intro i hi
  let L:E→L[ℝ] ℝ×E:=ContinuousLinearMap.inr ..
  let D:ℝ×E→ℂ:=Complex.ofRealCLM ∘ F
  have hd:ContDiffAt ℝ ω D 0:=Complex.ofRealCLM.contDiff.contDiffAt.comp _ smooth
  have h:=affine (Adjacent.levelJet hd (i+2)) L ((1:ℝ),(0:E))
  have shape:(fun x=>Assembly.jet D (i+2) (((1:ℝ),(0:E))+L x))=raw F i:=by
    funext x
    rw [←Assembly.jet_apply_left Complex.ofRealCLM F (i+2) (smooth.of_le le_top)]
    simp [raw,L]
  exact shape ▸ h

private theorem radialSmooth (C:UnitCost)(F:ℝ×E→ℝ)(r:ℕ)(A:E):
    ContDiffAt ℝ ω (radial C F r A) 0:=by
  have unit:ContDiffAt ℝ ω (fun t=>(C.rating t)⁻¹) 0:=C.smooth.inv (by simp [C.origin])
  apply ContDiffAt.sum
  intro i hi
  exact (C.here.pow i).mul (((YM.Tensor.diag_smooth (YM.Tensor.coeff F (i+2) 0) ω).contDiffAt).comp _
    (contDiffAt_const.prodMk (unit.smul contDiffAt_const)))

theorem filed (C:UnitCost)(F:ℝ×E→ℝ)(r:ℕ)(smooth:ContDiffAt ℝ ω F 0)
    (first:∀x:E,Assembly.jet F 1 (1,x)=0)(i:ℕ)(hi:i≤r)(A:E):
    observed C F i A=(coeff (i+2) (Prim.tale (fun t=>Ribbon.fees C t*F 0)):ℝ)+
      born (raw F) C 0 r i A:=by
  let g:=radial C F r A
  let s:=fun t=>Ribbon.fees C t*F 0
  have hs:ContDiffAt ℝ ω s 0:=((C.smooth.pow _).inv (by simp [C.origin])).mul contDiffAt_const
  have hg:ContDiffAt ℝ ω g 0:=radialSmooth C F r A
  have hprod:ContDiffAt ℝ ω ((fun t:ℝ=>t^2)*g) 0 := (contDiffAt_id.pow 2).mul hg
  have H:=issued C F r smooth first A (k:=i+2) (by omega)
  change _=Radial.jet (s+(fun t:ℝ=>t^2)*g) (i+2) 1 at H
  rw [←Prim.tale_jet,Prim.tale_add (hs.of_le le_top) (hprod.of_le le_top),map_add,
    Prim.tale_mul (f:=fun t:ℝ=>t^2) (g:=g) (contDiffAt_id.pow _) (hg.of_le le_top),
    Script.dictates (f:=fun t:ℝ=>t^2) (contDiffAt_id.pow _) (Script.predicts_pow _),
    coeff_X_pow_mul',if_pos (by omega),show i+2-2=i by omega,Prim.tale_jet (f:=g)] at H
  have f:(fun t=>ages (raw F) 0 r t (C.rating t) A)=Complex.ofRealCLM∘g:=by
    funext t
    simp only [ages,cover,zpow_zero,Complex.ofReal_one,one_mul,Function.comp_apply,Complex.ofRealCLM_apply,
      g,radial,raw,UnitCost.enter,Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_pow]
  change ((Assembly.jet _ _ _ :ℝ):ℂ)=_+motion _ _
  rw [H,Complex.ofReal_add,f]
  unfold motion
  rw [←Assembly.jet_apply_left Complex.ofRealCLM g i (hg.of_le le_top)]
  rfl

/-- Undo the actual clock after subtracting the literal two angular readings. -/
theorem original {E':Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (C:UnitCost)(F:ℝ×E→ℝ)(V:ℝ×E'→ℝ)(r:ℕ)
    (smooth:ContDiffAt ℝ ω F 0)(smooth':ContDiffAt ℝ ω V 0)
    (first:∀x:E,Assembly.jet F 1 (1,x)=0)(first':∀x:E',Assembly.jet V 1 (1,x)=0)
    (x y:E)(a b:E')(p:ℕ→ℕ→ℝ)
    (reading:∀i ≤ r,∀n ≤ i+2,
      ‖observed C F i ((n:ℝ) • x)-observed C F i ((n:ℝ) • y)-
        (observed C V i ((n:ℝ) • a)-observed C V i ((n:ℝ) • b))‖≤p i n)
    {j:ℕ}(hj:j≤r):
    ‖raw F j x-raw F j y-(raw V j a-raw V j b)‖≤
      WilsonPositionProgramDatedClockBill.cost C.inverseCurve 0 r j (·+2) p:=by
  let q:ℕ→ℤ:=fun i=>(i+2:ℕ)
  have up:Monotone q:=by intro i k hk; dsimp [q]; exact_mod_cast (Nat.add_le_add_right hk 2)
  have hf:Charge r q (raw F):=charges F smooth r
  have hv:Charge r q (raw V):=charges V smooth' r
  have H:=WilsonPositionProgramDatedClockBill.original C.inverseCurve 0 r j (·+2)
    (born (raw F) C 0 r) (born (raw V) C 0 r)
    (affordable 0 r hf C up) (affordable 0 r hv C up) x y a b p (by
      intro i hi n hn
      specialize reading i hi n hn
      rw [filed C F r smooth first i hi, filed C F r smooth first i hi,
        filed C V r smooth' first' i hi, filed C V r smooth' first' i hi] at reading
      simpa only [add_sub_add_left_eq_sub] using reading)
  rw [reverse 0 r hf C.rightInverse j hj, reverse 0 r hv C.rightInverse j hj] at H
  exact H

end YM.Integration.WilsonCapturedOriginalClockUntiming
end

