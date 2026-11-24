import YM.Integration.WilsonPositionProgramThermalPolar
import YM.Analysis.SmoothJets

/-! The centered radial jet of a nonlinear chart reads unit-thermal parent directions. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionProgramAngularChart
open Function Finset
open WilsonPositionProgramThermalPolar Comparison.RG02
open scoped Classical BigOperators ContDiff
variable {B E:Type*}[NormedAddCommGroup B][NormedSpace ℝ B][NormedAddCommGroup E][NormedSpace ℝ E]

def chart (g:B→E)(p:ℝ×B):ℝ×E:=(p.1,g p.2)
def clock (n:ℕ):ℝ:=iteratedFDeriv ℝ n (id:ℝ→ℝ) 0 (fun _=>1)
def part (g:B→E)(n:ℕ)(b:B):E:=(iteratedFDeriv ℝ n (chart g) 0 (fun _=>((1:ℝ),b))).2

private theorem fit (g:B→E)(hg:ContDiffAt ℝ ω g 0):ContDiffAt ℝ ω (chart g) 0:=
  contDiffAt_fst.prodMk (hg.comp (0:ℝ×B) contDiffAt_snd)

private theorem thermal (g:B→E)(hg:ContDiffAt ℝ ω g 0)(n:ℕ)(b:B):
    iteratedFDeriv ℝ n (chart g) 0 (fun _=>((1:ℝ),b))=(clock n,part g n b):=by
  have left:=DFunLike.congr_fun ((ContinuousLinearMap.fst ℝ ℝ E).iteratedFDeriv_comp_left
    (fit g hg) (i:=n) le_top) (fun _=>((1:ℝ),b))
  have right:=DFunLike.congr_fun ((ContinuousLinearMap.fst ℝ ℝ B).iteratedFDeriv_comp_right
    (show ContDiff ℝ ω (id:ℝ→ℝ) from contDiff_id) (0:ℝ×B) (i:=n) le_top) (fun _=>((1:ℝ),b))
  refine Prod.ext ?_ ?_
  · exact left.symm.trans right
  · rfl

theorem chain (g:B→E)(hg:ContDiffAt ℝ ω g 0)(origin:g 0=0)
    (h:(ℝ×E)→ℝ)(hh:ContDiffAt ℝ ω h 0)(n:ℕ)(b:B):
    iteratedFDeriv ℝ n (h ∘ chart g) 0 (fun _=>((1:ℝ),b))=
      ∑c:OrderedFinpartition n,iteratedFDeriv ℝ c.length h 0
        (fun j=>(clock (c.partSize j),part g (c.partSize j) b)):=by
  have base:chart g 0=0:=Prod.ext rfl origin
  have fitH:ContDiffAt ℝ ω h (chart g 0):=base.symm ▸ hh
  rw [iteratedFDeriv_comp fitH (fit g hg) le_top,FormalMultilinearSeries.taylorComp,_root_.sum_apply]
  apply sum_congr rfl
  intro c _
  simp only [FormalMultilinearSeries.compAlongOrderedFinpartition_apply,ftaylorSeries,
    OrderedFinpartition.applyOrderedFinpartition_apply,base,Function.comp_def,thermal g hg]

private theorem file (h:(ℝ×E)→ℝ)(n:ℕ)(b:E):
    iteratedFDeriv ℝ n h 0 (fun _=>((1:ℝ),b))=(n.factorial:ℝ)*Assembly.jet h n (1,b):=by
  unfold Assembly.jet
  rw [smul_eq_mul,←mul_assoc,mul_inv_cancel₀ (by exact_mod_cast (Nat.factorial_ne_zero n)),one_mul]

def invoice (g:B→E)(h:(ℝ×E)→ℝ)(n:ℕ)(b b₀:B):ℝ:=
  (n.factorial:ℝ)⁻¹*∑c:OrderedFinpartition n,
    let w:=weights (fun j=>clock (c.partSize j))
    ∑u∈w.support,w u*(c.length.factorial:ℝ)*
      (Assembly.jet h c.length (1,angular (fun j=>part g (c.partSize j) b) u)-
        Assembly.jet h c.length (1,angular (fun j=>part g (c.partSize j) b₀) u))

theorem centered (g:B→E)(hg:ContDiffAt ℝ ω g 0)(origin:g 0=0)
    (h:(ℝ×E)→ℝ)(hh:ContDiffAt ℝ ω h 0)(n:ℕ)(b b₀:B):
    Assembly.jet (h ∘ chart g) n (1,b)-Assembly.jet (h ∘ chart g) n (1,b₀)=invoice g h n b b₀:=by
  unfold Assembly.jet
  rw [←smul_sub,chain g hg origin h hh,chain g hg origin h hh,←sum_sub_distrib]
  unfold invoice
  change (n.factorial:ℝ)⁻¹ * _=_
  congr 1
  apply sum_congr rfl
  intro c _
  rw [WilsonPositionProgramThermalPolar.centered _ _ _ _ (Analysis.sym_Jet (hh.of_le le_top))]
  apply sum_congr rfl
  intro u _
  rw [file,file]
  ring

end YM.Integration.WilsonPositionProgramAngularChart
end
