import YM.Integration.WilsonPositionProgramAngularChart
import YM.Integration.WilsonMarkedRelativeForestChart
import YM.Next.WARD_BIN.Lies

/-! Each polar test of the curved Wilson chart has a cost independent of the period and forest. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionProgramAngularDirection
open Function Finset Lattice Tree RG Work.F03 WilsonPositionProgramAngularChart
open WilsonPositionProgramThermalPolar WilsonMarkedRelativeForestChart
open scoped Classical BigOperators ContDiff
variable {B E:Type*}[NormedAddCommGroup B][NormedSpace ℝ B][NormedAddCommGroup E][NormedSpace ℝ E]

theorem evaluate (g:B→E)(hg:ContDiffAt ℝ ω g 0)(n:ℕ)(b:B):
    part g n b=iteratedFDeriv ℝ n g 0 (fun _=>b):=by
  have fit:ContDiffAt ℝ ω (chart g) 0:=contDiffAt_fst.prodMk (hg.comp (0:ℝ×B) contDiffAt_snd)
  have left:=DFunLike.congr_fun ((ContinuousLinearMap.snd ℝ ℝ E).iteratedFDeriv_comp_left
    fit (i:=n) le_top) (fun _=>((1:ℝ),b))
  have right:=DFunLike.congr_fun (WardBin.Lies.liner (l:=n) (a:=(0:ℝ×B))
    (ContinuousLinearMap.snd ℝ ℝ B) (hg.of_le le_top)) (fun _=>((1:ℝ),b))
  exact left.symm.trans right

theorem cost {G:Gauge}{c f:Side}{g:Ratio c f}(F:Forest g)(n:ℕ)(b:ChartVars F G):
    ‖part (axisLog (G:=G) F) n b‖≤‖iteratedFDeriv ℝ n (localLog G) 0‖*‖b‖^n:=by
  rw [evaluate (axisLog (G:=G) F) (inclusion_smooth F).snd n b]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n (axisLog (G:=G) F) 0‖ * ∏ _j:Fin n,‖b‖ :=
      ContinuousMultilinearMap.le_opNorm _ _
    _ ≤ _ :=by simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin];gcongr
               exact WilsonMarkedRelativeForestChart.bound F n

theorem sum_price {d:ℕ}(v:Fin d→E)(u:Slots d):
    ‖angular v u‖≤∑i,|u i| *‖v i‖:=by
  have represented:angular v u=∑i,(u i)•v i:=by simp [angular,LinearMap.sum_apply]
  rw [represented]
  exact (norm_sum_le _ _).trans_eq (by simp [norm_smul,Real.norm_eq_abs])

def mass (G:Gauge){d:ℕ}(a:Fin d→ℕ)(u:Slots d):ℝ:=
  ∑j,|u j| *‖iteratedFDeriv ℝ (a j) (localLog G) 0‖

theorem original {G:Gauge}{c f:Side}{g:Ratio c f}(F:Forest g){d:ℕ}(a:Fin d→ℕ)
    (k:ℕ)(ha:∀j,a j≤k)(u:Slots d)(b:ChartVars F G):
    ‖angular (fun j=>part (axisLog F) (a j) b) u‖≤mass G a u*(1+‖b‖)^k:=by
  refine (sum_price _ _).trans ?_
  unfold mass
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _=>?_
  calc
    |u j| *‖part (axisLog F) (a j) b‖ ≤ |u j| *(‖iteratedFDeriv ℝ (a j) (localLog G) 0‖*‖b‖^(a j)) :=
      mul_le_mul_of_nonneg_left (cost F _ b) (abs_nonneg _)
    _ = _ := mul_assoc _ _ _ |>.symm
    _ ≤ _ :=by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (pow_le_pow_left₀ (norm_nonneg _) (by linarith : ‖b‖≤1+‖b‖) _).trans
        (pow_le_pow_right₀ (by linarith [norm_nonneg b]) (ha j))

end YM.Integration.WilsonPositionProgramAngularDirection
end
