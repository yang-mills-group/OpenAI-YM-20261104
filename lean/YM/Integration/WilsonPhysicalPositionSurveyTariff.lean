import YM.Integration.WilsonPhysicalPositionTargetRows
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! Signed target error for the native Born-branch position fit, including separate source and exterior homes. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalPositionSurveyTariff
open Filter Function Set Maxwell Maxwell.Free XSpace XSpace.Normalize WilsonPhysicalPositionTargetRows
open scoped Classical BigOperators ContDiff Topology
variable {G:Gauge}{d n:ℕ}{I:Type}{A:Screen G d}(D:Fray A)(H:A.Prepared)
variable (home:Fin n→I)(v:Fin n→Sec G d)

def operator (banks:I→D.Bag):WilsonPhysicalPositionTargetRows.Array G d n→L[ℝ]ℂ:=
  meter home v (fun i=>D.route H (banks i))

theorem analytic [Fintype I]:
    ContDiffAt ℝ ω (operator D H home v) (fun _=>D.opening.1):=by
  let o:I→D.Bag:=fun _=>D.opening.1
  have pier (i:I):ContDiffAt ℝ ω (D.route H ∘ fun b:I→D.Bag=>b i) o:=
    (D.train H).comp o (contDiff_apply ℝ D.Bag i).contDiffAt
  exact (smooth home v).contDiffAt.comp o (contDiffAt_pi.mpr pier)

private theorem operator_bound {X V:Type*}[NormedAddCommGroup X][NormedSpace ℝ X]
    [NormedAddCommGroup V][NormedSpace ℝ V] (t:X→V→L[ℝ]ℂ)(o:X)(h:ContDiffAt ℝ 1 t o):
    ∃ C:ℝ,0<C ∧ ∃ U∈𝓝 o,∀ x∈U,∀ y∈U,∀ a b,‖t x a-t y b‖≤C*(‖a-b‖+‖x-y‖*‖b‖):=by
  obtain ⟨k,U,hU,lip⟩:=h.exists_lipschitzOnWith
  have ho:o∈U:=mem_of_mem_nhds hU
  let C:ℝ:=1+k+‖t o‖
  have hk:(k:ℝ)≤C:=by dsimp [C];linarith [norm_nonneg (t o)]
  refine ⟨C,by dsimp [C];positivity,U ∩ Metric.ball o 1,inter_mem hU (Metric.ball_mem_nhds _ zero_lt_one),?_⟩
  intro x hX y hY a b
  have slope {x y:X}(hx:x∈U)(hy:y∈U):‖t x-t y‖≤k*‖x-y‖:=by
    simpa [dist_eq_norm] using (lipschitzOnWith_iff_dist_le_mul.mp lip) x hx y hy
  have close:‖x-o‖≤1:=by simpa [Metric.mem_ball,dist_eq_norm] using (show dist x o<1 from hX.2).le
  have head:‖t x‖≤C:=by
    calc
      ‖t x‖≤‖t x-t o‖+‖t o‖:=by simpa only [add_comm] using norm_le_insert' (t x) (t o)
      _≤(k:ℝ)*1+‖t o‖:=add_le_add ((slope hX.1 ho).trans
        (mul_le_mul_of_nonneg_left close k.coe_nonneg)) (le_refl _)
      _≤C:=by dsimp [C];linarith
  calc
    ‖t x a-t y b‖=‖t x (a-b)+(t x-t y) b‖:=by
      congr 1;simp only [map_sub,_root_.sub_apply];abel
    _≤‖t x (a-b)‖+‖(t x-t y) b‖:=norm_add_le _ _
    _≤‖t x‖*‖a-b‖+‖t x-t y‖*‖b‖:=add_le_add ((t x).le_opNorm _) ((t x-t y).le_opNorm _)
    _≤C*‖a-b‖+(C*‖x-y‖)*‖b‖:=add_le_add (mul_le_mul_of_nonneg_right head (norm_nonneg _))
      (mul_le_mul_of_nonneg_right ((slope hX.1 hY.1).trans
      (mul_le_mul_of_nonneg_right hk (norm_nonneg _))) (norm_nonneg _))
    _=C*(‖a-b‖+‖x-y‖*‖b‖):=by ring

theorem invoice [Fintype I]:
    ∃ C:ℝ,0<C ∧ ∃ U∈𝓝 (fun _:I=>D.opening.1),∀ X∈U,∀ Y∈U,∀ a b,
      ‖operator D H home v X a-operator D H home v Y b‖≤
        C*(‖a-b‖+‖X-Y‖*‖b‖):=
  operator_bound _ _ ((analytic D H home v).of_le (by simp))

theorem published (banks:I→Prediction G d)(M:MultilinearMap ℂ (fun _:Fin n=>Sec G d) ℂ):
    operator D H home v (fun i=>D.purse (banks i)) (rows M)=
      M (fun i=>stand (D.firstPass H (banks (home i))) (v i)):=by
  simpa only [operator,←D.guid] using counted home v M (fun i=>D.firstPass H (banks i))

end YM.Integration.WilsonPhysicalPositionSurveyTariff
