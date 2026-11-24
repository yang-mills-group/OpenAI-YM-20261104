import YM.Integration.WilsonMarkedRelativeForestCoordinates
import YM.Integration.WilsonPhysicalLogChainPrice

/-! Held coarse and free Wilson coordinates use the very same scalar ray.
Local nonlinear group multiplication gives a single price before all tori. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMarkedRelativeForestRay
open Function Filter Finset Lattice Exterior Stationary Tree Work.F03
open WilsonMarkedRelativeForestChart WilsonMarkedRelativeForestCoordinates
open scoped Topology ContDiff Classical
variable {G:Gauge} {c f:Side} {g:Ratio c f}

def ray (F:Forest g)(u:ChartVars F G)(t:ℝ):ℝ×Stationary.Link G f:=(t,field F (t • u))

theorem zero (F:Forest g)(u:ChartVars F G):ray F u 0=0:=by
  have axis0:axisLog F (0:ChartVars F G)=0:=congrArg Prod.snd (inclusion_zero F)
  simp [ray,field,axis0]

theorem regular (F:Forest g)(u:ChartVars F G):ContDiffAt ℝ ω (ray F u) 0:=by
  have fine:ContDiffAt ℝ ω (fun t:ℝ=>field F (t • u)) 0:=by
    have hfield:ContDiffAt ℝ ω (field F) ((0:ℝ) • u):=by simpa using WilsonMarkedRelativeForestCoordinates.smooth (G:=G) F
    exact hfield.comp (f:=fun t:ℝ=>t • u) 0 (contDiffAt_id.smul contDiffAt_const)
  exact contDiffAt_id.prodMk fine

theorem component {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F:Forest g)(u:ChartVars F G)(r:ℕ)(L:(ℝ×Stationary.Link G f)→L[ℝ]E):
    iteratedDeriv r (L ∘ ray F u) 0=L (iteratedDeriv r (ray F u) 0):=by
  rw [iteratedDeriv_eq_iteratedFDeriv,iteratedDeriv_eq_iteratedFDeriv]
  have h:ContDiffAt ℝ ∞ (ray F u) 0:=(regular F u).of_le le_top
  exact DFunLike.congr_fun (L.iteratedFDeriv_comp_left h (by exact_mod_cast le_top)) (fun _=>1)

theorem fiber (F:Forest g)(u:ChartVars F G)(r:ℕ):
    iteratedDeriv r (fun t:ℝ=>field F (t • u)) 0=
      iteratedFDeriv ℝ r (field F) 0 (fun _=>u):=by
  let L:=ContinuousLinearMap.toSpanSingleton ℝ u
  rw [iteratedDeriv_eq_iteratedFDeriv]
  change iteratedFDeriv ℝ r (field F ∘ L) 0 (fun _=>1)=_
  rw [Next.Foundations.jets_linear L ((WilsonMarkedRelativeForestCoordinates.smooth F).of_le le_top),
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1;funext i;exact one_smul ℝ u

theorem bound (F:Forest g)(u:ChartVars F G)(r:ℕ):
    ‖iteratedDeriv r (ray F u) 0‖ ≤ 1+
      ‖iteratedFDeriv ℝ r (localLog G) 0‖*‖u‖^r:=by
  let x:=iteratedDeriv r (ray F u) 0
  have time:x.1=(if r=1 then 1 else 0):=by
    rw [show x.1=iteratedDeriv r (fun t:ℝ=>t) 0 from
      (component F u r (ContinuousLinearMap.fst ℝ ℝ (Stationary.Link G f))).symm,iteratedDeriv_fun_id_zero]
  have space:x.2=iteratedFDeriv ℝ r (field F) 0 (fun _=>u):=
    (component F u r (ContinuousLinearMap.snd ℝ ℝ (Stationary.Link G f))).symm.trans (fiber F u r)
  change max ‖x.1‖ ‖x.2‖ ≤ _
  apply max_le
  · have pos:0≤‖iteratedFDeriv ℝ r (localLog G) 0‖*‖u‖^r:=mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
    rw [time];split_ifs <;> simp only [norm_one,norm_zero] <;> linarith only [pos]
  · rw [space]
    have fee:‖iteratedFDeriv ℝ r (field F) 0 (fun _=>u)‖ ≤
        ‖iteratedFDeriv ℝ r (localLog G) 0‖*‖u‖^r:=by
      refine ((iteratedFDeriv ℝ r (field F) 0).le_opNorm _).trans ?_
      simp only [prod_const,card_univ,Fintype.card_fin];exact
        mul_le_mul_of_nonneg_right (WilsonMarkedRelativeForestCoordinates.bound F r) (pow_nonneg (norm_nonneg u) _)
    linarith only [fee]

end YM.Integration.WilsonMarkedRelativeForestRay
end
