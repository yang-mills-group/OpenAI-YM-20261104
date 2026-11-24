import YM.Integration.WilsonPositionPrescribedScreen
import YM.XSpace.Deck

/-! Simultaneously change the incoming measured fields on the entire finite
position screen. The original physical Born limit controls the transformed
screen even when the incoming change has no expansion in the coupling. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalPositionChangePanel
open Function Filter Set Finset Spec Table Extraction Trace.Pilot PhysMS
open Maxwell Maxwell.Free XSpace XSpace.Normalize
open scoped Topology BigOperators Classical
variable {G:Gauge}{d:ℕ}

def displacement (p:Sec G d):MoveSpace G d→ₗ[ℝ] RSpace G d where
  toFun a:=tableD G d (((guide G d).symm a).val p)
  map_add' a b:=by rw [map_add];exact map_add (tableD G d) _ _
  map_smul' a b:=by rw [map_smul];exact map_smul (tableD G d) _ _

theorem coordinates {I:Type}{l:Filter I}(A:I→Change G d)
    (small:Tendsto (fun i=>guide G d (A i)) l (𝓝 0))(p:Sec G d):
    Tendsto (fun i=>tableD G d (stand (A i) p)) l (𝓝 (tableD G d p)):=by
  have z: Tendsto (fun i=>displacement p (guide G d (A i))) l (𝓝 0):=by
    simpa only [map_zero,Function.comp_def] using ((displacement p).continuous_of_finiteDimensional.tendsto 0).comp small
  have expand i:tableD G d (stand (A i) p)=tableD G d p+displacement p (guide G d (A i)):=by
    simp only [stood,map_add,displacement,LinearMap.coe_mk,AddHom.coe_mk,LinearEquiv.symm_apply_apply]
  simp_rw [expand]
  simpa only [add_zero] using (tendsto_const_nhds (x:=tableD G d p)).add z

theorem transformed {I:Type}{l:Filter I}{S:Screen G d}(D:Fray S)
    (P:I→Prediction G d)(bank:D.Via P (u:=l))(A:I→Change G d)
    (small:Tendsto (fun i=>guide G d (A i)) l (𝓝 0)):
    D.Via (fun i=>recruit (stand (A i)) (P i)) (u:=l):=by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro k
  let w:=D.scope i
  let p(j:Fin w.n):Sec G d:=Module.finBasis ℝ (Sec G d) (k j)
  let bas(r:Fin w.n→Pin G d)(j:Fin w.n):Sec G d:=Module.finBasis ℝ (Sec G d) (r j)
  let v(t:I)(j:Fin w.n):=stand (A t) (p j)
  change Tendsto (fun t=>P t w.n w.t (v t)) l (𝓝 (reference G d w.n w.t p))
  have entry(r:Fin w.n→Pin G d):Tendsto (fun t=>P t w.n w.t (bas r)) l (𝓝 (reference G d w.n w.t (bas r))):=
    tendsto_pi_nhds.mp (tendsto_pi_nhds.mp bank i) r
  have scaled(r:Fin w.n→Pin G d):Tendsto (fun t=>∏j,tableD G d (v t j) (r j)) l
      (𝓝 (∏j,tableD G d (p j) (r j))):=by
    apply tendsto_finsetProd
    intro j _
    exact tendsto_pi_nhds.mp (coordinates A small (p j)) (r j)
  have total:=tendsto_finsetSum Finset.univ fun (r:Fin w.n→Pin G d) _=>(scaled r).smul (entry r)
  have lhs(t:I):P t w.n w.t (v t)=∑r:Fin w.n→Pin G d,(∏j,tableD G d (v t j) (r j)) • P t w.n w.t (bas r):=
    medium (v t) ((P t w.n w.t).restrictScalars ℝ)
  have rhs:reference G d w.n w.t p=∑r:Fin w.n→Pin G d,(∏j,tableD G d (p j) (r j)) • reference G d w.n w.t (bas r):=
    medium p ((reference G d w.n w.t).restrictScalars ℝ)
  simpa only [←lhs,←rhs] using total

variable {C:Family G}{f:Extraction.Order}{S:Table C.book}
    (F:Final C f S)(J:ℝ→tower S)

theorem original (lead:Leading F J)(V:Store G)(d:ℕ)(A:ℝ→Change G d)
    (small:Tendsto (fun r=>guide G d (A r)) trail (𝓝 0)):
    let P:=fun r=>recruit (stand (A r)) (WilsonPositionPrescribedScreen.hierarchy F J d r)
    let T:=fun r=>(V.survey d).firstPass (V.prepared d) (P r)
    Tendsto (fun r=>guide G d (T r)) trail (𝓝 0) ∧
    ∀ᶠr in trail, Fray.SetEq (V.measure d) (T r) (P r) ∧ Bijective (stand (T r)):=by
  intro P T
  have bank:=transformed (V.survey d) _ (WilsonPositionPrescribedScreen.warm F J lead V d) A small
  exact ⟨(V.survey d).turns_approach (V.prepared d) bank,
    ((V.survey d).passed (V.prepared d) bank).and ((V.survey d).stand_sure (V.prepared d) bank)⟩

end YM.Integration.WilsonPhysicalPositionChangePanel
end
