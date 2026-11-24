import YM.Analysis.Symmetric
import Mathlib.LinearAlgebra.Dual.Lemmas
import YM.Comparison.RG02.Assembly.Vertices

/-! Mixed thermal and link directions from unit-thermal angular tests. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionProgramThermalPolar
open Function Filter Finset Set
open scoped Classical BigOperators Topology

abbrev Slots (r:ℕ):=Fin r→ℝ
abbrev Thermal (r:ℕ):=ℝ×Slots r

private def symmetric (r:ℕ):Submodule ℝ (Tensor.T (Thermal r) ℝ r) where
  carrier:={A|Tensor.Sym A}
  zero_mem':=fun _ _=>rfl
  add_mem' {A B} hA hB v e:=by simp only [add_apply,hA _ _,hB _ _]
  smul_mem' c A hA v e:=by simp only [smul_apply,hA _ _]

private theorem separate {r:ℕ}(A:Tensor.T (Thermal r) ℝ r)(sym:Tensor.Sym A)
    (one:∀u:Slots r,A (fun _=>((1:ℝ),u))=0):A=0:=by
  have off (t:ℝ)(ht:t≠0)(u:Slots r):A (fun _=>(t,u))=0:=by
    have rep:(t,u)=t • ((1:ℝ),t⁻¹ • u):=by
      change (t,u)=(t*1,t • t⁻¹ • u)
      rw [mul_one,←mul_smul,mul_inv_cancel₀ ht,one_smul]
    rw [rep,A.map_smul_univ (fun _=>t) (fun _=>((1:ℝ),t⁻¹ • u)),one,smul_zero]
  apply Tensor.ext_diag _ _ sym (fun _ _=>rfl)
  funext v
  obtain ⟨t,u⟩:=v
  change A (fun _=>(t,u))=0
  by_cases h:t=0
  · subst t
    have run:Continuous (fun t:ℝ=>A (fun _=>(t,u))):=
      A.cont.comp (continuous_pi fun _=>continuous_id.prodMk continuous_const)
    exact tendsto_nhds_unique_of_eventuallyEq
      ((run.tendsto 0).mono_left (nhdsWithin_le_nhds (s:=Ioi (0:ℝ))))
      tendsto_const_nhds (mem_of_superset (self_mem_nhdsWithin (a:=0) (s:=Ioi (0:ℝ))) fun t ht=>off t (ne_of_gt ht) u)
  · exact off t h u

private theorem booked {r:ℕ}(t:Fin r→ℝ):∃w:Slots r→₀ℝ,∀A:Tensor.T (Thermal r) ℝ r,
    Tensor.Sym A → A (fun i=>(t i,Pi.single i (1:ℝ)))=
      ∑u∈w.support,w u*A (fun _=>((1:ℝ),u)):=by
  let F:=symmetric r
  let ev (v:Fin r→Thermal r):F→ₗ[ℝ]ℝ:=
    (ContinuousMultilinearMap.apply ℝ (fun _:Fin r=>Thermal r) ℝ v).toLinearMap.comp F.subtype
  let diag (u:Slots r):=ev (fun _=>((1:ℝ),u))
  let full:=ev (fun i=>(t i,Pi.single i 1))
  have mem:full∈Submodule.span ℝ (Set.range diag):=
    FiniteDimensional.mem_span_of_iInf_ker_le_ker (by
      intro a ha
      have gone:∀u,diag u a=0:= fun u=>(Submodule.mem_iInf _).mp ha u
      have vanish:a=0:=Subtype.ext (separate a.1 a.2 gone)
      rw [vanish]
      exact Submodule.zero_mem _)
  obtain ⟨w,eq⟩:=Finsupp.mem_span_range_iff_exists_finsupp.mp mem
  refine ⟨w,fun A hA=>?_⟩
  have h:=congrArg (fun k:F→ₗ[ℝ]ℝ=>k ⟨A,hA⟩) eq.symm
  simpa [Finsupp.sum,full,diag,ev,LinearMap.sum_apply] using h

def weights {r:ℕ}(t:Fin r→ℝ):Slots r→₀ℝ:=(booked t).choose

variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]

def angular {r:ℕ}(v:Fin r→E):Slots r→ₗ[ℝ]E:=∑i,(LinearMap.proj i (R:=ℝ)).smulRight (v i)

private def raise {r:ℕ}(v:Fin r→E):Thermal r→L[ℝ](ℝ×E):=
  ((LinearMap.fst ℝ ℝ (Slots r)).prod ((angular v).comp (LinearMap.snd ℝ ℝ (Slots r)))).toContinuousLinearMap

private theorem base {r:ℕ}(v:Fin r→E)(i:Fin r):angular v (Pi.single i (1:ℝ))=v i:=by
  simp [angular,LinearMap.sum_apply,LinearMap.smulRight_apply,Pi.single_apply,ite_smul]

theorem evaluated {r:ℕ}(t:Fin r→ℝ)(v:Fin r→E)(A:Tensor.T (ℝ×E) ℝ r)(sym:Tensor.Sym A):
    A (fun i=>(t i,v i))=∑u∈(weights t).support,weights t u * A (fun _=>((1:ℝ),angular v u)):=by
  let B:=A.compContinuousLinearMap (fun _=>raise v)
  have well:Tensor.Sym B:=by
    intro x e
    simp only [B,ContinuousMultilinearMap.compContinuousLinearMap_apply]
    exact sym ((raise v) ∘ x) e
  have h:=(booked t).choose_spec B well
  change A (fun i=>(t i,angular v (Pi.single i 1)))=
    ∑u∈(weights t).support,weights t u * A (fun _=>((1:ℝ),angular v u)) at h
  simpa only [base] using h

theorem centered {r:ℕ}(t:Fin r→ℝ)(v w:Fin r→E)(A:Tensor.T (ℝ×E) ℝ r)(sym:Tensor.Sym A):
    A (fun i=>(t i,v i))-A (fun i=>(t i,w i))=
      ∑u∈(weights t).support,weights t u*(A (fun _=>((1:ℝ),angular v u))-A (fun _=>((1:ℝ),angular w u))):=by
  rw [evaluated t v A sym,evaluated t w A sym,←sum_sub_distrib]
  exact sum_congr rfl fun u _=>(mul_sub _ _ _).symm

end YM.Integration.WilsonPositionProgramThermalPolar
end
