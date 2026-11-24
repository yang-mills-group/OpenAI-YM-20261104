import YM.Integration.WilsonOriginalJointDeckMotion
import YM.Analysis.SmoothJets
import YM.Comparison.RG02.Assembly.Vertices

/-! The measured one-thermal ray at one paid Taylor degree determines every ordered mixed slot. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalGradedJointBinding
open Function Finset Filter Analysis Lattice RG Wilson QuadraticLocal Stationary
open Further.PhysicalPeriodLimitF933 Macrame FVA1Physical FVA1Physical.TwoReset
open Comparison.RG02 WilsonOriginalPolarizedAngularPage WilsonOriginalConnectedPeriodPage WilsonOriginalJointDeckMotion WilsonEmittedRootedJetWage
open scoped Classical BigOperators ContDiff Topology
variable {G:Gauge} {n N:Side}

theorem tensor {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (r:ℕ) (Y Z:ℝ×E→ℂ)
    (art:ContDiffAt ℝ r Y 0) (star:ContDiffAt ℝ r Z 0)
    (heard:∀A:E, Assembly.jet Y r (1,A)=Assembly.jet Z r (1,A)):
    iteratedFDeriv ℝ r Y 0=iteratedFDeriv ℝ r Z 0:=by
  let a:=iteratedFDeriv ℝ r Y 0
  let b:=iteratedFDeriv ℝ r Z 0
  have unit (A:E):a (fun _=>(1,A))=b (fun _=>(1,A)):=by
    have live:(r.factorial:ℝ)≠0:=by exact_mod_cast Nat.factorial_ne_zero r
    simpa only [Assembly.jet,smul_smul,mul_inv_cancel₀ live,one_smul] using
      congrArg (fun v:ℂ=>(r.factorial:ℝ) • v) (heard A)
  have away (t:ℝ) (ht:t≠0) (A:E):a (fun _=>(t,A))=b (fun _=>(t,A)):=by
    have rep:(t,A)=t • ((1:ℝ),t⁻¹ • A):=Prod.ext (by simp) (by change A=t • t⁻¹ • A;simp [smul_smul,ht])
    rw [rep,a.map_smul_univ,b.map_smul_univ,unit]
  apply Tensor.ext_diag _ _ (Analysis.sym_Jet art) (Analysis.sym_Jet star)
  funext y
  obtain ⟨t,A⟩:=y
  by_cases ht:t=0
  · subst t
    have ca:Continuous (fun t:ℝ=>a (fun _=>(t,A))):=a.cont.comp (continuous_pi fun _=>continuous_id.prodMk continuous_const)
    have cb:Continuous (fun t:ℝ=>b (fun _=>(t,A))):=b.cont.comp (continuous_pi fun _=>continuous_id.prodMk continuous_const)
    exact tendsto_nhds_unique_of_eventuallyEq ((ca.tendsto 0).mono_left (nhdsWithin_le_nhds (s:=Set.Ioi (0:ℝ))))
      ((cb.tendsto 0).mono_left (nhdsWithin_le_nhds (s:=Set.Ioi (0:ℝ))))
      (mem_of_superset self_mem_nhdsWithin fun t gt=>away t (ne_of_gt gt) A)
  · exact away t ht A

theorem orbit (h:n.val∣N.val) (x y:Site N) (r:ℕ) (Y Z:ℝ×Directions G N→ℂ)
    (art:ContDiff ℝ r Y) (star:ContDiff ℝ r Z)
    (heard:∀A:Directions G N,Assembly.jet (board h x (motion G) Y) r (1,A)=Assembly.jet (board h y (motion G) Z) r (1,A)) (u:Fin r→Slot G N):
    (∑a:Deck h,(entry r Y (turn a.1 u)-entry r Z (turn a.1 u)))=0:=by
  have yc:ContDiff ℝ r (board h x (motion G) Y):=by
    unfold board;simp_rw [Finset.sum_fn]
    exact ContDiff.sum fun p _=>art.comp (motion G ((page h (splitter h x) p).val-x)).contDiff
  have zc:ContDiff ℝ r (board h y (motion G) Z):=by
    unfold board;simp_rw [Finset.sum_fn]
    exact ContDiff.sum fun p _=>star.comp (motion G ((page h (splitter h y) p).val-y)).contDiff
  have same:=tensor r _ _ yc.contDiffAt zc.contDiffAt heard
  rw [sum_sub_distrib,sub_eq_zero,←slots h x Y art u,←slots h y Z star u,entry,entry,same]

end YM.Integration.WilsonOriginalGradedJointBinding
