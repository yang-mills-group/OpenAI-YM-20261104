import YM.Integration.FVA1Physical.Wilson.PhysicalInlet
import YM.Integration.FVA1Physical.Wilson.EnterRows

/-! Planting the raw mixed inlet in the actual forest gives exactly the FVA2
source bank, coefficient by coefficient including all trunk, repeated and
coincident slots. The identity precedes taking any Gaussian or Haar integral. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Set Finset Lattice RG YM.Wilson Tree Precision Exterior Push.Uniform
open RGComparison.Core16 RGComparison.Core16.Spool RGComparison.Core16.Lumen
open FormalOPE.RG10.MultiGauge FVA2.CityHistory PertExtension.Chart
open MSbar MSbar.Bakery MSbar.Rolling MSbar.Mosaic YM.Integration.FVA1Physical.Round2.Curvature
open scoped Classical Topology
variable {G:Gauge} {I:Type} [Fintype I] (J:I→Lamp G)

def inletProjection {c f:Side} (S:StepData c f) (F:Forest S.ratio) (o:I→Site f):
    (Future G S F × Pins G c) →L[ℝ] (↥(Finset.univ:Finset (Slice J))→G.Color):=
  ContinuousLinearMap.pi fun t=>
    if ht:legs J o t.val∈F.trunks then 0 else
      (ContinuousLinearMap.proj (R:=ℝ) (⟨legs J o t.val,ht⟩:F.Free)).comp (ContinuousLinearMap.fst ℝ _ _)

theorem inlet_draped {c f:Side} (S:StepData c f) (F:Forest S.ratio) (o:I→Site f) (part:Bool)
    (v:Future G S F × Pins G c):
    look part (column J o (F.drape (expLinks G _ v.1)))=
      lampShape J part Finset.univ (inletProjection J S F o v):=by
  unfold column lampShape
  rw [←exhibition J o]
  apply congrArg (fun z=>look part (exhibit J z))
  funext t
  simp only [selectLinks,Finset.mem_univ,dif_pos,Function.comp_apply,inletProjection,ContinuousLinearMap.pi_apply]
  by_cases win:legs J o t∈F.trunks
  · rw [dif_pos win,F.on_tree _ ⟨_,win⟩];exact G.mat_lieExp_zero.symm
  · rw [dif_neg win,F.off_tree _ (⟨_,win⟩:F.Free)];rfl

theorem inlet_ticket (A:Issue G) (o:I→Site A.f) (part:Bool) (z:Positions (Joint A.F G)) (i:ℕ):
    MvPolynomial.eval z (PowerSeries.coeff i (enterRows A (stencilInlet J o part)))=
      PowerSeries.coeff i (Stack.read ((tint G _ (pushG A.F z)),(0:Pins G A.c))
        (Stack.rise (stencilSignal A.S A.F J o part))):=by
  let v:Future G A.S A.F × Pins G A.c:=(tint G _ (pushG A.F z),0)
  rw [enter_read,stencilInlet,PowerSeries.coeff_mk,MvPolynomial.eval_rename,lampRow_eval,
    group_stencil_ticket A.S A.F J o part,Stack.read_rise]
  rw [show (fun w:Future G A.S A.F × Pins G A.c=>look part (column J o (A.F.drape (expLinks G _ w.1))))=
    lampShape J part Finset.univ ∘ inletProjection J A.S A.F o from funext (inlet_draped J A.S A.F o part)]
  rw [FVA2.GermLaplace.jet_pull _ _ (lampShape_hot J part _|>.of_le le_top)]
  congr 1
  funext t;apply PiLp.ext;intro l
  let e:=legs J o t.val
  rw [taps,LinearMap.toMatrix'_mulVec]
  change Rolling.stamp A.F G (pushG A.F z) ((e.1,Exterior.coord e.2),l)=(inletProjection J A.S A.F o v t) l
  rw [Rolling.ruler]
  unfold inletProjection
  simp only [ContinuousLinearMap.pi_apply]
  by_cases he:e∈A.F.trunks
  · rw [dif_pos he,dif_pos he];rfl
  · rw [dif_neg he,dif_neg he];rfl

theorem inlet_FVA2 (A:Issue G) (o:I→Site A.f) (part:Bool):
    enterRows A (stencilInlet J o part)=jointFieldBank J A o part:=by
  ext1 i
  apply MvPolynomial.funext;intro z
  rw [inlet_ticket]
  have same:(fun i:Joint A.F G=>Sum.elim (fun k=>z (.inl k)) (fun k=>(tint G _ (pushG A.F z) k.1) k.2) i)=z:=by
    funext k;cases k <;> rfl
  exact (joint_seed J A o part i (tint G _ (pushG A.F z),0) (fun k=>z (.inl k))).trans (by rw [same])

end YM.Integration.FVA1Physical.Wilson
