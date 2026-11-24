import YM.Work.A15
import YM.Extra.WEAK_SCALING_ACTLAW.Adjust
set_option autoImplicit false
noncomputable section
namespace YM.Contacts.Rigid
open Function Set Filter MeasureTheory Extraction Table Analysis
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{L:Register G}{S T:Table L}
 -- use the same compact averaging as A15. no orientation reach hidden in custom detector
scoped instance : CompactSpace Ortho := Work.A15.compact_ortho
scoped instance : SecondCountableTopology Ortho := by
  haveI : SecondCountableTopology M4 := inferInstanceAs (SecondCountableTopology (Axis → Axis → ℝ))
  exact inferInstanceAs (SecondCountableTopology ↥((Matrix.unitaryGroup Axis ℝ : Set M4)))
scoped instance : MeasurableSpace Ortho:= borel Ortho
scoped instance : BorelSpace Ortho:= ⟨rfl⟩

def all : TopologicalSpace.PositiveCompacts Ortho := ⟨⟨Set.univ,isCompact_univ⟩,by simp⟩
def probability : Measure Ortho:= Measure.haarMeasure all
scoped instance prob_isHaar : probability.IsHaarMeasure:=by unfold probability; infer_instance
scoped instance prob_isProb : IsProbabilityMeasure probability:=⟨@Measure.haarMeasure_self Ortho _ _ _ _ _ all⟩

lemma integral_over {α:Type*}[NormedAddCommGroup α][NormedSpace ℝ α](t:Ortho)(f:Ortho→α): (∫ i,f (t*i) ∂ probability)=∫ i,f i ∂ probability :=(measurePreserving_mul_left probability t).integral_comp (Homeomorph.mulLeft t).measurableEmbedding f

-- label transformations: evaluate continuously in field and angle. No assertion outside Conf here.
variable (R:S.Rotation) {D:DiffPlan S} {H:S.RealSpin}(h:R.Laws D H)
include h in
lemma act_cont (d:ℕ): Continuous fun x:Ortho× S.Field d=> R.act d x.1 x.2:=by
   let b:= Module.finBasis ℂ (S.Field d); have he (x:Ortho) (v) : R.act d x v= ∑ i, b.coord i v • R.act d x (b i):= by simp_rw [← map_smul,← map_sum]; rw [show ∑ i,b.coord i v • b i=v from b.sum_repr _]
   -- `simp_rw` dangerous infinite loop
   rw [show (fun x:Ortho× S.Field d=> R.act d x.1 x.2)= fun x=> ∑ i, b.coord i x.2 • R.act d x.1 (b i) from funext fun i=> he ..]; exact continuous_finsetSum _ (fun i _ => ((b.coord i).continuous_of_finiteDimensional.comp continuous_snd).smul ((h.spin ..).comp continuous_fst))
-- real conjugation restricted (needed for moving tags)
def realConj (H:S.RealSpin)(d:ℕ): S.Field d→L[ℝ] S.Field d:= by
   haveI : FiniteDimensional ℝ (S.Field d) := Module.Finite.trans ℂ _
   exact LinearMap.toContinuousLinearMap { toFun:=fun x=> S.conj H d x, map_add':= (S.conj H d).map_add,
                                           map_smul':=fun r v=> by simp only [RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smulₛₗ]; simp } -- check
@[simp] lemma realConj_apply (H:S.RealSpin)(d:ℕ)(v:S.Field d): realConj H d v=S.conj H d v:= rfl

section Lower
-- keep coupled to physical rotations. Lower each neighbor before aligning all fixed/growing proofs
variable (hT:S.Hierarchy)(hl:R.Laws D hT.spin)(hr:D.Orientation hT.spin)(he:D.Inclusions S)
include hl hr he
lemma keeps (d:ℕ) : ∃ P:S.Field (d+1)→ₗ[ℂ] S.Field d, (∀ v, P (D.rise (Nat.le_succ d) v)=v) ∧
      (∀ K v,P (R.act (d+1) K v)=R.act d K (P v)) ∧ ∀ v,P (S.conj hT.spin _ v)=S.conj hT.spin d (P v) := by
   classical
   obtain ⟨P,hP,-,hp⟩:= Extra.WeakScaling.retraction hT D he hr d
   let y K : S.Field (d+1) →ₗ[ℂ] S.Field d:= (R.act d K).toLinearMap ∘ₗ P ∘ₗ (R.act (d+1) K⁻¹).toLinearMap
   have hy K v: y K v=R.act d K (P (R.act _ K⁻¹ v)):=rfl
   have hv v : Integrable (fun i=> y i v) probability := by
       simp_rw [hy]; exact ((act_cont R hl d).comp (continuous_id.prodMk (P.continuous_of_finiteDimensional.comp ((hl.spin (d+1) v).comp continuous_inv)))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
   let L x:= ∫ i,y i x ∂ probability
   refine ⟨{ toFun:=L, map_add':=?_, map_smul':=?_ },?_,?_,?_⟩
   · intro a b; simp_rw [L,map_add,integral_add (hv a) (hv b)]
   · intro a b; simp_rw [L,map_smul,integral_smul]; rfl -- smul vs mul
   · intro v; change ∫ i,y i (D.rise _ v) ∂ probability= _; simp_rw [hy,hl.filtered d (d+1),hP,← hl.group,mul_inv_cancel,hl.fixes]; simp
   · intro K v
     let A:= LinearMap.toContinuousLinearMap (R.act d K).toLinearMap; have h (i): y (K*i) (R.act (d+1) K v)= A (y i v):=by
         rw [hy,hy,hl.group,mul_inv_rev]; change _ = R.act d K _; rw [← hl.group (d+1), mul_assoc,inv_mul_cancel,mul_one]
     calc _ = ∫ i, y i (R.act (d+1) K v) ∂ probability:= rfl
          _ = ∫ i, y (K*i) (R.act (d+1) K v) ∂ probability := (integral_over K (fun i=> y i (R.act _ K v))).symm
          _ = ∫ i, A (y i v) ∂ probability := by simp_rw [h]
          _ = _ := ContinuousLinearMap.integral_comp_comm A (hv v)
   intro v; let f:= realConj hT.spin d
   have h K: y K (S.conj hT.spin _ v)= f (y K v):= by simp_rw [hy,← hl.real]; unfold f; rw [hp]; simp_rw [realConj_apply,← hl.real] -- order
   change ∫ i,y i (S.conj hT.spin _ v) ∂ probability=f (∫ i,y i v ∂ probability); simp_rw [h]; exact ContinuousLinearMap.integral_comp_comm f (hv v)
end Lower
end YM.Contacts.Rigid
