import YM.AveragedStep.Parcel.Dove
set_option autoImplicit false
noncomputable section
namespace YM.AveragedStep
open Lattice RG Wilson Precision Function Filter MeasureTheory Tree Loops
open scoped Classical Topology BigOperators Matrix.Norms.Frobenius ContDiff
-- The product integral is reduced to the integral in the selected coordinate.
-- (but there's no air continuity in our factor across all X).
lemma eliminate {S T:Type*}[Fintype S][DecidableEq S][MeasurableSpace T][Nonempty T](μ:Measure T)[IsProbabilityMeasure μ]
    (i:S)(F:(S→T)→ℝ)(h : Envelope F)(ht:∀ x,(∫ y,F (update x i y)∂μ)=0):
    (∫ x,F x ∂Measure.pi (fun _:S=>μ))=0:=by
  let α:= fun _:S=>T
  let P:= fun x:S=>x=i
  let A:=Subtype P
  letI : Unique A:=⟨⟨⟨i,rfl⟩⟩,fun x=> Subtype.ext x.prop⟩
  let M:Measure (A→T):= @Measure.pi A (fun _=>T) (Subtype.fintype P) _ (fun _=>μ)
  let e := MeasurableEquiv.piEquivPiSubtypeProd α P
  let N := @Measure.pi {x//¬ P x} (fun _=>T) (Subtype.fintype _) _ (fun _=>μ)
  have he:MeasurePreserving e _ (M.prod N):=measurePreserving_piEquivPiSubtypeProd (fun _=>μ) P
  rw [← he.symm.integral_comp',integral_prod_symm]
  · let g:=MeasurableEquiv.funUnique A T
    have hm: MeasurePreserving g M μ:= by
      convert! measurePreserving_funUnique μ A using 1
      unfold M; congr 1; exact Subsingleton.elim ..
    refine (integral_eq_zero_of_ae (Eventually.of_forall (fun z=>?_))) -- name
    change (∫ x,F (e.symm (x,z))∂ M)=0
    rw [← hm.symm.integral_comp']; by_cases hh:Nonempty T
    · let t:T:=Classical.arbitrary T
      have hx(j:T):update (e.symm (g.symm t,z)) i j=e.symm (g.symm j,z) := by
        funext k; by_cases h:k=i; · subst k; rw [update_self]; change j=if h:P i then j else z ⟨i,h⟩; rw [dif_pos (rfl:i=i)]
        rw [update_of_ne h]; change (if h:P k then t else z ⟨k,h⟩) = (if h:P k then j else z ⟨k,h⟩); rw [dif_neg h,dif_neg h]
      change (∫ x, F (e.symm (g.symm x,z))∂μ)=0
      calc
        _ = ∫ x,F (update (e.symm (g.symm t,z)) i x) ∂μ:=integral_congr_ae (Eventually.of_forall fun x=> congr_arg F (hx x).symm)
        _ = 0:= ht _
    exact False.elim (hh (by infer_instance)) -- from measure prob
  haveI : IsProbabilityMeasure M:=by
    unfold M
    rw [Subsingleton.elim (Subtype.fintype P) (inferInstance:Fintype A)]
    exact Measure.pi.instIsProbabilityMeasure _
  apply (env_comp h e.symm.measurable).integrable

variable {G:Gauge}{c f:Side}{S:StepData c f}{A:ChartRatio G}(F:Forest S.ratio)(Q:Cuff S.patch S.kernel A)(b:Site c)
lemma paired_balance {Φ: Hand G c f→ℝ}(hΦ:ContDiff ℝ 1 Φ)(i:F.Free)(v:G.Color)(τ:ℝ)
    (hA:LocalRatio A)(h:S.patch.Branches S.kernel G){u:Config G c→ℝ}(hu:Envelope u):
    report F (τ^2) b (fun p=> u p.2*sdEq F Q b Φ i v τ p)=0:=by
 rw [report_as F b h (τ^2) ((env_comp hu measurable_snd).mul (sd_safe F Q b Φ hΦ i v τ hA)),
     show (∫ V,∫ U,assay F (τ^2) b (U,V)*(u V*sdEq F Q b Φ i v τ (U,V))∂F.order G∂prior G c)=0 from ?_,mul_zero]
 suffices he:∀ V:Config G c,(∫ U,assay F (τ^2) b (U,V)*(u V*sdEq F Q b Φ i v τ (U,V))∂F.order G)=0 by simp_rw [he]; simp
 intro V
 simp_rw [show ∀ (R p:ℝ), R*(u V*p)=u V*(R*p) from fun R p=>mul_left_comm .. ,integral_const_mul]
 rw [show (∫ U,assay F (τ^2) b (U,V)*sdEq F Q b Φ i v τ (U,V)∂F.order G)=_ from eliminate G.probHaar i _
    (env_comp ((assay_env F b h _).mul (sd_safe F Q b Φ hΦ i v τ hA)) (measurable_id.prodMk measurable_const)) (fun U=>sd_held F Q b Φ hΦ i v τ hA h U V), mul_zero]
end YM.AveragedStep
