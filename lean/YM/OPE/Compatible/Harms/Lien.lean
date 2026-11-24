import YM.OPE.Compatible.Harms.Peal
/-!
# Activation along chase
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Work.F03
open Bloch Laurent Progress.DirectedRecipe Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat Matter
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Gas Ursell Trees Animals Corona Daisy Leaf
open Planned.GuardedAtom.Guard AnalyticBridge.VerifiedReset Geo
open Next.Rank.Thirst YM.OPE
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Push.Local Source
variable {G :Gauge}{X:Type}{L n c:Side}{k m:ℕ}{T S:StepData c n} {R:Rep G n}{β v w σ Λ K ξ0 a:ℝ}{b: ℕ→ℝ}
-- direct marker at any smooth
variable (p:ℂ→L[ℝ]ℝ) (g:Config G c)
variable {α γ t s : ℝ}{C:Labels.Frame G k}(V:SectionData C){o:Site n}{A:Hol G} {Y:Coefficient C n}
abbrev ζPiece (R:Rep G n)(F:Coefficient C n)(U:SectionData C) (o:Site n):Config G n→ℝ:= p∘F.exponentialEntry o U R
section
variable (ha: Y.remBound o R v w)(hF:Y.Format o A R)
include ha hF
lemma ζEnv: Envelope (ζPiece p R Y V o):=by
       let f:=V.places (C.scaled R.p.threshold⁻¹ (C.core Y.x)) o; let z:= masked R.p.threshold (V.footprint o) f; let TM (i):= Y.maskedTerm R i; let v:=fun i:Config G n=>∑' k,TM k i; have hQ(i:ℕ):Measurable (TM i):=masked_measurable _ _ _ (hF.smooth i).borel; obtain ⟨b,hb⟩:= (isCompact_range (V.continuous_places _ o).norm).bddAbove; obtain ⟨B,hB⟩:= (Coefficient.regular_series ha).bound; have hK:Measurable z:= masked_measurable _ _ _ (V.continuous_places ..|>.measurable); refine ⟨p.continuous.measurable.comp ((Measurable.add (measurable_const (a:=Y.x 0)) hK).add (Measurable.tsum hQ)),‖p‖*(‖Y.x 0‖+max 0 b + B),fun i=> (p.le_opNorm (Y.x 0 + z i + v i)).trans (mul_le_mul_of_nonneg_left ((norm_add_le ..).trans (add_le_add ((norm_add_le ..).trans (add_le_add le_rfl ?_)) (hB i))) (norm_nonneg _))⟩; by_cases h: Healthy R.p.threshold (V.footprint o) i
       · rw [show z i=f i from masked_eq _ _ _ _ h]; exact (hb ⟨i,rfl⟩).trans (le_max_right ..)
       rw [show z i=0 from masked_ne _ _ _ _ h,norm_zero]; exact le_max_left ..
variable (hS:S.IsKernel R.beta G)(hR:R.Lawful σ K Λ ξ0 β)
include hS hR
lemma κGrowth (hp:Cinch R S t a g)(ht:t≤R.p.supportExponent)(hy:0 ≤ S.push R.beta R.eval g):
      ‖p (S.push R.beta (Y.density o V R) g)-S.push R.beta (R.eval*ζPiece p R Y V o) g‖ ≤ (|a| * ‖p‖)*(v*w)*S.push R.beta R.eval g:=by
       have Hz:=ha; obtain ⟨k,h,hk,-,hh,hv,-,b,hb,hZ⟩:=Hz
       obtain ⟨F,hY⟩:= hiredS S p hF (fun i=> (hZ i).2); let e i:= p (Y.density o V R i); let f:=R.eval*ζPiece p R Y V o; let Z(i:Config G n):=∑' j,(F j).cicada i
       have hB : Summable fun i=>(F i).weight:= ((sumBudget_uncharge (fun i=>(hZ i).1) hb|>.2.1).mul_left ‖p‖).congr (fun i=> (hY i).2.2.symm)
       have hM : Dominated fun j (U:Config G n)=> (F j).cicada U:= dominateC F (fun i=>(hY i).1) hB hR
       have hz:= Coefficient.envelope V hR ha hF; obtain ⟨b',hb'⟩:=hz.cost
       have hY': p (S.push R.beta (Y.density o V R) g)=S.push R.beta e g:=by
            unfold StepData.push; rw [← p.integral_comp_comm (StepData.push_slice hS g _ (Integrable.of_bound hz.meas.aestronglyMeasurable b' (Eventually.of_forall hb')))]; simp_rw [ContinuousLinearMap.map_smul]; rfl
       have he: e=f+Z:=funext fun i=> pebbles V p _ (fun i=>(hY i).1) (fun i=>(hY i).2.1) hB ha hR i
       have hi:Envelope Z:=⟨Measurable.tsum (fun i=>(F i|>.sells hR).1.meas),hM.bound⟩
       let Q:= S.push R.beta R.eval g; rw[hY',he,StepData.push_add hS f Z (((R.envelope hR).mul (ζEnv p V ha hF)).integrable _) (hi.integrable _),Pi.add_apply,add_sub_cancel_left,← (push_Real hS hM (fun i=> (F i|>.sells hR).1.meas) g).tsum_eq]
       have hL(i:ℕ): ‖S.push R.beta (F i).cicada g‖≤ (|a| *Q*‖p‖) * (R.p.mass (R.activities.forced i).support (b i)):=by
            have hH:(F i).crest=(R.activities.forced i).support:=by unfold Leaf.crest; rw [(hY i).1]; rfl
            rw [BudgetPoint.mass]; apply (hp _).trans; rw [(hY i).2.2,hH]; change a*Q*_*_ ≤ _; rw [show |_| *Q*‖p‖*_= ((|a| * Q) * (Real.exp (R.p.supportExponent * coverNumber R.p.B ((F i).crest)))) * (‖p‖* b i) from ?_]
            · apply mul_le_mul_of_nonneg_right _ (mul_nonneg (norm_nonneg _) (hZ i).1); apply mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self _) hy); swap; · exact Real.exp_nonneg _
              swap; · exact mul_nonneg (abs_nonneg _) hy
              rw [hH]; exact Real.exp_monotone (mul_le_mul_of_nonneg_right ht (by positivity))
            rw [hH]; ring
       obtain ⟨_,hM,hS⟩:= budget_mono (budget_scale (mul_nonneg (mul_nonneg (abs_nonneg _) hy) (norm_nonneg _)) hb) (fun i=>norm_nonneg _) hL
       apply (norm_tsum_le_tsum_norm hM).trans (hS.trans _); apply le_trans (b:=|a| *Q*‖p‖*(v*w)); apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith only [hh,hk]) hv.le) (mul_nonneg (mul_nonneg (abs_nonneg _) hy) (norm_nonneg _)); exact le_of_eq (by unfold Q;ring)
end
lemma keeper (V:SectionData C)(F:Coefficient C n) (i:Config G n)(h: RG.flags R.p.threshold i=∅):R.eval i>0 ∧ F.density o V R i=(R.eval i:ℂ) * F.exponentialEntry o V R i:=by
    refine ⟨?_,?_⟩
    · unfold Rep.eval; rw [Activities.gas_one _ _ h,mul_one]; exact Real.exp_pos _
    have hg (p : Finset ℕ) : F.marked R p i=0:=by
       unfold Coefficient.marked; split; swap; · rfl
       rename_i ht; obtain hp|⟨j,hj⟩:=p.eq_empty_or_nonempty; subst p; exact sum_empty
       have hx : (R.activities.forced j).inventory⊆p.biUnion fun i=> (R.activities.forced i).inventory:= Finset.subset_biUnion_of_mem (fun i=> (R.activities.forced i).inventory) hj; rw [ht.2,h] at hx; exact ((R.activities.forced j).inventory_ne.ne_empty (subset_empty.mp hx)).elim
    unfold Coefficient.density; simp_rw [hg]; simp
end YM.PhysicalNext.Repeat.Aroma
