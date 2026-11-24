import YM.IntegrationR2.Assemble

/-!
The subtraction `breakP` is on whole coefficients. Need to pay Format/Tab
separately; here verify its density semantics. No summability of unmasked
values (regular extension off the Healthy domains) claimed.
-/

set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Matric.R2
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d} (B:SectionData F){n:Side}{P Q:Coefficient F n}{R:Rep G n}
  {o:Site n}{k r s l w σ A A' U U':ℝ}
lemma eval_sub (h:P.support=Q.support) (hr:R.Lawful σ A A' U U') (hp:P.remBound o R k r) (hq:Q.remBound o R l s) :
    (breakP P Q).density o B R=P.density o B R-Q.density o B R:=by
  let E:= breakP P Q
  funext x
  have hh(i): E.maskedTerm R i= P.maskedTerm R i-Q.maskedTerm R i:=by
     change maskLinear R.p.threshold (P.support i) (P.regular i-Q.regular i)=_
     rw [map_sub, show maskLinear R.p.threshold (P.support i) (Q.regular i)= Q.maskedTerm R i from (by rw [h]; rfl)]
     rfl
  have hz(T:Coefficient F n): T.exponentialEntry o B R x=part B o R x T.x +∑' i,T.maskedTerm R i x:=rfl
  have hX:E.exponentialEntry o B R x=P.exponentialEntry o B R x-Q.exponentialEntry o B R x:=by
     simp_rw [hz,hh,Pi.sub_apply,show E.x=P.x-Q.x from rfl,map_sub]; rw [Summable.tsum_sub ((P.regular_series hp).summable x) ((Q.regular_series hq).summable x)]; abel
  have hd:= rem_dominated hp; have he:= rem_dominated hq
  have hv:Dominated E.forced:=by
     obtain ⟨a,ha,hA⟩:=hd; obtain ⟨b,hb,hB⟩:=he
     exact ⟨a+b,ha.add hb,fun i x=>(norm_sub_le ..).trans (add_le_add (hA ..) (hB ..))⟩
  change E.density o B R x=_
  simp only [Pi.sub_apply,Coefficient.density,hX,dress_eq hr hd,dress_eq hr he,dress_eq hr hv,show ∀ i, E.forced i x=P.forced i x-Q.forced i x from fun _=>rfl,sub_mul]; rw [Summable.tsum_sub ((dress_abs hr hd).summable x) ((dress_abs hr he).summable x)]; ring

lemma blast_diff (H:History G) (N p m d:ℕ) (S T: Config G (H.S.side (m+1) p)→ℂ) (he:Integrable S (prior G _)) (hd:Integrable T (prior G _)) : blast H N p m d (S-T)= blast H N p m d S-blast H N p m d T:=by
   unfold blast
   rw [sub_eq_add_neg S, ← neg_one_smul ℂ T,StepData.push_add (H.levels.transition_mass ..) _ _ he (hd.smul (-1:ℂ)),StepData.push_smul _ _ _ _ hd, neg_one_smul,← sub_eq_add_neg, smul_sub]
end YM.MergeProof.Matric.R2
