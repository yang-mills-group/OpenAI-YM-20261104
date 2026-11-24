import YM.OPE.Compatible.Lady.Coop
import YM.OPE.Compatible.Ingle.Hock
/-! # pan book scales before accepting. interior selection -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Lass
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge Tree
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{I:Type*}{j i k m n B:ℕ}{R v t s u r:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown Borealis Borealis.Galea Borealis.Lav
variable {K:Sponsor G}{T:Seasons K}
namespace Zest
section
open Source Labels Extra.Multi
variable {n:Side}{k b:ℕ}{X: Labels.Frame G k} (S:SectionData X)(o:Site n) {R:Rep G n}{h:Hol G}(P:Coefficient X n){a b' c:ℝ}
variable (hp:Pet o S P a c b' (R:=R) (H:=h))
include hp
abbrev budgetK (v:ℕ):= (4*v+2)*v+2*v
noncomputable abbrev Ξoff (U:BudgetPoint):= Real.exp (-(U.supportExponent*(U.B:ℝ)))
-- generic tails finite trunc for all supports
lemma stemQ (Q:Finset ℕ)(H:∀ i∈Q,coverNumber R.p.B (P.support i) ≤ R.p.B)(i)(hi:i∈Q): P.support i ⊆ Spindle.patch (budgetK R.p.B) o:=by
       intro j hj; rw [Spindle.doors]; rw [budgetK, mul_comm (_+_)]; exact (Corona.extent (P.support i) _ (hp.form.origin i) hj).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (H i hi)) _)
lemma Beacon (h':S.Sound h)(hℓ:S.footprint o⊆ Spindle.patch b o) (hd:budgetK R.p.B ≤ b):∀ᶠ K:Finset ℕ in atTop,∀ U:Config G n,
       let Q:= K.filter fun i=>coverNumber R.p.B (P.support i)≤R.p.B; Healthy R.p.threshold (Spindle.patch b o) U→ ‖P.exponentialEntry o S R U-GroveV o S P Q R U‖ ≤ Ξoff R.p*(1+b'):=by -- n rename
       obtain ⟨t,r,ht,hr,hB,hc,⟨e,he,hE⟩,hR⟩:=hp.cap
       let A:=R.activities; let Y:= R.p; let f(i):= Y.mass (P.support i) (e i); have hv:Summable f:= he.2.1; have he': Summable e:= hv.of_nonneg_of_le (fun i=> (hE i).1) (fun i=> Y.loMass _ _ (hE i).1)
       let η:= Ξoff Y; have hη:0< η:= Real.exp_pos _; have hs(i:ℕ)(K:Config G n): ‖P.maskedTerm R i K‖ ≤ e i:=by
              by_cases h:Healthy R.p.threshold (P.support i) K
              · unfold Coefficient.maskedTerm; rw [masked_eq _ _ _ _ h]; exact (hE i).2 K h [] (by simp) (by simp)
              rw [show P.maskedTerm R i K=0 from masked_ne _ _ _ _ h,norm_zero]; exact (hE i).1
       let B(i):=coverNumber R.p.B (P.support i); have hX(i:ℕ)(h:R.p.B ≤ B i) : e i ≤η*f i:=by
              unfold η f Ξoff BudgetPoint.mass; rw [←mul_assoc,← Real.exp_add]; apply le_mul_of_one_le_left (hE i|>.1); apply Real.one_le_exp; have hΩ:Y.supportExponent*Y.B ≤ Y.supportExponent*B i:= mul_le_mul_of_nonneg_left (Nat.cast_le.mpr h) Y.exponent_pos.le
              exact (by linarith only [hΩ])
       filter_upwards [(he'.hasSum.eventually (lt_mem_nhds (sub_lt_self (∑' i,e i) hη)))] with q hq U Q hF
       let g(i):=P.maskedTerm R i U; have hg: Summable (fun i=>‖g i‖):= he'.of_nonneg_of_le (fun _=>norm_nonneg _) (fun _=>hs _ _); have hY : (∑' i,g i) = (∑ i∈q,g i)+(∑' j: ((↑q: Set ℕ)ᶜ: Set ℕ), g j):= (hg.of_norm.sum_add_tsum_subtype_compl _).symm
       let Pq:= ((q:Set ℕ)ᶜ)
       let Pval (f:ℕ→ℂ):= ∑' i:Pq,f i.val; have hm: ‖Pval g‖ ≤ η:=by
              have hs1:Summable (fun i:Pq=> ‖g i.val‖):= hg.subtype _; have hs2:Summable (fun i:Pq=>e i.val):= he'.subtype _; apply (norm_tsum_le_tsum_norm hs1).trans; apply (hs1.tsum_le_tsum (fun i:Pq=> hs i.val U) hs2).trans; rw [← he'.sum_add_tsum_subtype_compl q] at hq; have hr:(∑ j∈q,e j)+(∑' i:Pq,e i.val)-η <∑ j∈q,e j:=hq; linarith only [hr]
       have hz:P.exponentialEntry o S R U=S.places (X.scaled R.p.threshold⁻¹ P.x) o U+∑' i,g i:=by
              unfold Coefficient.exponentialEntry; rw [masked_eq _ _ _ _ (hF.mono_left hℓ),Spells.coreG o S P R h']
       let z:=S.places (X.scaled R.p.threshold⁻¹ P.x) o U; have hh : GroveV o S P Q R U=z+∑ i∈Q,g i:=by
              unfold GroveV; rw [Pi.add_apply,Finset.sum_apply]; apply congr_arg (z+·); apply Finset.sum_congr rfl; intro i hi; have hp':P.support i⊆Spindle.patch b o:= (stemQ S o P hp Q (fun j hj=>(mem_filter.mp hj).2) i hi).trans (Corona.halo_mono hd (Finset.Subset.refl _)); exact (masked_eq _ _ _ _ (hF.mono_left hp')).symm
       let Pq':=∑ i∈q\ Q,g i; have hp' : P.exponentialEntry o S R U-GroveV o S P Q R U=Pq'+Pval g:=by
              rw [hz,hh,hY,show ∑ i∈q,g i=(∑ i∈q\ Q,g i)+∑ i∈Q,g i from (Finset.sum_sdiff (filter_subset ..)).symm]; change z+ (Pq'+_+_)-_= _; unfold Pval Pq; abel
       rw [hp']; apply (norm_add_le ..).trans; refine (add_le_add (b:=η*b') ?_ hm).trans_eq ?_
       · apply (norm_sum_le ..).trans; refine (Finset.sum_le_sum (g:=fun i=>η*f i) (fun i hi=>?_)).trans ?_
         · exact (hs i U).trans (hX i (Nat.le_of_lt (lt_of_not_ge (fun h=> (mem_sdiff.mp hi).2 (mem_filter.mpr ⟨(mem_sdiff.mp hi).1,h⟩)))))
         rw [←mul_sum]; exact mul_le_mul_of_nonneg_left ((hv.sum_le_tsum _ fun i _=>he.1 i).trans (he.2.2.trans (le_trans (le_add_of_nonneg_right hr) hB))) hη.le
       change _= η*(1+b'); ring
end
end Zest
end YM.OPE.Lass
