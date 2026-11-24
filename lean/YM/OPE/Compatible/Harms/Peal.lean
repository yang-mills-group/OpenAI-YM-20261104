import YM.OPE.Compatible.Month.Goblin
import YM.Extra.SOURCE_HISTORIES.Play
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
section
variable (P:ℕ→Leaf S R)(hg:∀ i,(P i).turn=Wing.gasKey i)(he:Summable fun i=>(P i).weight)(hR:R.Lawful σ K Λ ξ0 β)
include hg he hR
-- joint.Supp.Co
lemma dodder : Dominated fun (i:ℕ × Finset ℕ) (U:Config G n)=> (P i.1).bun i.2 U:=by
       let A:=R.activities; obtain ⟨q,hq,h⟩:= R.activities.K_total hR.labels.boundK
       let z i:= (P i).weight+q i; have hz i:0≤z i:=add_nonneg ((P i).profit) (h i).1; have hp:Summable z:= he.add hq
       let g (x:Finset ℕ):= ∏ i∈x, z i; have hf x:0≤ g x:=Finset.prod_nonneg fun i _=> hz i; let w (x:Finset ℕ×ℕ):ℝ:=if x.2∈x.1 then g x.1 else 0; have hw x: 0≤ w x:=by unfold w; split; exact hf _; rfl
       have hx (x:Finset ℕ): HasSum (fun i=> w (x,i)) ((x.card:ℝ)*g x):=by
            convert hasSum_sum_of_ne_finset_zero (s:=x) (fun i hi=>show w (x,i)=0 from if_neg hi) using 1; rw [← nsmul_eq_mul,← Finset.sum_const]; exact Finset.sum_congr rfl (fun i h=>(if_pos h).symm)
            infer_instance
       have ht:Summable (fun x:Finset ℕ=> (x.card:ℝ)*g x):=(summable_finsetProd_of_summable_nonneg (f:=fun i=>2*z i) (fun i=> mul_nonneg zero_le_two (hz i)) (hp.mul_left 2)).of_nonneg_of_le (fun i=> mul_nonneg (Nat.cast_nonneg _) (hf i)) (fun i=>by rw [prod_mul_distrib,Finset.prod_const]; apply mul_le_mul_of_nonneg_right _ (hf _); exact_mod_cast (Nat.lt_two_pow_self).le)
       have hh: Summable w:= (summable_prod_of_nonneg hw).2 ⟨fun i=>(hx i).summable,ht.congr (fun x=>(hx x).tsum_eq.symm)⟩
       refine ⟨_,hh.prod_symm,?_⟩; rintro ⟨j,x⟩ U; change ‖(P j).bun x U‖≤ w (x,j); unfold bun; split_ifs
       next hb=> unfold Leaf.bill; split
                 next hh => have hi:(Wing.gasKey j).Occupied x:= (hg j) ▸ hh; change j∈x at hi; unfold w; dsimp only; rw [if_pos hi,hg j,Wing.remaining,norm_mul,norm_prod]; unfold g; rw[← Finset.mul_prod_erase x _ hi]; exact mul_le_mul (((P j).earn U).trans (le_add_of_nonneg_right (h _).1)) (prod_le_prod (fun i _=> norm_nonneg _) (fun i _=> ((h i).2 U).trans (le_add_of_nonneg_left (P i|>.profit)))) (prod_nonneg fun i _=>norm_nonneg _) (hz j)
                 next _=> rw [norm_zero]; exact hw _
       rw [norm_zero]; exact hw _
lemma dominateC : Dominated fun j (U:Config G n)=> (P j).cicada U:=by
       obtain ⟨v,hv,h⟩:=dodder P hg he hR; obtain ⟨z,hz⟩:=(R.exponentEnv hR |>.exp).cost; have hp:0≤z:=(norm_nonneg _).trans (hz 1)
       let Q i:=∑' j,v (i,j); have hk:Summable Q:=hv.prod; refine ⟨_,hk.mul_left z,fun i U=>?_⟩; unfold cicada; rw [norm_mul]; apply mul_le_mul (hz _) _ (norm_nonneg _) hp; apply (norm_tsum_le_tsum_norm ((P i).bud hR|>.absolute U)).trans; exact Summable.tsum_le_tsum (fun j=>h (i,j) _) ((P i).bud hR|>.absolute U) (hv.prod_factor i)
end
variable {C:Labels.Frame G m}(V:SectionData C){A:Hol G}{o:Site n}{Pm:Coefficient C n}
-- launch μ
lemma hiredS (S:StepData c n)(p:ℂ→L[ℝ]ℝ) (hz: Pm.Format o A R)(hw:∀ i U,‖Pm.forced i U‖≤ b i):∃ F:ℕ→ Leaf S R,∀ i,(F i).turn=.gasKey i ∧ (F i).ingredient=p ∘ Pm.forced i∧ (F i).weight=‖p‖*b i:=by
       refine ⟨(fun i=> ⟨.gasKey i,_,?_,?_,trivial,_,?_,?_,p.continuous.measurable.comp (hz.borel i)⟩),fun i=>⟨rfl,rfl,rfl⟩⟩
       · exact fun u v hu he=> congr_arg p (hz.supported i u v hu he)
       · intro U h; apply hz.forcing i; intro he; apply h; rw [Function.comp_apply,he,map_zero]
       · intro U; exact (p.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hw _ _) (norm_nonneg _))
       intro t _ u; exact congr_arg p (hz.invariant i t u) -- pose
lemma κapply (p:ℂ→L[ℝ]ℝ)(x:ℝ)(y:ℂ):p ((x:ℂ)*y)=x*p y:=p.map_smul x y
lemma pebbles (p:ℂ→L[ℝ]ℝ)(F:ℕ→Leaf S R) (hf:∀ i,(F i).turn=.gasKey i)(ht:∀ i,(F i).ingredient=p∘Pm.forced i) (hk:Summable fun i=>(F i).weight) (ha:Pm.remBound o R v w)(hz:R.Lawful σ K Λ ξ0 β)(U:Config G n):
       p (Pm.density o V R U)=R.eval U*p (Pm.exponentialEntry o V R U)+∑' j,(F j).cicada U:=by
       have hM: Summable fun b=> Pm.marked R b U:=by
            obtain ⟨n,m,-,-,-,-,-,h⟩:=ha; exact ((Push.Local.dominated_gasMark (show Push.Local.ForceCost R.p R.activities Pm.forced (v*m) from h) hz.labels.boundK).summable U).congr fun i=> Push.Local.gasMark_eq ..
       have hv(p:Finset ℕ)(i:ℕ)(hx:i∉p): (F i).bun p U=0:=by simp [bun,Leaf.bill,hf,Wing.Occupied,hx]
       let g (i:ℕ)(j:Finset ℕ):=(F i).bun j U; have he:Summable (uncurry g):= (dodder F hf hk hz).summable U
       unfold Coefficient.density; rw[map_add,κapply,κapply,p.map_tsum hM]; simp_rw[cicada,tsum_mul_left]; change _= _+_* (∑' i,∑' j,g i j); rw[← he.tsum_comm]; apply congr_arg; apply congr_arg; apply tsum_congr; intro j; unfold Coefficient.marked; rw [tsum_eq_sum (s:=j) (fun i hi=>hv j i hi)]; split
       next h => rw [map_sum]; apply sum_congr rfl; intro i hi; unfold bun Leaf.bill; rw [if_pos h, if_pos ((hf i).symm ▸ (hi:Wing.Occupied (.gasKey i) j)),hf i,ht i,mul_comm (Pm.forced ..),← Complex.ofReal_prod,κapply,mul_comm]; rfl
       next h => rw [map_zero]; exact (Finset.sum_eq_zero (fun i _=>show g i j=0 from if_neg h)).symm
end YM.PhysicalNext.Repeat.Aroma
