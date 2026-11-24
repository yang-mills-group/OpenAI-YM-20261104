import YM.OPE.Compatible.Tillage.Orbit
/-!
# Tip: tape-measure. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Work.F05 Votive Tree Frequency
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{n c f L:Side}{P:Patch}{K:KernelChoices}{I J M W:Type}{m k r d:ℕ}{σ C s u z:ℝ}
namespace Script
open Page Virgin
section
variable {X v : M→ℝ}
lemma tipRoot {S:M→Row I I}(h:Tip s S v X)(hp:0≤v)(hg:1 ≤ X): Tip s (fun i=> ROOT (I:=J) (S i)) v X:=by
    obtain ⟨c,hc,k,H⟩:= h; refine ⟨c,hc,k,fun i a b=>?_⟩; have hz: 0 ≤ c*(X i^k)*v i:= mul_nonneg (mul_nonneg hc (zero_le_one.trans (one_le_pow₀ (hg i)))) (hp i); rcases a with a|a<;> rcases b with b|b
    any_goals apply H i a b
    all_goals change Width s (c*_*_) (0:Cover→ℝ); simp [Width,SumBudget,hz]
lemma roots_tipδ {S T:M→Row I I}(h:Tip s (S-T) v X)(hp:0≤v)(hg:1 ≤ X): Tip s (fun i=> ROOT (I:=J) (S i)-ROOT (I:=J) (T i)) v X:=by
    have he : (fun i=>ROOT (I:=J) (S i)-ROOT (I:=J) (T i))=fun i=> ROOT ((S-T) i):=by ext i (x|x) (y|y) j <;> first | rfl |simp [ROOT,toLeft]
    rw [he]; exact tipRoot h hp hg
section
variable [Fintype I][Fintype J][Fintype W]
omit [Fintype I] [Fintype W] in
lemma compose_subT {U V: Row I J} {Q: Row J W}(h:Whole U)(he:Whole V)(hp: Whole Q): composeRows U Q-composeRows V Q= composeRows (U-V) Q:=by
    apply bank_injective ((h.prod hp).minus (he.prod hp)|>.safe) ((h.minus he).prod hp|>.safe); intro i; erw [(h.prod hp).less (he.prod hp), h.acts hp,he.acts hp,(h.minus he).acts hp,h.less he,Matrix.sub_mul] -- args
omit [Fintype I] [Fintype W] in
lemma Tip.commote {P:M→Row I J}{Q:M→Row J W}{p:M→ℝ}(hp:0 ≤ σ)(h:Tip σ P v X)(hy:Tip σ Q p X):Tip σ (fun i=>composeRows (P i) (Q i)) (v * p) X:=by
    obtain ⟨c,hc,n,H⟩:= h; obtain ⟨b,hb,j,G⟩:=hy; refine ⟨Fintype.card J*c*b,by positivity,n+j,fun i=>?_⟩; apply strip_mono (strip_compose hp (H i) (G i)) le_rfl; exact le_of_eq (by simp only [Pi.mul_apply]; ring)
omit [Fintype I] [Fintype W] in
lemma tip_mon {P:M→Row I W}(hp: σ ≤ s)(h:Tip s P v X): Tip σ P v X:=by -- p
    obtain ⟨c,hc,n,H⟩:=h; exact ⟨c,hc,n,fun i=> strip_mono (H i) hp le_rfl⟩
end
end
-- assemble uniforms. 
variable (C: Medal P G K P.J) {X v:M→ℝ}
lemma tipsDelta (h:0<s) (hx:1≤X)(hv:0 ≤ v)(Z Y:M→ Train P.J) (hk:Tip s (fun i=> Op K (Z i) - Op K (Y i)) v X):∃ e:ℝ,0<e∧ Tip e (fun i=>C.V (Z i)) 1 X ∧ Tip e (fun i=> C.V (Y i)) 1 X ∧ Tip e (fun i=> C.V (Z i)-C.V (Y i)) v X ∧ Tip e (fun i=>sifter C (Z i)) 1 X∧Tip e (fun i=>sifter C (Y i)) 1 X∧Tip e (fun i=> sifter C (Z i)-sifter C (Y i)) v X:= by
    obtain ⟨t,D,ht,H⟩:= Medal.line_p P K G; let e:=min (min t s) C.width; have he:0<e:= lt_min (lt_min ht h) C.toll; have hh(P:M→Train P.J):Tip e (fun i=>C.V (P i)) 1 X:=⟨max C.crown 0, le_max_right _ _,0,fun i=>strip_mono (C.price _) (min_le_right ..) (by simp)⟩
    have heq: Tip e (fun i=> C.V (Z i)- C.V (Y i)) v X:=by
       obtain ⟨a,ha,n,H'⟩:= hk; let A:ℝ:= |C.visits|; refine ⟨A*a, mul_nonneg (abs_nonneg _) ha,n,fun i=>?_⟩; have hc : 0≤ a*(X i^n)*v i:= mul_nonneg (mul_nonneg ha (zero_le_one.trans (one_le_pow₀ (hx i)))) (hv i)
       refine strip_mono (C.approach (Z i) (Y i) P.order_cut he (min_le_right ..) (A:=a*X i^n*v i) ?_) le_rfl ( (mul_le_mul_of_nonneg_right (le_abs_self C.visits) hc).trans_eq (by unfold A; ring))
       have hf:=strip_mono (H' i) (le_trans (min_le_left (min t s) C.width) (min_le_right t s)) le_rfl
       intro x y; simp_rw [Width,Pi.sub_apply,norm_sub_rev (Op K (Y i) x y _)]; exact hf ..
    have hc : Tip e (fun _:M=> Medal.line P K G) 1 X:=⟨max 0 D,le_max_left ..,0,fun i=> strip_mono H (le_trans (min_le_left ..) (min_le_left ..)) (by simp)⟩
    have hu(Z:M→ Train P.J):Tip e (fun i=>sifter C (Z i)) 1 X:=by
       have hf:Tip e (fun i=> C.rowNet (Z i)) 1 X:= one_mul (1:M→ℝ) ▸ (hh Z).commote he.le hc
       obtain ⟨c,hc,n,H⟩:= hf; let q:=max 1 c; refine ⟨q,zero_le_one.trans (le_max_left ..),n,fun i a b=>?_⟩; have h: 1 ≤ X i^n:=one_le_pow₀ (hx i); rw [Pi.one_apply,mul_one]; rcases a with a|a
       · refine (Work.F08.strip_mono (P:=unitRow _) ?_ le_rfl (show 1≤q*X i^n from one_le_mul_of_one_le_of_one_le (le_max_left ..) h)) a b
         exact fun _ _=> Work.F08.strip_unit ..
       exact strip_mono (H i) le_rfl (A':=q*X i^n) (by simp only [Pi.one_apply,mul_one]; exact mul_le_mul_of_nonneg_right (le_max_right ..) (zero_le_one.trans h)) a (mus G b)
    refine ⟨e,he,hh _,hh _,heq,hu Z,hu Y,?_⟩; have hf :Tip e (fun i=>composeRows (C.V (Z i)-C.V (Y i)) (Medal.line P K G)) v X:= mul_one v ▸ heq.commote he.le hc
    obtain ⟨c,hc',n,H'⟩:=hf; refine ⟨c,hc',n,fun i a b=>?_⟩; rcases a with a|a
    · have ht: 0≤ c*X i^n*v i:=mul_nonneg (mul_nonneg hc' (zero_le_one.trans (one_le_pow₀ (hx i)))) (hv i); change Width _ _ (unitRow _ a b-unitRow _ a b); simp [Width,SumBudget,ht]
    have h:= compose_subT (C.whole (Z i)) (C.whole (Y i)) (Medal.line_p P K G); have hh:(composeRows (C.V (Z i)-C.V (Y i)) (Medal.line P K G)).strip e _:=H' i; rw [← h] at hh; exact hh a (mus G b)
end Script
end YM.OPE.Flume
