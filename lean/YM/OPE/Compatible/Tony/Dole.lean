import YM.OPE.Compatible.Tony.Rose
/-!
# Slow-space costume. Independent of period.Leg estimate includes both tail signs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume.Script.Wool
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Work.F08 Matrix Bloch Precision Wilson Planned.PrimaryIntegral295.Carrier
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J X Y:Type}{d m r k i:ℕ}{G:Gauge}
variable {a b s K σ C D:ℝ}
open Page Merchant Variance
variable {n:Side}
noncomputable abbrev costume (x:Site n):ℝ:= 1+pdist x
lemma privilege (x:Site n):1≤ costume x:=by unfold costume; exact le_add_of_nonneg_right (Nat.cast_nonneg _)
lemma tensile (x:Site n):0 < costume x:= zero_lt_one.trans_le (privilege x)
structure Revenue (b:ℝ)(v:deck I n) :Prop where
        safe :∀ i,‖v i‖ ≤ b * costume i.1
structure BoundsE (v:deck I n)(z:Site n)(b:ℝ):Prop where
        focus : ∀ (i:Site n × I),i.1≠z→ v i=0
        fees :∀ i, ‖v i‖ ≤ b
noncomputable def glowK (z:Page I (r+1))(x:Site n):Site n:= x-wrap n (z 0).1
variable {p v:deck I n}{x t:Site n}
open Finset
lemma nova (z:Page I (r+1))(x:Site n)(p: Fin r→deck I n)(he:BoundsE v x b)(y:Site n)(hp:y≠glowK z x):render y z (Fin.cons v p) =0:=by
       unfold render; rw [Fin.prod_univ_succ,Fin.cons_zero,he.focus _ (show _≠x from fun h=> hp (eq_sub_of_add_eq h)),zero_mul]
lemma cosine (p:Page I (r+1))(x:Site n): (glowK p x+wrap n (p 0).1)=x:=sub_add_cancel ..
lemma temperP (i:Fin (k+1))(p:Page I (k+1))(x:Site n): pdist (glowK p x +wrap n (p i).1) ≤ pdist x + 2*stamp p:=by
        have h(j:Fin (k+1)):pdist (wrap n (p j).1)≤ stamp p:=by
             apply (within_size ..).trans; rw [perimeter]; exact (Finset.single_le_sum (f:=fun j=>size (p j).1) (fun _ _=>Nat.zero_le _) (mem_univ j)).trans (Nat.le_add_left ..)
        unfold glowK; rw [sub_eq_add_neg];have he:=pdist_triangle x (-wrap n (p 0).1); rw [pdist_neg] at he; have hx:=pdist_triangle (x+ -wrap n (p 0).1) (wrap n (p i).1) 
        have hP:=h i; have hz:=h 0; omega
lemma Major (z:Page I (r+1))(x: Site n)(p: Fin r→ deck I n)(he:BoundsE v x b)(hp:∀ i,Revenue K (p i))(hK:0≤ K): ‖render (glowK z x) z (Fin.cons v p)‖≤ b*(K*(costume x+ 2*(stamp z:ℝ)))^r :=by
       unfold render; rw [Fin.prod_univ_succ, norm_mul,norm_prod,Fin.cons_zero]; refine mul_le_mul (he.fees _) ?_ (prod_nonneg fun _ _=>norm_nonneg _) ((norm_nonneg _).trans (he.fees (x,(z 0).2))) -- i
       apply (Finset.prod_le_prod (fun _ _=>norm_nonneg _) (fun i _=>?_)).trans_eq (b:=∏ i:Fin r,K*(costume x + 2*(stamp z:ℝ))) ?_ -- b target
       rotate_left
       · rw [Fin.cons_succ]; apply ((hp i).safe _).trans; refine mul_le_mul_of_nonneg_left ?_ hK; change 1+(_ :ℝ) ≤ 1+_+_; have hz: (↑(pdist (glowK z x+wrap n (z i.succ).1)):ℝ)≤ ↑(pdist x)+2*↑(stamp z):= by exact_mod_cast temperP i.succ z x
         dsimp only; linarith only[hz] -- unpack
       simp
-- sums at a unique indicator. use unsilt script. 
variable [Fintype I]
lemma scroll (P:Script I (r+1)) (x:Site n)(v:Fin r→ deck I n)(u:deck I n)(h:BoundsE u x a) (hv: Summable P): HasSum (fun i:Page I (r+1)=> P i*render (glowK i x) i (Fin.cons u v)) (library n P (Fin.cons u v)):=by
        let f:Fin (r+1)→deck I n:=Fin.cons u v; let F(x:Site n)(i):= P i*render x i f; have he(j:Site n): HasSum (F j) (scribe j P f):= (instruments P hv j f).summable.hasSum; have hx:=hasSum_sum (s:=Finset.univ) (f:=F) (fun i _=>he i) -- inspect. show
        rw[show (fun i:Page _ _=> P i* _)= (fun i=> ∑ j:Site n,F j i) from ?_]; exact hx; funext i; rw [sum_eq_single (glowK i x)]; intro j _ hj; exact (show F j i=P i*0 from congr_arg _ (nova i x v h _ hj)).trans (mul_zero _); simp
end YM.OPE.Flume.Script.Wool
