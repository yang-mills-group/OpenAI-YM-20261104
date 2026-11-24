import YM.OPE.Compatible.Glim.Beck
/-! # contour escaper in Gram.Asym. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion
open Flock Libra.Shell Next.Foundations Weir Score Exterior Bloch Next.Free Frequency Streamer AnalyticNext.QuarticMatch.Joint Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
variable {n:Side}(H:Even n.val)(T:Plot H)(p:T.Free)(x:Site n){t l c:ℝ}
local notation "L!"=> offZ H T (G:=G)
local notation "E!"=> Keys G T.Free
noncomputable abbrev chestZ := (spool G n).toContinuousLinearMap ∘L L!
variable (i:G.ColorIndex)
noncomputable abbrev bop : E! := An p (Phone G) i
abbrev BeamNear(c:ℝ) := ∀ i:edgeV n,pathX H i=p.val→ (n.val:ℝ)≤ c*(1+separation x i.1)
lemma tiny : ‖bop H T p i‖≤1:=by
     apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr; intro j; by_cases h:j=p; · subst j; rw [show bop H T p i p= _ from (show bop H T p i p=Phone G i from by simp[bop,An])]; exact ((Awake (G:=G)).norm_eq_one i).le
     rw [show bop H T p i j=0 from (show bop H T p i j=0 from by simp [bop,An,h])];simp
lemma crimp {e:edgeV n}(q:G.ColorIndex)(h:pathX H e ≠ p.val): chestZ H T (bop H T p i) (e.1,e.2,q)=0:=by
    let v:= bop H T p i; change L! v (whiz e) q=0; rw [hub_r]; suffices hj: hover H (T.rollX v) e =0 from congr_arg (fun c:G.Color=>c q) hj; have ht: T.rollX v (pathX H e)=0:=by
        by_cases ht:T.Branch (pathX H e); exact T.keptZ 0 v (⟨_,ht⟩:T.Stable)
        let j:T.Free:=⟨_,ht⟩; have hh:j≠p:=fun hv=>h (congr_arg Subtype.val hv); rw [show T.rollX v (pathX H e)=v j from T.kept 0 v j]; simp [v,bop,An,hh]
    unfold hover;rw[ht]; simp
set_option maxHeartbeats 200000 in
lemma Crumble (ha:BeamNear H T p x c)(hc:0≤c)(m:ℕ)(a:Keys G T.Free)(r:ℕ)(u:Page (Shade G) r)(w:Fin r):
     (n.val:ℝ)^m * ‖render x u (Function.update (fun _:Fin r=> chestZ H T a) w (chestZ H T (bop H T p i)))‖ ≤ c^m*Page.figure m u*(1+‖a‖)^r:=by
       let y:=chestZ H T (bop H T p i); let X:=Function.update (fun _:Fin r=>chestZ H T a) w y; let o(j:Fin r):Site n:=x+wrap n (u j).1; have ht(j:Fin r): ‖X j (o j,(u j).2)‖≤1+‖a‖:= by
           apply (norm_le_pi_norm ..).trans; by_cases h:j=w
           · subst j; rw [show X _ =y from update_self ..]; exact ((ray_norm H T _).trans (tiny H T p i)).trans (by simp)
           rw [show X _=chestZ H T a from update_of_ne h ..]; exact (ray_norm H T _).trans (le_add_of_nonneg_left zero_le_one)
       have hv:‖render x u X‖ ≤ (1+‖a‖)^r:=by unfold render; rw[norm_prod]; apply (prod_le_prod (fun i _=>norm_nonneg _) (fun i _=>ht i)).trans_eq; simp
       let k:edgeV n:=(o w,(u w).2.1); by_cases h:pathX H k=p.val; swap
       · rw [show render ..=0 from ?_,norm_zero,mul_zero]; exact mul_nonneg (mul_nonneg (pow_nonneg hc _) (zero_le_one.trans (Page.payer m u))) (by positivity)
         unfold render; refine prod_eq_zero (i:=w) (mem_univ _) ?_; rw [update_self]; exact crimp H T p i (e:=k) ((u w).2.2) h
       have he: (n.val:ℝ)^m ≤ c^m*Page.figure m u:=by
            have hh:separation x (o w)≤ size (u w).1:=by unfold o; rw [separation_comm,separation,add_sub_cancel_left]; exact within_size ..
            apply (pow_le_pow_left₀ (by positivity) (ha k h) m).trans; rw [mul_pow]; apply mul_le_mul_of_nonneg_left _ (pow_nonneg hc _); apply pow_le_pow_left₀ (by positivity); change (1:ℝ)+↑(separation x (o w)) ≤ (Page.stamp u:ℝ); exact_mod_cast (show 1+separation x (o w)≤Page.stamp u from (by rw [Page.perimeter];gcongr;exact hh.trans (Finset.single_le_sum (fun j _=>Nat.zero_le (size ((u j).1))) (mem_univ _))))
       exact mul_le_mul he hv (norm_nonneg _) (by have hh:=n.pos; exact (by positivity:(0:ℝ)≤(n.val:ℝ)^m)|>.trans he)
end YM.OPE.Variance
