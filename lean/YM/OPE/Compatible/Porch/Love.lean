import YM.OPE.Compatible.Porch.Hub
import Mathlib.Analysis.Calculus.Taylor
/-!
# Energy Taylor size. sparse laws.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Zeph
open Function Filter Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Matrix Bloch Precision Exterior Tree
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra GaussianScore Metric Push Push.AbsoluteSums
variable {G:Gauge}{c f:Side}
attribute [local instance] Gauge.frobInner
open Radial Flume.Virgin Set
open PhysicalNext.Repeat.Aroma
open YM.AnalyticNext.QuarticMatch Radius Radius.Articles Radius.Polish Radius.Fetch Radius.Showroom Estimate Sheets Radius.Model
open Woody Next.Free Finset Work.F03 Progress.StationaryScenes AnalyticNext.QuarticMatch.Local
variable {t r R B b ε:ℝ}{m:ℕ}
variable {S:StepData c f} {F: Forest S.ratio} {k:S.Choices}
local notation "Q" =>(Bid.Dir G c × AxisChart G F)
namespace Dew
section
variable {X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X]
lemma Railing (x:X)(p:X→ℝ)(t:ℝ)(hp:ContDiffAt ℝ ω p (t • x))(j:ℕ) : iteratedDeriv j (fun t:ℝ=>p (t • x)) t= iteratedFDeriv ℝ j p (t • x) (fun _=>x):=by
        let A:=ContinuousLinearMap.toSpanSingleton ℝ x; unfold iteratedDeriv; erw [lin_rate_at p A t hp]; refine congr_arg _ (funext fun i=>?_); change (1:ℝ) • x=x; simp
lemma toll_W (x:X)(p:X→ℝ)(ht:0<ε)(k:ℕ)(C:ℝ)(hC:0 ≤ C) (hf:∀ v∈Icc 0 ε,ContDiffAt ℝ ω p (v • x))(hp:∀ v∈Icc 0 ε, ‖iteratedFDeriv ℝ (k+1) p (v • x) (fun _=>x)‖ ≤ C) :
      ‖p (ε • x)- ∑ i∈ range (k+1), ε^i*jet p i x‖ ≤ C*ε^(k+1):=by
          let I:= Set.Icc 0 ε; let f:=fun t:ℝ=> p (t • x); have he(x':ℝ)(hv:x'∈I):ContDiffAt ℝ (↑(k+1:ℕ)) f x':= ((hf _ hv).comp (f:=fun t:ℝ=>t • x) x' (contDiffAt_id.smul contDiffAt_const)).of_le le_top
          have h0 :0∈ I:= left_mem_Icc.mpr ht.le
          have hx(i:ℕ)(hi:i≤ k+1)(x':ℝ)(hv:x'∈ I):iteratedDerivWithin i f I x'=iteratedFDeriv ℝ i p (x' • x) (fun _=>x):=by rw [iteratedDerivWithin_eq_iteratedFDerivWithin,iteratedFDerivWithin_eq_iteratedFDeriv (uniqueDiffOn_Icc ht) ((he x' hv).of_le (Nat.cast_le.mpr hi)) hv, ← iteratedDeriv_eq_iteratedFDeriv]; exact Railing x p x' (hf _ hv) i
          have hg:= taylor_mean_remainder_bound (n:=k) (f:=f) ht.le (fun x hx=>(he x hx).contDiffWithinAt) (right_mem_Icc.mpr ht.le) (C:=C) fun i hi=>by rw [hx _ le_rfl _ hi]; exact hp i hi
          have hz:taylorWithinEval f k I 0 ε=∑ i∈range (k+1), ε^i* jet p i x:=by rw [taylor_within_apply]; refine Finset.sum_congr rfl fun i hi=>?_ ; rw [hx _ (mem_range.mp hi|>.le) 0 h0,sub_zero]; unfold jet; rw[zero_smul]; rw [smul_eq_mul]; ring
          rw [← hz]; rw [sub_zero] at hg; exact hg.trans ((div_le_iff₀ (by exact_mod_cast k.factorial_pos)).mpr (le_mul_of_one_le_right (by positivity) (by exact_mod_cast k.factorial_pos)))
end
section
variable {Y E: (Bid.Dir G c × AxisChart G F)→ℝ}{f' g:Site f→ (Bid.Dir G c × AxisChart G F)→ℝ}
lemma Pile.dorm (H:Pile S F r R t m Y f'){x y:Q}(hh:‖x‖<r)(p:Site f→ℝ)(hk:0 ≤ p)(he:∀ i,On S F G t i y (p i)) (j:ℕ)(hj:j ≤ m): ‖iteratedFDeriv ℝ j Y x (fun _=>y)‖ ≤ R * ∑ i,p i ^ j:=by
        rw [H.dunk hh,_root_.sum_apply,mul_sum]; apply (norm_sum_le ..).trans; apply Finset.sum_le_sum; intro i _; let z:= H.voice i x hh j hj; simpa only [Radius.Polish.budget,prod_const,Fintype.card_fin,card_univ] using z (fun _=>y) (fun _=>p i) (fun _=>⟨hk i, he i⟩)
lemma Pile.SignedLaw (H:Pile S F r R t m Y f') (hx:0 ≤ R)(x:Q)(ht:0<ε)(hr:ε*‖x‖<r)(p:Site f→ℝ)(hk:0≤p)(he:∀ i,On S F G t i x (p i)) (n:ℕ)(hn:n+1≤ m):
    ‖Y (ε • x)-∑ j∈ range (n+1),ε^j*jet Y j x‖ ≤ R*(∑ i, p i^(n+1))*ε^(n+1):=by
          have hh(q:ℝ)(hq:q∈ Icc 0 ε): ‖q • x‖<r:=by rw [norm_smul,Real.norm_of_nonneg hq.1]; exact (mul_le_mul_of_nonneg_right hq.2 (norm_nonneg _)).trans_lt hr
          exact toll_W x Y ht n _ (mul_nonneg hx (sum_nonneg (fun i _=> pow_nonneg (hk i) _))) (fun i hi=> H.smokes (hh i hi)) (fun i hi=> H.dorm (hh i hi) p hk he _ hn)
lemma Pile.atX (H:Pile S F r R t m Y f')(x:Q)(hr:0<r)(p:Site f→ℝ)(hk:0≤p)(he:∀ i,On S F G t i x (p i)) (n:ℕ)(hn:n ≤ m): ‖jet Y n x‖ ≤ R*∑ i, p i^n :=by unfold jet; have hh:=H.dorm (show ‖(0:Q)‖<r by rw[norm_zero];exact hr) p hk he n hn; rw [norm_mul]; refine le_trans (mul_le_of_le_one_left (norm_nonneg _) ?_) hh; rw [Real.norm_of_nonneg (by positivity)]; exact inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr n.factorial_pos)
end
end Dew
end YM.OPE.Zeph
