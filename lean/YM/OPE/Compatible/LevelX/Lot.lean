import YM.OPE.Compatible.LevelX.Tol
/-!
# Ball top mean eta.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Drift
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Paver Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Pose Votive Alps Roles
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e t:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{v v':ℝ}{C:KernelChoices}{P:Patch}{R:ChartRatio G}{p:Clip}{b:ℝ}
variable (P:Flight i j)(K:KernelChoices)(h:4 ≤ i)(hp: 4 ≤ j)(hx:P.patch.Branches K G)
noncomputable abbrev journey (X: bed G k m):bed G k m:=⟨wagon P hp K G k m X.val, bedW P hp K X.val X.property hx⟩
include hx
lemma tJourney (x: bed G k m)(r:ℕ): terrace G k m r (journey P K hp hx x)=pipeX K G P hx hp (terrace G k m r x):=Subtype.ext (stool P hp K x.val (m:=m) r)
lemma survivor (X: bed G k m){e:ℕ}(he:e ≤ i)(hm:e ≤ m+1)(ht:X∈ fillet G k m e hm): journey P K hp hx X∈ fillet G k m e hm:=by
     unfold fillet at *; simp_rw [Submodule.mem_iInf,Submodule.mem_comap] at *; intro t; rw [tJourney]; exact survives hx hp _ ((Nat.sub_le ..).trans he) ((Nat.sub_le ..).trans hm) (ht t)
lemma priceS (X:bed G k m)(he:e ≤ i-1)(hm:e<m)(ht:X∈fillet G k m e (by omega))(hz:e ≤ d): stepRead G d e k m hm.le (journey P K hp hx X) = ((P.L.val:ℝ)⁻¹ ^ e) • stepRead G d e k m hm.le X :=by
     funext i; let C:= Flume.Script.tiller G i.val m (e-i.val) (by omega) d; let f:= terrace G k m i.val; let T:= coordinateQ G d e i.val; rw [Pi.smul_apply]; change T (C (f (journey P K hp hx X)))= _ • T (C (f X)); rw [show f _= _ from (tJourney _ _ hp hx X i.val)]; unfold C; rw [earnings hx hp (f X) ((Nat.sub_le ..).trans he) ((Nat.sub_le ..).trans_lt hm) _ ((Nat.sub_le ..).trans hz), map_smul, show i.val+(e-i.val)=e by have h:=i.isLt; omega]; exact (decrement X).1 ht i.val
-- payoff
omit hx in
lemma rides (G:Gauge)(C:KernelChoices)(t:ℕ)(h:t≤ i-2)(h1:4≤ i)(h2:4≤j)(k m:ℕ)(hk:t≤m) :∃ z:ℝ,0≤z∧∀ P:Flight i j,∀ x:bed G k m,x∈fillet G k m t (hk.trans (Nat.le_succ _))→∀ H:P.patch.Branches C G, ‖journey P C h2 H x‖ ≤ z*(P.L.val:ℝ)⁻¹^t * ‖x‖:=by
     choose B hp H using fun z:Fin (k+1) => Flume.Script.opus G.ColorIndex (v:=C.penalty) C.penalty_pos h1 h2 (show t-z.val ≤ i-2 by omega) (show t-z.val ≤ m by omega) z.val
     let c:= ∑ i,B i; have hc:0≤c:= Finset.sum_nonneg fun i _=> hp i; refine ⟨c,hc,fun P x ht hr=>?_ ⟩; let v:= journey P C h2 hr x; let L:ℝ := P.L.val; have hy: L ≥1:= by unfold L; exact_mod_cast P.L.pos
     let q:= lilies m k (Shade G); change ‖v.val‖≤ _; apply (pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg hc (by positivity)) (norm_nonneg _))).mpr; intro j; let p:= q x.val j.val; let z:=q v.val j.val; have hS:seed m j.val (Shade G) (v.val j)=opal G.ColorIndex P C.penalty p:=by rw [← stool P h2]; symm; rw [soup,moduleAt,dif_pos (Nat.le_of_lt_succ j.isLt)]; rfl
     have he:= H j P ‖x‖ p ((sproutV m k x.val).2 _) ((decrement x).1 ht j.val); rw [← hS] at he; change ‖v.val j‖≤ _; rw [← (Silt.Float.sprig m j.val (v.val j)).tsum_eq]; apply he.2.2.trans; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); rw [div_eq_mul_inv,← inv_pow]; exact mul_le_mul (single_le_sum (f:=B) (fun i _=>hp i) (mem_univ _)) (pow_le_pow_of_le_one (by positivity) (inv_le_one_of_one_le₀ hy) (by omega)) (by positivity) hc -- names
end YM.OPE.Drift
