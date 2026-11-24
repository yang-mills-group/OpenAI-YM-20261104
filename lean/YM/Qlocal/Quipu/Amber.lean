import YM.Next.STATIONARY.Shape.GaugeJets
import YM.Qlocal.Quipu.Pear
/-!
# Complex extension along each full path

The extension acts on the entire path and does not require an analytic extension
of the log, which cannot survive for long paths. Existence of sums
is through price, including uniform estimates on analytic balls.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Quipu.Lasso
open Function Filter Lattice Laurent RG Wilson Stationary Metric Work Work.F02
open scoped Topology BigOperators Classical ENNReal ContDiff Matrix.Norms.Frobenius
variable (G:Gauge) (d:ℕ) {n:Side}

def patience (i: G.ColorIndex)(k:ℕ) :=
   let L : Tensor.T G.Color G.Color k:= Tensor.coeff (carryOn G) k 0
   let V : Corn G.ColorIndex≃L[ℝ] G.Color:= (PiLp.continuousLinearEquiv 2 ℝ _).symm
   listen (enlarge (((PiLp.proj 2 (fun _:G.ColorIndex=>ℝ) i (𝕜:=ℝ)).compContinuousMultilinearMap (L.compContinuousLinearMap fun _=> V.toContinuousLinearMap)).toMultilinearMap)) -- parenthesis

lemma plateau (i:G.ColorIndex)(v:G.Color)(k:ℕ): patience G i k (fun _=> colorUp G v)= ((Tensor.coeff (carryOn G) k 0 (fun _=>v) i:ℝ):ℂ):= by
   let f:= G.Color; unfold patience
   let V : Corn G.ColorIndex≃L[ℝ] G.Color:= (PiLp.continuousLinearEquiv 2 ℝ _).symm
   let L : Tensor.T G.Color G.Color k:= Tensor.coeff (carryOn G) k 0
   let R := (PiLp.proj 2 (fun _:G.ColorIndex=>ℝ) i (𝕜:=ℝ)).compContinuousMultilinearMap (L.compContinuousLinearMap fun _=> V.toContinuousLinearMap)
   have hv:colorUp G v=axes (V.symm v):=rfl
   change enlarge R.toMultilinearMap _=_; simp_rw [hv]; exact enlarge_real R.toMultilinearMap (fun _=>V.symm v)

def summitV (x:CColor G) (i:G.ColorIndex):ℂ:= ∑ k∈Finset.range (d+1), patience G i k (fun _=>x)
lemma summitCurve : ContDiff ℂ ω (summitV G d):= by
    apply contDiff_pi.mpr; intro i; unfold summitV; apply ContDiff.sum; exact fun k _=> (patience G i k).contDiff.comp (contDiff_pi.mpr (fun _=> contDiff_id))
lemma summitReal (x:G.Color): summitV G d (colorUp G x)= colorUp G (theta G d x):= by
    ext1 i; rw [summitV]; unfold theta G05.blockTaylor; rw [Finset.sum_apply, map_sum (colorUp G),Finset.sum_apply]; exact Finset.sum_congr rfl fun j _=> plateau G i x j

def offBank (i:G.ColorIndex):ℝ:=∑ k∈Finset.range (d+1), ‖patience G i k‖
def thistle:= 1+∑ i,offBank G d i
lemma off_nn (i): 0≤offBank G d i:= Finset.sum_nonneg fun _ _=>norm_nonneg _
lemma thistles:1≤thistle G d:= le_add_of_nonneg_right (Finset.sum_nonneg fun i _=>off_nn G d i)
lemma thorn (x:CColor G) (A:ℝ)(h:‖x‖≤ A) (ha:1≤A): ‖summitV G d x‖ ≤ thistle G d * A^d:= by
    have he:= thistles G d; apply (pi_norm_le_iff_of_nonneg (by positivity : 0≤thistle G d*A^d)).mpr; intro i; apply (norm_sum_le ..).trans
    apply le_trans _ (mul_le_mul_of_nonneg_right (show offBank G d i ≤ thistle G d from (Finset.single_le_sum (fun i _=>off_nn G d i) (Finset.mem_univ i)).trans (by unfold thistle;linarith)) (show 0≤A^d by positivity)); unfold offBank; rw [Finset.sum_mul]; refine Finset.sum_le_sum fun j hj=>?_
    apply ((patience G i j).le_opNorm _).trans; simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]; exact mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ (norm_nonneg _) h _).trans (pow_le_pow_right₀ ha (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))) (norm_nonneg _)

-- arbitrary walk and inverse carry; orientation already accounted on that path

def slopePath (G:Gauge)(x:Site n)(w:Walk)(M:Ambient G n):=
   colorProject G ((1/2:ℝ) • (stringMat M w x-stringMat M (Lattice.reverse w) (stop x w)))
def hype (G:Gauge)(t:ℕ)(x:Site n)(w:Walk) := summitV G t ∘ slopePath G x w
lemma hypeDiff (x:Site n)(w:Walk): ContDiff ℂ ω (hype G d x w) := by
   apply ContDiff.comp (summitCurve ..); unfold slopePath; exact (colorProject G).contDiff.comp (((stringMat_contDiff w x).sub (stringMat_contDiff ..)).const_smul _)
lemma hypeActual (x:Site n)(w:Walk)(U:Config G n) : hype G d x w (physical U)=colorUp G (theta G d (G.curvature (travel U x w))):= by
    unfold hype slopePath; dsimp only [Function.comp_apply]; rw [stringMat_physical,stringMat_physical,travel_reverse,colorProject_skew,summitReal]; rfl; simp only [star_smul,star_trivial,G.mat_inv,star_sub,star_star,← smul_neg, neg_sub]
-- norm qualifiers
private def bankOp {E F :Type}[NormedAddCommGroup E][NormedSpace ℂ E][NormedAddCommGroup F][NormedSpace ℂ F] (L:E→L[ℂ]F):ℝ:=‖L‖
def ticket (G:Gauge):=1+bankOp (colorProject G)*‖(1:G.Mat)‖
lemma ticket_ge :1≤ticket G:= le_add_of_nonneg_right (mul_nonneg (show 0≤ bankOp (colorProject G) from norm_nonneg _) (norm_nonneg _))
lemma cost_berry (U:Config G n)(w:Walk)(x:Site n){σ:ℝ}(hs:0<σ)(M:Ambient G n)(hm:M∈closedBall (physical U) (Work.F02.radius σ)):
    ‖slopePath G x w M‖≤ticket G*Real.exp (σ/2*w.length):=by
       let b:=Real.exp (σ/2*w.length); let C:= b*‖(1:G.Mat)‖
       let V:=stringMat M w x; let Y:=stringMat M (Lattice.reverse w) (stop x w)
       have ht:1+Work.F02.radius σ=Real.exp (σ/2):=by unfold Work.F02.radius; ring
       have hw (w':Walk)(he:w'.length=w.length) (x:Site n) :‖stringMat M w' x‖≤ C:= by
          apply (stringMat_bound U (radius_pos hs|>.le) M hm w' x).trans_eq; rw [he,ht,← Real.exp_nat_mul, mul_comm (w.length:ℝ)]
       unfold slopePath; have hP:= (colorProject G).le_opNorm ((1/2:ℝ) • (V-Y)); apply hP.trans; have hL:0 ≤bankOp (colorProject G):=norm_nonneg _; rw [norm_smul,Real.norm_of_nonneg (by norm_num : 0 ≤ (1/2:ℝ))]; refine le_trans (mul_le_mul_of_nonneg_left (show _ ≤ C from ?_) hL) ?_
       · linarith [norm_sub_le V Y,(show ‖V‖≤C from hw w rfl _),(show ‖Y‖≤ C from hw _ (by simp only [Lattice.reverse,List.length_map,List.length_reverse]) _)]
       unfold C ticket; let f:= bankOp (colorProject G); have hb :b>0:=Real.exp_pos _; change f*(b*‖(1:G.Mat)‖)≤(1+f*‖(1:G.Mat)‖)*b; nlinarith
variable {σ:ℝ} (h:0<σ)
def bire (p:ℕ)(σ:ℝ) := σ/(p+1)
def quote (G:Gauge)(p:ℕ) := thistle G p * ticket G^p
 include h
lemma bire_pos (p:ℕ):0<bire p σ:= div_pos h (by positivity)
 omit h in
lemma quote_pos (p:ℕ):0<quote G p:= by have hp:=ticket_ge G; have hh:=thistles G p; unfold quote; positivity
lemma cost_hype (p:ℕ)(U:Config G n)(w:Walk)(x:Site n)(M:Ambient G n)(hm: M∈closedBall (physical U) (Work.F02.radius (bire p σ))): ‖hype G p x w M‖ ≤ quote G p * Real.exp (σ*w.length):= by
    have hρ:=bire_pos h p
    let q:=bire p σ/2*w.length
    have hp:0≤q:= mul_nonneg (half_pos hρ|>.le) (by positivity)
    have hb:1≤ Real.exp q:=Real.one_le_exp hp
    have hx:=ticket_ge G
    refine (thorn G _ _ _ (cost_berry G U w x hρ M hm) (show 1≤ ticket G*Real.exp q from by nlinarith)).trans ?_
    rw [mul_pow,← Real.exp_nat_mul, ← mul_assoc]; apply mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) (quote_pos G p|>.le)
    unfold bire; field_simp; have hN:0≤(w.length:ℝ):=(by positivity); nlinarith
end YM.Qlocal.Quipu.Lasso
