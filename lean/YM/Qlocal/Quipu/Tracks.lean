import YM.Qlocal.Quipu.Merit
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Quipu.Eluder
open AllOrder AllOrder.Ink Floe
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace Laplace.SigmaP Ker Ker.Start
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response Ink Ink.Method Ink.Money GaussianScore Module
open Tree Wilson PhysicalNext Repeat Lapis ConnectedActivityE6 Blaze Precision Push Pressure Next.Fluctuations Next.SectorChange MeasureTheory
open Kinetic.Port
open Bloch hiding direct
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
open Turbin Sonnet Marker Kinetic Primitives.GCC.Anchor
open Ballad Dais Zora Lasso AnalyticNext.QuarticMatch Joint CubicMatch
open Album Exterior
namespace Incline
namespace Tracks
-- arbitrary Euclidean/normed finite dimensions; Inventory necessary to buy composition charges.
variable {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X]{a b v E:ℝ} {m n k N:ℕ}{f:X→ℝ}
lemma taut (x:X)(h:Prices k a f):Prices (k-1) (‖x‖* (a*honor k)) (diff' x f):=by
 by_cases he:x=0; · rw [he,norm_zero,zero_mul,show diff' (0:X) f=0 from funext fun i=>map_zero _]; exact price_const (abs_zero.le) _
 let V:= ‖x‖; have hv:0<V:=norm_pos_iff.mpr he; let u:= V⁻¹ • x; have hc:‖u‖≤1:=by unfold u; rw [norm_smul, Real.norm_of_nonneg (inv_pos.mpr hv).le, show ‖x‖= _ from (rfl:‖x‖=V),inv_mul_cancel₀ hv.ne'] -- hv cast motive
 rw [show diff' x f= V • diff' u f from ?_]; swap; · ext z; change fderiv ℝ f z x=V • _; rw (occs:=.pos [1]) [show x=V • u from (smul_inv_smul₀ hv.ne' x).symm]; exact map_smul (fderiv ℝ f z) ..
 have hh:= price_scale (h.taper u hc) V; rw [abs_of_pos hv] at hh; exact hh
def scaleH (n k:ℕ):ℝ:= match n with
 | 0=>1
 | n+1 => honor k * scaleH n (k-1)
def boundH (n k:ℕ):= ∑ i∈ range (n+1),scaleH i k
lemma s_ge (n k:ℕ):0< scaleH n k:= by induction n generalizing k with| zero=>exact zero_lt_one| succ n ih=> exact mul_pos (honor_pos k) (ih _)
lemma enough (hx:k≤N): scaleH k n≤ boundH N n:= Finset.single_le_sum (f:=fun i=>scaleH i n) (fun i _=>(s_ge ..).le) (mem_range.mpr (by omega))
lemma b_ge (n k:ℕ):0 < boundH n k := (s_ge _ _).trans_le (enough (Nat.zero_le _))
private lemma plus_budget (x:X)(h:Prices k a f): ‖iteratedFDeriv ℝ n f x‖ ≤ scaleH n k*a*(1+‖x‖)^k:=by
 induction n generalizing k a f with
 | zero=>rw [norm_iteratedFDeriv_zero,scaleH,one_mul]; exact h.2.2 x
 | succ n ih=>
    have hx:=h.1; let q:=roi x; let S:=scaleH n (k-1); let v0:=scaleH (n+1) k * a * q^k; have hh:=s_ge (n+1) k; refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) (fun v=>?_)
    rw (occs:=.pos [1]) [← Fin.cons_self_tail v]; rw [Analysis.cons_inner ((h.2.1.read.smooth.contDiffAt).of_le le_top)]; let V:=Fin.tail v; rw [Fin.prod_univ_succ]; change ‖iteratedFDeriv ℝ n (diff' (v 0) f) x V‖ ≤ v0*(‖v 0‖ * ∏ i,‖V i‖); rw [←mul_assoc]; apply le_trans (ContinuousMultilinearMap.le_opNorm ..) (mul_le_mul_of_nonneg_right _ (by positivity)); refine (ih (taut (v 0) h)).trans ?_; change S*(‖v 0‖*(a*honor k))*q^(k-1)≤ honor k*S*a*q^k*‖v 0‖
    rw [mul_right_comm (honor k*S*a),show honor k*S*a*‖v 0‖=S*(‖v 0‖*(a*honor k)) from (by ring)]; exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by simp [q,roi]) (by omega)) (by have he:=honor_pos k; have hp:0<S:=s_ge ..; positivity)
variable (x:X)(hf:Prices k a f)
include hf
lemma ripe(n:ℕ): Allows n f x (boundH n k*a*roi x^k):= by
 refine ⟨hf.2.1.read.smooth.contDiffAt,fun i hi=>?_⟩; refine (plus_budget x hf).trans ?_; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (enough hi) hf.1) (show 0≤ (1+ ‖x‖)^k from by positivity)
lemma aloud {Y:ℝ→X}(he:Allows n Y 0 v): Allows n (f∘Y) 0 (composeCost n (boundH n k*a*(1+v)^k) v):= by
 have h0:=ripe (Y 0) hf n; exact (h0.mono (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (show 0 ≤1+‖Y 0‖ from by positivity) (add_le_add_right he.value _) _) (mul_nonneg (b_ge ..).le hf.1))).comp he
omit hf in
lemma per_jet {Y:ℝ→X} (h:Allows k Y 0 v)(hx:n≤k): ‖someJ Y n‖ ≤ v:= by
 have ht:=h.norm_le n hx; rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at ht; unfold someJ; rw [norm_smul,Real.norm_of_nonneg (by positivity)]; exact le_trans (mul_le_of_le_one_left (norm_nonneg _) (by apply (inv_le_one₀ (show 0<(↑n.factorial:ℝ) by positivity)).mpr; exact_mod_cast (Nat.factorial_pos n))) ht
-- Amp ℝ meta scales up/Π.
def pawnout (j n:ℕ)(w:ℝ):= composeCost j (boundH j n*(1+w)^n) w
variable {Y:ℝ→X}(h:Allows n Y 0 v)
include h
lemma verity(hx:m≤n): ‖someJ (f ∘ Y) m‖ ≤ a*pawnout n k v:= by
 apply le_trans (per_jet (aloud hf h) hx); unfold pawnout composeCost; apply le_of_eq; ring
omit h hf
variable {ζ:Type}(z:ζ→ℝ){V:ζ→ Side→ ℝ}
lemma quote (n k:ℕ)(hp:Weight z m V) : Weight z (m*k + m*n) (fun i r=> pawnout n k (V i r)):= by
 let Y i r:=1+V i r; have hv:Weight z m Y:= ((Weight.fixed z 1 zero_le_one).ups (Nat.zero_le _)).stamp hp; simpa only [Nat.zero_add] using! (((Weight.fixed z (n.factorial:ℝ) (by positivity)).times ((Weight.fixed z (boundH n k) (b_ge n k).le).times (hv.raise k))).times (hv.raise n))
lemma pawned (hp:0≤v): 0≤pawnout n k v:= by unfold pawnout composeCost; have ht:=b_ge n k; positivity
-- Polynomial interpolation from sampled mask estimates
abbrev foster (k:ℕ):= ((k+1:ℕ):ℝ)*(k+1:ℕ)^k*(analytic_cost k).choose
theorem foster_ge (k:ℕ):0< foster k:= by unfold foster; have he:=(analytic_cost k).choose_spec.1; positivity
theorem embark (h : Rank X k f)(he:∀ x, ‖x‖ ≤ 1 → |f x| ≤ E): Prices k (foster k*E) f:=by
 let F:=(analytic_cost k).choose; let M:=((k+1:ℕ):ℝ); have ht:1≤M:=(by unfold M; exact_mod_cast (Nat.le_add_left 1 k)); have ht':0<M:=zero_lt_one.trans_le ht; have he': 0≤E:= (abs_nonneg (f 0)).trans (he 0 (by simp))
 refine ⟨mul_nonneg (foster_ge k).le he',h,fun x=>?_⟩; let r:=roi x; have hr:1≤r:= by simp [r,roi]
 let R:=M*r; have hR:1≤R:= (one_le_mul_of_one_le_of_one_le ht hr); have hh:0<R:=zero_lt_one.trans_le hR; have hm:= (analytic_cost k).choose_spec
 let A:= ContinuousLinearMap.toSpanSingleton ℝ (R⁻¹ • x); let f':=f ∘ A; have hj: Rank ℝ k f':= h.lead A; have hc (i:ℕ)(hi:i∈range (k+1)): ‖someJ f' i‖ ≤ F*E:= by
    refine hm.2 f' hj E ?_ ⟨i, mem_range.mp hi⟩; intro j; let u:= (j.val:ℝ); have hu: u ≤ M:= (Nat.cast_le.mpr j.isLt.le); refine he _ ?_; change ‖u • (R⁻¹ • x)‖ ≤ _; rw [norm_smul,norm_smul,Real.norm_of_nonneg (show 0 ≤ u from Nat.cast_nonneg _),Real.norm_of_nonneg (inv_pos.mpr hh).le]; calc
       _ ≤ M*(R⁻¹*r) := by apply mul_le_mul hu (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (inv_pos.mpr hh).le); exact mul_nonneg (inv_pos.mpr hh).le (norm_nonneg _); exact ht'.le
       _ = _ := by have he:0<r:=zero_lt_one.trans_le hr; unfold R; field_simp
 rw [show f x=f' R from (show f x=f (R•R⁻¹ • x) from congr_arg _ (smul_inv_smul₀ hh.ne' x).symm),← Real.norm_eq_abs, congr_fun (rank_taylor hj).2]; unfold PositionX.Jet.delay; refine (norm_sum_le ..).trans ((Finset.sum_le_sum (g:=fun i=> R^k * (F*E)) (s:=range (k+1)) ?_).trans_eq ?_)
 · intro j hj; rw [norm_smul,Real.norm_of_nonneg (pow_nonneg hh.le _)]; exact mul_le_mul (pow_le_pow_right₀ hR (Nat.le_of_lt_succ (mem_range.mp hj))) (hc j hj) (norm_nonneg _) (pow_pos hh k).le
 rw [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; change M*(R^k*(F*E))=(foster k*E)*r^k; unfold foster; change M*(R^k*(F*E))=(M*M^k*F*E)*r^k; unfold R; rw [mul_pow]; ring
end Tracks
end Incline
end YM.Qlocal.Quipu.Eluder
