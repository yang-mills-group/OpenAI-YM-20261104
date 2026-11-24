import YM.AllOrder.Response.Algebra
import YM.Comparison.RG02.Order.VacLog
/-!
Canonical Fk component numerator identified through whole coupled grade.Then unmarked vacuum-log
agreement reduces to converting ordinary logS of positive-unit series in REAL convention to exact
Order.logVac. We don't infer via matching integration coefficients. Needs unit cp.V. Orders before
work forecasts, no analytic approximation. Uses same marker library.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Fk.Ballot
open Function Finset Filter MeasureTheory RG Precision Lattice
open Marker Multi Comparison.RG02 Comparison.RG02.Cumulants Comparison.RG02.Order Join
open AllOrder AllOrder.Laplace AllOrder.Laplace.SigmaP AllOrder.Response
open PositionX.Jet
open scoped Topology BigOperators Classical
variable {V : Type}[fv : Fintype V][DecidableEq V] (J : Census V)
section el
variable (d:ℕ) (F:ℕ→ℝ)
local notation "P"=> Poly J
-- Constant map PowerSeries.coeff.Pow.Lecture. Expand polynomial only finite d+1. Zero rank Mark criterion. use expS (logS numerator) proven via analytic-Word.Φ. denominator identifies.
def inc : ℝ →+* Poly J := (Poly.bead J).comp Complex.ofRealHom
def cast (F:ℕ→ℝ): PowerSeries (Poly J):= PowerSeries.map (inc J) (PowerSeries.mk F)
def pure (F:ℕ→ℝ): Grade J d:= series J d (cast J F)
omit fv in
lemma cast_at [Fintype V] (i:ℕ): PowerSeries.coeff i (cast J F)=Poly.send J.quiet (Complex.ofReal (F i)):= by rw [cast,PowerSeries.coeff_map,PowerSeries.coeff_mk]; rfl
lemma seen {n:ℕ}(he:n≤d): observe J d (pure J d F) n=Poly.bead J (Complex.ofReal (F n)):=by rw [pure,observation J d _ he]; exact cast_at J F n
omit [Fintype V] in
lemma inc_quiet (z:ℂ): (Poly.bead J z).part J.quiet=z:=by simp [Poly.bead]
lemma neutral (h:F 0=0): (pure J d F).part (Board J d).quiet=0:=by
   rw [pure,← Join.pair_quiet, ← (Symmetric.known (cast J F)).observe_part J.quiet (indices d).quiet]; -- order_id
   change (Nat.factorial 0:ℂ)*(observe _ _ (pure J d F) 0).part _=_; rw [seen J d F (Nat.zero_le _), inc_quiet,h]; simp
private lemma fully {x y:Grade J d}(h:Symmetric x)(hs:Symmetric y)(hb:∀ i≤d,observe J d x i=observe J d y i):x=y:=by
   obtain ⟨p,rfl⟩:=h; obtain ⟨q,rfl⟩:=hs; refine (Order.trunc_complete J d p q).2 ?_; ext1 i; rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc]; split
   next h' => exact (observation J d p (Nat.le_of_lt_succ h')).symm.trans ((hb i (Nat.le_of_lt_succ h')).trans (observation J d q (Nat.le_of_lt_succ h')))
   rfl
lemma mono_mark (x : Grade J d) (hs:Symmetric x) (he : ∀ i≤d, (observe J d x i).part J.quiet=↑(F i)): denominator x=pure J d F:= by
   refine fully J d hs.vacant (Symmetric.known _) ?_; intro i hi; unfold denominator; rw [seen J d F hi,observe_bottom]
   change Poly.bead J _=_; exact congr_arg (Poly.bead J) (he _ hi)
lemma write_pass (h:F 0=0) : Poly.pass (pure J d F)=pure J d (expS F):=by
   let A:= Fintype.card (V ⊕ Fin d); have ht :d≤ A:=by simp [A];
   let u : PowerSeries P := ∑ i∈range (A+1),((i.factorial:ℂ)⁻¹) • ((cast J F)^i)
   have he : series J d u= Poly.pass (pure J d F):=by unfold u Poly.pass pure; rw [map_sum]; apply sum_congr rfl fun i _=>?_ ; rw [series_smul, map_pow]
   rw [← he, pure, trunc_complete]; ext1 n; rw [PowerSeries.coeff_trunc,PowerSeries.coeff_trunc]; split
   next h' =>
      rw [cast_at, exp_pay (show light F from h) ((Nat.le_of_lt_succ h').trans ht)]
      unfold u onward; rw [map_sum,Finset.sum_apply]; simp_rw [cast, ← map_pow,PowerSeries.coeff_smul,PowerSeries.coeff_map]
      change ∑ x∈range (A+1), (x.factorial:ℂ)⁻¹ • Poly.bead J ↑(xpow F x n)=Poly.bead J (Complex.ofReal (∑ x∈_,((x.factorial:ℝ)⁻¹)*xpow F x n)); rw [Complex.ofReal_sum,map_sum]; apply sum_congr rfl fun b _=> ?_; rw [Complex.ofReal_mul, Complex.ofReal_inv,map_mul, ← Poly.product_bead]; push_cast; rfl
   rfl
lemma shift (h:F 0=1): logS F 0=0:=by rw [logS,run_zero,h,Real.log_one]
lemma expense (h:0<F 0): expS (logS F)=F:=by
   funext i; have he:= Act.swell F (show i≤ i from le_rfl); have ht:0< (delay F i) 0:= h.trans_eq he.zero.symm
   refine (Act.realizes ?_ ((he.transit (Real.contDiffAt_log.mpr h.ne')).transit (m:=Real.exp) Real.contDiff_exp.contDiffAt)).trans_at he le_rfl
   exact (he.nice.continuousAt.eventually (lt_mem_nhds ht)).mono fun x hx=> Real.exp_log (show _ from hx)
-- no include v
lemma log_mono (x:Grade J d) (h:F 0=1)(hs:Symmetric x)(he : ∀ i≤d, (observe J d x i).part J.quiet=↑(F i)) : logVac x=pure J d (logS F):= by
    unfold logVac; have hv:= neutral J d (logS F) (shift F h); have ht:= Cumulants.connected_pass hv; rw [write_pass _ _ _ (shift F h),expense F (by rw [h]; exact zero_lt_one)] at ht; rw [mono_mark J d F x hs he]; exact ht
end el
end YM.QuadraticLocal.Fk.Ballot
