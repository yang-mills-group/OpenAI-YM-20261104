import YM.FormalBulk08.Broc.Ends

/-!
Stationary cross-check library. This is just low-degree identification,
independent of iterative mask operations. Homogeneity including Hessian & Haar.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Plait
open Wick Series Orb Jets Lava Gorge Mesa Cork Broc PowerSeries Function Filter
open scoped BigOperators Topology Classical ContDiff
variable {T V : Type*} [Fintype V]
omit [Fintype V] in lemma vacuum_seal {R : Type*}[CommRing R] (p:MvPolynomial V R): MvPolynomial.constantCoeff p=MvPolynomial.aeval (R:=R) (0:V→R) p:= by
   induction p using MvPolynomial.induction_on with
   | C c=>simp
   | add p q hp hq=> rw [map_add,map_add,hp,hq]
   | mul_X p i hp=> simp
omit [Fintype V] in lemma pin_drop (m : V →₀ ℕ)(h:m≠0):∃ i n, m=n+Finsupp.single i 1:= by
   obtain ⟨i,hi⟩ := Function.ne_iff.mp (show ⇑m ≠ (0 : V → ℕ) from fun he=> h (DFunLike.ext _ _ (congr_fun he))); refine ⟨i,m-Finsupp.single i 1,?_⟩; symm; apply tsub_add_cancel_of_le; intro j; by_cases hv:j=i
   · subst j; rw [Finsupp.single_eq_same]; exact Nat.pos_of_ne_zero hi
   simp [hv]
omit [Fintype V] in lemma pin_check {R:Type*}[CommRing R][IsDomain R][CharZero R](p q: MvPolynomial V R)(h:∀ i:V,MvPolynomial.pderiv i p=MvPolynomial.pderiv i q)(hp:MvPolynomial.constantCoeff p=MvPolynomial.constantCoeff q): p=q:= by
    ext1 d; by_cases hz:d=0
    · subst d;exact hp
    obtain ⟨i,n,rfl⟩:=pin_drop d hz;have ht:=congr_arg (MvPolynomial.coeff n) (h i); rw [MvPolynomial.coeff_pderiv,MvPolynomial.coeff_pderiv,← Nat.cast_add_one] at ht; exact mul_right_cancel₀ (by exact_mod_cast (by omega : n i+1≠0)) ht
lemma pin_gauge {V:Type*}[Fintype V](f:Jets.Rays V→ℝ): PowerSeries.map MvPolynomial.constantCoeff (paste f)=C (f 0):= by
   ext1 i;rw [coeff_map,vacuum_seal]; cases i with
   | zero=> rw [paste_first];simp
   | succ i=>change traceP (0:Jets.Rays V) _=_; rw [trace_paste]; simp [PertExtension.Series.Radial.jet]; exact Or.inr (ContinuousMultilinearMap.map_coord_zero _ (0 : Fin (i+1)) rfl)

-- normalization `g` comparison
lemma pin_spark (f:Jets.Rays V→ℝ) (h:ContDiffAt ℝ ∞ f 0)(hp:f 0=0): paste (Real.exp ∘ f)=expan (paste f):= by
    let E:=Real.exp ∘ f; have he:coeff 0 (paste f)=0:=by rw [paste_first,hp,map_zero]
    have hh:PowerSeries.map MvPolynomial.constantCoeff (paste E)=PowerSeries.map MvPolynomial.constantCoeff (expan (paste f)) := by rw [pin_gauge,map_expan _ he,pin_gauge,hp,map_zero,root_expan]; simp [E,hp];
    let g i (x:Jets.Rays V):= fderiv ℝ f x (dotI i); have hx i : (fun x=> fderiv ℝ E x (dotI i))=ᶠ[𝓝 0] E * g i:= by
        filter_upwards [((h.of_le (show (1: WithTop ℕ∞) ≤∞ by norm_num)).eventually (by simp))] with x hx; unfold E Function.comp; rw [fderiv_exp (hx.differentiableAt (by norm_num))];rfl
    have ht i: ContDiffAt ℝ ∞ (g i) 0:= ContDiffAt.clm_apply (f:=fderiv ℝ f) (g:=fun _=>dotI i) (h.fderiv_right (by norm_num)) contDiffAt_const
    have hW i: shaft (MvPolynomial.pderiv i) (paste E)=X*(paste E * paste (g i)) := by rw [gradient E i h.exp, paste_replace (hx i), paste_mul E (g i) h.exp (ht i)]
    have hP i: shaft (MvPolynomial.pderiv i) (expan (paste f))= X*(expan (paste f)*paste (g i)):= by rw [shaft_expan_over _ _ he,gradient _ _ h,mul_left_comm]
    ext1 m; change coeff m (paste E)=_; induction m using Nat.strong_induction_on with
    | h m ih=>
        refine pin_check _ _ (fun i=>?_) ?_
        · rw [←coeff_shaft,←coeff_shaft,hW i,hP i];cases m with
          | zero =>rw [coeff_zero_X_mul,coeff_zero_X_mul]
          | succ m=> rw [coeff_succ_X_mul,coeff_succ_X_mul]; exact ((Through.mul (show Through m (paste E) _ from fun i hi=>ih i (by omega)) (Through.exact_eq _ m)).apex)
        simpa only [coeff_map] using! (congr_arg (coeff m) hh)
lemma pin_rung (f:Jets.Rays V→ℝ)(hp : f 0=1)(h:ContDiffAt ℝ ∞ f 0): paste (Real.log ∘ f)=covelog (paste f) := by
   let W:= Real.log ∘ f; have hx: W 0=0:= by simp [W,hp]
   have hh: ∀ᶠ x in 𝓝 (0:Jets.Rays V),0<f x:= h.continuousAt.eventually (lt_mem_nhds (hp.symm ▸ zero_lt_one))
   have hz : paste f = expan (paste W):= (paste_replace (f:=f) (g:=Real.exp ∘ W) (hh.mono (fun i h=> (Real.exp_log h).symm))).trans (pin_spark W (h.log (hp.symm ▸ one_ne_zero)) hx)
   rw [hz, covelog_after (by rw [paste_first,hx,map_zero])]
end YM.FormalBulk08.Plait
