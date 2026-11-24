import YM.GapsContact.Series.Get
/-!
# Lift calibrated all-order Euclidean data. Fixed compact on any patch with Coverage suffices

(no origin analytic-neighbourhood estimate in hypotheses). Euclidean norm matches the
*Euclidean* labels only; the same v must be used for W when applying this, along with the
price theorem actually obtained for that v. Thresholds/powers after finite index budgets
not necessarily uniform in perturbative truncation or in the real/tubular compacts. Use
with e.g. (𝓝[>]0)×ˢ(any parameter/phase filter) if strengthened Euclidean prices available.
No assertion here that e.g. the Wilson coefficients and any lifted version of the contact OPE
compare to all orders; more inputs/propagation have to be produced.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GapsContact.Pattern
open Function Set Filter Metric
open scoped Topology BigOperators ContDiff Classical
variable {ι Ω E:Type*} {g:Ω→ℝ} {A:ℕ→E→ℂ}{f:Filter Ω}

-- order q includes coeffs j<q (thus q=0 asserts boundedness)
def Rem (g:Ω→ℝ)(F:Ω→ E→ℂ)(A:ℕ→ E→ℂ)(q:ℕ)(i:Ω)(x:E):ℂ:= F i x - chart A (g i:ℂ) q x

def Expansion (f:Filter Ω)(g:Ω→ℝ)(F:Ω→E→ℂ)(A:ℕ→E→ℂ)(K:Set E) := ∀ q:ℕ,TagPrice f (Rem g F A q) K (fun i=> g i^q)

variable {F:Ω→ E→ℂ}{K U:Set E} (m:Meter f g)
include m
lemma Meter.low (k q:ℕ)(hk:k<q)(h:TagPrice f (Rem g F A q) K (fun i=> g i^q)) : TagPrice atTop (fun i x=> m.pull k F q i x-A k x) K (fun i=>wage i^(q-k)):=by
   let R:= Rem g F A q; have he:= TagPrice.several atTop (fun (v:Fin q) n x=> m.rate k q n v*R (recv m n v) x) Finset.univ (S:=K) (p:=fun i=>wage i^(q-k))
   apply TagPrice.congr (he ?_) ?_
   · intro j _; obtain ⟨C,hC,hT⟩:= m.fee k q j; obtain ⟨D,hD,hh⟩:= (own_levels m j).1
     have hy:TagPrice atTop (fun i x=> R (recv m i j) x) K (fun i=> wage i^q):=by
       refine (h.at (roll m j)).improve (pow_nonneg hD q) ?_
       filter_upwards [hh,(roll m j).eventually m.warm] with i hi hu; rw [← mul_pow]; exact pow_le_pow_left₀ hu.le hi q
     refine (hy.pays hC hT).up ?_; apply Eventually.of_forall; intro i; have hw:= wage_pos i; rw [inv_pow, ← div_eq_mul_inv]
     conv_lhs=> arg 1; rw [show q=q-k+k by omega,pow_add];
     field_simp; norm_num
   filter_upwards [m.right_coeff hk] with i hi x hx
   unfold Meter.pull; simp_rw [R, Rem,mul_sub,Finset.sum_sub_distrib]; rw [show (∑ j: Fin q,m.rate k q i j * chart A (g (recv m i j)) q x)= A k x from hi (fun a=> A a x)]
lemma Meter.left (e:Expansion f g F A K)(k:ℕ)(x:E)(hx:x∈K):∀ᶠ q in atTop,Tendsto (fun i=> m.pull k F q i x) atTop (𝓝 (A k x)):=by
   filter_upwards [eventually_gt_atTop k] with q hq
   have hp:= (m.low k q hq (e q)).tends (by simpa [zero_pow (show q-k≠0 by omega)] using wage_limit.pow (q-k)) x hx
   simpa using hp.add_const (A k x)
lemma Meter.knot (K U:ℕ→E→ℂ)(x:E)(h:Expansion f g F K {x})(he: Expansion f g F U {x})(q:ℕ):K q x= U q x :=by
   obtain ⟨i,hi,hj⟩:= ((m.left h q x rfl).and (m.left he q x rfl)).exists
   exact tendsto_nhds_unique hi hj

section Flow
variable {E:Type} [NormedAddCommGroup E][NormedSpace ℂ E][ProperSpace E]
variable {F:Ω→E→ℂ}{V:ℕ→ E→ℂ}{S T U K:Set E}

structure Binds (f: Filter Ω)(p:Ω→ℝ)(F:Ω→E→ℂ)(U:Set E):Prop where
   hol : ∀ᶠ i in f,AnalyticOnNhd ℂ (F i) U
   expense : ∀ K:Set E,IsCompact K→ K⊆U→∃ b:ℕ,TagPrice f F K (fun i=> (p i)⁻¹^b)

structure Charter (S U:Set E):Prop where
   openU : IsOpen U
   connected : IsPreconnected U
   pitch : S⊆ U
   dock : ∃ x:E,∃ d:ℝ,∃ R:Set E,IsCompact R∧R⊆U∧ 0<d ∧ closedBall x d⊆ U ∧ Covered S R (closedBall x d) -- coverage from S to complex ball
variable (C: Charter S U) (H: Binds f g F U)
omit [ProperSpace E] C m in -- m used statement
lemma holo (m:Meter f g) (H:Binds f g F U)(k q:ℕ): ∀ᶠ i:ℕ in atTop,AnalyticOnNhd ℂ (m.pull k F q i) U:=by
   filter_upwards [eventually_all.mpr (show ∀ (x:Fin q),∀ᶠ i in atTop, AnalyticOnNhd ℂ (F (recv m i x)) U from fun x=> (roll m x).eventually H.hol)] with i hi
   unfold Meter.pull
   exact Finset.analyticOnNhd_fun_sum _ (fun j hj=> analyticOnNhd_const.mul (hi j))
-- driver for propagation from patch
omit m in
lemma Charter.high {f:Filter Ω}{g:Ω→ℝ}{T:Filter ι}{A:ι→Ω→ E→ℂ}(C: Charter S U)(H:Support A T f g U)(h: Ready A T f g S) (K:Set E)(hK:IsCompact K) (hx:K⊆U):Ready A T f g K:=by
   obtain ⟨x,d,R,hR,hr,hd,hx',hV⟩:= C.dock
   exact H.body C.openU C.connected ⟨x,d,hd,hx',H.carries hR hr hV h⟩ hK hx
include H C
-- estimates for BOTH zoom increments and changing q, price of U⁻¹ depends on bK+k only (Binds price + kth coeff inverse)
lemma forms (k j:ℕ)(h:Expansion f g F V S) :
    let F':ℕ × ℕ→ℕ→E→ℂ:= fun q i x=> m.pull k F q.1 (i+j) x- m.pull k F q.2 i x
    ∀ K:Set E, IsCompact K → K⊆U→ Ready F' atTop atTop wage K:=by
   intro F'; apply C.high; swap
   · intro a
     have hk(q:ℕ)(hq:k+a+1≤q) : TagPrice atTop (fun i x=> m.pull k F q i x - V k x) S (fun i=> wage i^a):= (m.low k q (by omega) (h q)).up (Eventually.of_forall fun i=> pow_le_pow_of_le_one (wage_pos i).le (wage_short i) (by omega))
     filter_upwards [eventually_ge_atTop (k+a+1,k+a+1)] with q hq
     apply TagPrice.congr ( (( (hk q.1 hq.1).at (tendsto_add_atTop_nat j)).up ?_).sub (hk q.2 hq.2))
     swap
     · apply Eventually.of_forall; intro i; rw [wage_add]; apply pow_le_pow_left₀ (mul_nonneg (wage_pos i).le (wage_pos j).le) (mul_le_of_le_one_right (wage_pos i).le (wage_short j))
     exact Eventually.of_forall fun i x hx=> by dsimp only [F']; ring
   refine ⟨Eventually.of_forall fun q=> (((tendsto_add_atTop_nat j).eventually (holo m H k q.1)).and (holo m H k q.2)).mono fun i he x hx=> (he.1 x hx).sub (he.2 x hx), ?_, Eventually.of_forall wage_pos⟩
   intro K hK hx; obtain ⟨b,hB⟩:=H.expense K hK hx
   refine ⟨b+k, Eventually.of_forall (fun q=> ?_)⟩
   refine (TagPrice.improve ((m.high_nf k q.1 hB).at (tendsto_add_atTop_nat j)) (C:=(wage j)⁻¹^(b+k)) (by have hz:=wage_pos j; positivity) ?_).sub (m.high_nf k q.2 hB)
   apply Eventually.of_forall; intro i; rw [wage_add,mul_comm (wage i),mul_inv,mul_pow]

variable (S U) in -- might reset to implicits
lemma River.ofExpense (k:ℕ)(V:ℕ→E→ℂ)(h:Expansion f g F V S) : River (m.pull k F) U:=by
   refine ⟨Eventually.of_forall fun q=> holo m H k q, fun K hk hh=>?_, fun K hk hh=>?_⟩
   · have he:= forms m C H k 1 h K hk hh 1
     apply (tendsto_atTop_diagonal.eventually he).mono; intro i hi;
     simpa only [pow_one] using hi
   simpa only [Nat.add_zero,pow_one] using forms m C H k 0 h K hk hh 1

-- remainder beyond perturbative truncation after exact coefficients identified
omit C [ProperSpace E] in
lemma service_step (J:ℕ→E→ℂ)(h:∀ i,AnalyticOnNhd ℂ (J i) U) : Support (Rem g F J) atTop f g U:=by
   refine ⟨Eventually.of_forall fun q=> H.hol.mono fun i hF=>hF.sub (Finset.analyticOnNhd_fun_sum Finset.univ (s:=U) (f:=fun j:Fin q=> fun x=> (g i:ℂ)^(j:ℕ)*J j x) (fun j _=> analyticOnNhd_const.mul (h j))),?_, m.warm⟩
   intro K hK hx; obtain ⟨b,hh⟩:=H.expense K hK hx; refine ⟨b, Eventually.of_forall (fun q=>?_)⟩
   refine hh.sub (TagPrice.several f (fun j:Fin q=>fun i x=> (g i:ℂ)^(j:ℕ)*J j x) Finset.univ (fun j _=>?_))
   obtain ⟨C,hC⟩:= hK.bddAbove_image ((h _).continuousOn.norm.mono hx)
   refine ⟨|C|,abs_nonneg _,?_⟩; filter_upwards [m.short] with i ⟨hi,hw⟩ x hX
   rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hi.le]
   exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hi.le hw)).trans ((hC (mem_image_of_mem (fun x=> ‖J j x‖) hX)).trans ((le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) (one_le_pow₀ ((one_le_inv₀ hi).mpr hw)))))

lemma flows (J:ℕ→ E→ℂ)(ht:∀ i,AnalyticOnNhd ℂ (J i) U) (hp:Expansion f g F J S):∀ q:ℕ, Scoped f (Rem g F J q) U (fun i=> g i^q):=by
   intro q K hK hU
   have h: Ready (Rem g F J) atTop f g S:= by
      intro t; filter_upwards [eventually_ge_atTop t] with a ha; exact (hp a).up (m.short.mono fun i h=> pow_le_pow_of_le_one h.1.le h.2 ha)
   have hh:=C.high (service_step m H J ht) h K hK hU q
   obtain ⟨N,hN⟩:=eventually_atTop.mp hh; let p:=fun i=> g i^q
   -- truncate extended estimate back to desired power by paying the finite analytic coefficients
   have Y (k:ℕ) : TagPrice f (Rem g F J (q+k)) K p → TagPrice f (Rem g F J q) K p:=by
      induction k with
      | zero => exact id
      | succ k IH =>
        intro hk; apply IH
        obtain ⟨C,hC⟩:= hK.bddAbove_image (((ht (q+k)).continuousOn.mono hU).norm)
        rw [← Nat.add_assoc] at hk
        have ht: TagPrice f (fun i x=> (g i:ℂ)^(q+k)*J (q+k) x) K p:=by
            refine ⟨|C|, abs_nonneg _,?_⟩; filter_upwards [m.short] with i ⟨hi,hh⟩ x hx
            rw [norm_mul,norm_pow,Complex.norm_real, Real.norm_of_nonneg hi.le,mul_comm |C|]; exact mul_le_mul (pow_le_pow_of_le_one hi.le hh (Nat.le_add_right ..)) ((hC (mem_image_of_mem (fun x=> ‖J (q+k) x‖) hx)).trans (le_abs_self _)) (norm_nonneg _) (pow_nonneg hi.le _)
        apply (hk.add ht).congr; apply Eventually.of_forall; intro i x hx; unfold Rem; dsimp only; rw [chart_next]; ring
   exact Y N (hN (q+N) (by omega))
end Flow
section
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℂ E][FiniteDimensional ℂ E] [ProperSpace E] {S U:Set E}
variable {F:Ω→E→ℂ} {V:ℕ→E→ℂ}

structure Extension (f:Filter Ω)(F:Ω→E→ℂ)(g:Ω→ℝ)(V:ℕ→ E→ℂ)(U:Set E) : Prop where
    hol (k:ℕ):AnalyticOnNhd ℂ (V k) U
    jets (j q:ℕ): Scoped f (fun i=>iteratedFDeriv ℂ j (Rem g F V q i)) U (fun i=> g i^q)

omit m [FiniteDimensional ℂ E] [ProperSpace E] in
lemma Extension.power (h:Extension f F g V U) (K:Set E)(hk:IsCompact K)(hK:K⊆U): Expansion f g F V K:=fun q=> by
   simpa [TagPrice] using h.jets 0 q K hk hK

omit [FiniteDimensional ℂ E] [ProperSpace E] in
lemma Extension.uniq {J:ℕ→E→ℂ} (h:Extension f F g V U)(x:E)(hx:x∈U)(he:Expansion f g F J {x}) (q:ℕ):V q x= J q x:= Meter.knot m V J x (h.power _ isCompact_singleton (singleton_subset_iff.mpr hx)) he q -- unused finite?

lemma stretch (C: Charter S U)(H:Binds f g F U)(hp: Expansion f g F V S): ∃ J:ℕ→ E→ℂ,(∀ i,EqOn (V i) (J i) S) ∧ Extension f F g J U:=by
   choose J hJ ht using fun k=> (River.ofExpense m S U C H k V hp).gleam C.openU
   have hh (i:ℕ): EqOn (V i) (J i) S:=by
      intro x hx
      obtain ⟨n,hn,h'⟩:= ((m.left hp i x hx).and (ht i _ isCompact_singleton (singleton_subset_iff.mpr (C.pitch hx)))).exists
      exact tendsto_nhds_unique hn (h' x rfl)
   refine ⟨J, hh, hJ, fun j q=>?_⟩
   have he : Expansion f g F J S:=fun q=> (hp q).congr (Eventually.of_forall fun i x hx=> by
      unfold Rem chart; congr 1; exact Finset.sum_congr rfl fun k _=> congr_arg _ (hh k hx))
   exact (flows m C H J hJ he q).jet (m.warm.mono (fun _ hx=>pow_nonneg hx.le q)) C.openU
      (H.hol.mono fun i hF=> hF.sub (Finset.analyticOnNhd_fun_sum Finset.univ (s:=U) (f:=fun j:Fin q=> fun x=> (g i:ℂ)^(j:ℕ)*J j x) (fun j _=> analyticOnNhd_const.mul (hJ j)))) j
end
end YM.GapsContact.Pattern
