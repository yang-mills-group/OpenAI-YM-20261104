import YM.GapsContact.Series.Full
import YM.TraceExtension.Fock.VacuumLocal
import YM.Work.C14

/-!
# Patch norm on real profiles → the point-kernel input for extrapolation

`Chime` uses fixed C^M norm of independent profiles (translated as needed in the
coordinates of this statement -- costs here in pure Euclidean beam/position units, no
rates in imaginary coordinates or coupling derivatives). 'Independent' means the arbitrary
*joint* profiles, not tensor-factor tests. Constant and C^M order may be chosen per compact;
constants may depend on perturbative order but number of derivatives CANNOT. `Banks` is the
separate formal input that the Euclidean kernels have at least one continuous derivative;
not a real-kernel matching or limiting assertion. No growth at coincidence required by this
smrel consumer (different for contact matching!).
-/
set_option autoImplicit false
noncomputable section
namespace YM.GapsContact.Pattern
open Function Filter Set Metric Boundary Probe TraceExtension TraceExtension.Photons
open MeasureTheory
open scoped BigOperators Topology ContDiff Classical InnerProductSpace

variable {F:Type}[NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

def chiNorm (n:ℕ) (φ:Probe F):= ∑ i ∈ Finset.range (n+1), Probe.size 0 i φ
omit [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] in
lemma chime_non (n:ℕ)(φ:Probe F):0≤ chiNorm n φ:=by unfold chiNorm size; positivity

section adjustment
variable (y:F)
def blossom (ε:ℝ): Probe F := ahead y (condense ε⁻¹ (petal F))
lemma cut_radius {ε:ℝ}(he:0<ε): tsupport ⇑(blossom y ε)⊆closedBall y (2*ε):=by
   apply closure_minimal _ isClosed_closedBall
   intro x hx; have hu: ε⁻¹ • (x-y)∈tsupport (petal F):= subset_tsupport _ (fun h=> hx (by unfold blossom; rw [ahead_at,condense_eval _ (by positivity),h,smul_zero]))
   have hp:= tsupport_comp_subset Complex.ofReal_zero _ hu; change ε⁻¹ • (x-y)∈ tsupport ((bump F).normed volume) at hp
   rw[ContDiffBump.tsupport_normed_eq, mem_closedBall,dist_zero_right,norm_smul,Real.norm_of_nonneg (by positivity), ← div_eq_inv_mul] at hp; change dist x y ≤ _; rw [dist_eq_norm]; exact (div_le_iff₀ he).mp hp
lemma mass_one {ε:ℝ}(he:0<ε): (∫ x, blossom y ε x)=1:=by
   unfold blossom; simp_rw [ahead_at, condense_eval _ (inv_pos.mpr he), integral_smul]
   let s (x:F):=(petal F) (ε⁻¹ • x)
   have hx:(∫ x,s (x-y))=∫ x,s x:= integral_sub_right_eq_self ..
   rw [show _ • _ = _ from congr_arg ((ε⁻¹^Module.finrank ℝ F) • ·) hx]; unfold s
   rw [Measure.integral_comp_smul_of_nonneg volume (petal F) _ (hR:=by positivity), smul_smul,mul_inv_cancel₀ (by positivity),one_smul]
   change (∫ x,Complex.ofReal ((bump F).normed volume x))=1; rw [integral_complex_ofReal,ContDiffBump.integral_normed]; rfl
lemma mass_abs {ε:ℝ}(he:0<ε): (∫ x, ‖blossom y ε x‖)=1:=by
   have hp(x): ∀ g:ContDiffBump (0:F), ‖(g.normed volume x : ℂ)‖=(↑(g.normed volume x):ℂ).re:=fun g=> by rw [Complex.norm_real,Real.norm_of_nonneg (g.nonneg_normed ..)]; rfl
   have hx(x): ‖blossom y ε x‖=(blossom y ε x).re:=by
      unfold blossom; rw [ahead_at,condense_eval _ (by positivity), norm_smul,Real.norm_of_nonneg (by positivity)]; change _* ‖(Complex.ofReal ((bump F).normed _ _))‖= _; rw [hp]; simp only [Complex.smul_re]; rfl
   simp_rw [hx]; change (∫ x,RCLike.re (blossom y ε x))=1; rw [integral_re (blossom y ε).integrable, mass_one y he]; rfl
lemma cry (i:ℕ) {ε:ℝ}(he:0<ε):Probe.size 0 i (blossom y ε) ≤ ε⁻¹^(Module.finrank ℝ F+i)*Probe.size 0 i (petal F):=by
   apply SchwartzMap.seminorm_le_bound ℂ _ _ _ (by unfold size; positivity); intro x
   let r:= ε⁻¹; let p:=(petal F); let g(x:F):= p (r • x); have hh : ContDiff ℝ i g:= (p.smooth i).comp (show ContDiff ℝ i (fun x:F=> r • x) from by fun_prop)
   unfold blossom; rw [pow_zero,one_mul,Work.C14.deriv_ahead,show ((condense ε⁻¹ p):F→ℂ)=(fun x=> (ε⁻¹^Module.finrank ℝ F) • g x) from funext (condense_eval _ (inv_pos.mpr he) p), iteratedFDeriv_const_smul_apply' hh.contDiffAt]
   unfold g r; rw [iteratedFDeriv_comp_const_smul _ (p.smooth _), norm_smul, norm_smul,Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg (by positivity),pow_add,mul_assoc]; gcongr; exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ p i _
lemma choir (k:ℕ) {ε:ℝ}(he:ε∈ Ioc (0:ℝ) 1): chiNorm k (blossom y ε) ≤ (ε⁻¹^(Module.finrank ℝ F+k))*chiNorm k (petal F):=by
   unfold chiNorm; rw [Finset.mul_sum]; refine Finset.sum_le_sum fun i hi=> (cry y i he.1).trans ?_
   apply mul_le_mul_of_nonneg_right _ (apply_nonneg ..); apply pow_le_pow_right₀ ((one_le_inv₀ he.1).mpr he.2); exact Nat.add_le_add_left (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) _
end adjustment

variable {Ω:Type*}{f: Filter Ω}{g:Ω→ℝ} (m:Meter f g) {S K:Set F}{V:ℕ→F→ℂ}{A:Ω→ F→ℂ}
local notation "⌞" h "⌟" => fderiv ℝ h

structure Chime (f:Filter Ω)(g:Ω→ℝ)(A:Ω→ F→ℂ)(V:ℕ→F→ ℂ)(K:Set F)(d:ℕ) : Prop where
    through (q:ℕ): ∃ C:ℝ,0≤C∧∀ᶠ i in f, ∀ φ: Probe F, tsupport φ ⊆ K →
       Integrable (fun x=>Rem g A V q i x * φ x) ∧ ‖∫ x, Rem g A V q i x * φ x‖ ≤ C*g i ^ q * chiNorm d φ

def Banks (V:ℕ→F→ℂ)(S:Set F):=∀ i x,x∈S → ContDiffAt ℝ 1 (V i) x

-- Lipschitz estimate at fixed perturbative order on PU coords; add analytically to pay every likely remainder.
omit [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] in
lemma noisy_price (m:Meter f g) {b:ℕ} (hv:IsCompact K)(hc:Convex ℝ K)(h:TagPrice f (fun i=> fderiv ℝ (A i)) K (fun i=> (g i)⁻¹^b)) (hx:∀ᶠ i in f,∀ x∈K, DifferentiableAt ℝ (A i) x) (hg:Banks V K)(q:ℕ): ∃ D:ℝ,0≤ D ∧ ∀ᶠ i in f,∀ x∈K,∀ y∈ K,
    ‖Rem g A V q i x - Rem g A V q i y‖ ≤ D * (g i)⁻¹^b * ‖x-y‖:=by
   induction q with
   | zero =>
    obtain ⟨C,hC,h⟩:=h; refine ⟨C,hC,(hx.and h).mono fun i hi x hx y hy=>?_⟩
    simpa only [Rem,chart,Finset.univ_eq_empty,Finset.sum_empty,sub_zero] using hc.norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℝ) (fun x=> hi.1 x) (fun x=> hi.2 x) hy hx
   | succ q IH=>
    obtain ⟨D,hD,hh⟩:=IH; obtain ⟨C,hC⟩:= hv.bddAbove_image (show ContinuousOn (fun x=> ‖fderiv ℝ (V q) x‖) K from fun x hx=> (ContinuousAt.norm ((hg q x hx).continuousAt_fderiv (by simp))).continuousWithinAt)
    refine ⟨D+|C|,by positivity, ?_⟩; filter_upwards [hh,m.short] with i hi ⟨ht,hr⟩ x hx y hy
    rw [show Rem g A V (q+1) i x- Rem g A V (q+1) i y=Rem g A V q i x - Rem g A V q i y - (g i:ℂ)^q * (V q x-V q y) by unfold Rem; rw [chart_next,chart_next]; ring]
    refine (norm_sub_le ..).trans ?_; rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg ht.le,add_mul,add_mul]; apply add_le_add (hi _ hx _ hy)
    apply (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ ht.le hr)).trans; apply hc.norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℝ) _ _ hy hx
    · exact fun x hx=> (hg q x hx).differentiableAt (by simp)
    exact fun x hx=> (hC (mem_image_of_mem _ hx)).trans ((le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) (one_le_pow₀ ((one_le_inv₀ ht).mpr hr))))

lemma chi_value (A:F→ℂ)(U:Probe F)(b y:ℝ) (x:F)(S:Set F) (hy:tsupport U⊆ S)(hz:(∫ z,U z)=1)(hp:(∫ z,‖U z‖)=1)(_hc:0≤b)(hi:Integrable (fun x=>A x*U x)) (he:∀ w∈S, ‖A x - A w‖ ≤ b) (ht: ‖∫ z,A z*U z‖≤ y): ‖A x‖ ≤ y+b:=by
    rw [add_comm]; have hx:A x= (∫ z,(A x - A z)*U z) + (∫ z,A z* U z) :=by simp_rw [sub_mul]; rw [integral_sub ((U.integrable).const_mul _) hi, sub_add_cancel, integral_const_mul,hz]; simp
    refine (le_of_eq (congr_arg norm hx)).trans (norm_add_le_of_le ?_ ht)
    apply (norm_integral_le_of_norm_le (μ:=volume) (U.integrable.norm.const_mul b) ?_).trans_eq (by rw [integral_const_mul,hp,mul_one]); refine ae_of_all _ fun p=> ?_
    by_cases H:U p=0; · simp [H]
    rw [norm_mul]; exact mul_le_mul_of_nonneg_right (he p (hy (subset_tsupport _ H))) (norm_nonneg _)

lemma upgrade_ball (m:Meter f g) {x:F}{n j b d:ℕ}{r:ℝ}(hr:0<r)(H:Chime f g A V (closedBall x (2*r)) d) (ht:Banks V (closedBall x (2*r)))
      (h:TagPrice f (fun i=> fderiv ℝ (A i)) (closedBall x (2*r)) (fun i=> (g i)⁻¹^b))
      (hx:∀ᶠ i in f,∀ y∈ closedBall x (2*r), DifferentiableAt ℝ (A i) y)(hj:n+(b+n+1)*(Module.finrank ℝ F+d) ≤ j) : TagPrice f (Rem g A V j) (closedBall x r) (fun i=> g i^n):=by
   let N:=Module.finrank ℝ F+d; let K:=closedBall x (2*r)
   let T:= n+b+1
   let t(i):= g i^T; have hT:Tendsto t f (𝓝 0):=by simpa [T] using m.little.pow T
   obtain ⟨C,hC,hK⟩:= noisy_price m (isCompact_closedBall ..) (convex_closedBall ..) h hx ht j
   obtain ⟨D,hD,hV⟩:= H.through j
   let R:=chiNorm d (petal F); have hR:0≤R:= chime_non ..
   refine ⟨D*R+2*C,by positivity,?_⟩
   filter_upwards [m.short,hT.eventually_le_const (half_pos hr),hK,hV] with i ⟨hp,hq⟩ hu hs he y hy
   let φ:= blossom y (t i); have hy' : t i∈ Ioc (0:ℝ) 1 := ⟨pow_pos hp _,pow_le_one₀ hp.le hq⟩
   let V':= closedBall y (2*t i); have hb: tsupport ⇑φ⊆ V':= cut_radius y hy'.1; have ha:V'⊆closedBall x (2*r):= fun z hz=> (dist_triangle z y x).trans (by linarith only [hu,mem_closedBall.mp hy,mem_closedBall.mp hz])
   obtain ⟨hg,hh⟩:= he φ (hb.trans ha)
   rw [add_mul]; apply chi_value _ φ _ _ _ V' hb (mass_one y hy'.1) (mass_abs y hy'.1) (by positivity) hg
   · intro z hz; let a:= g i; have ha₁ : g i ^ T = g i ^ b * g i ^(n+1):=by rw[← pow_add]; congr 1; omega -- unfold
     apply le_trans (hs y (closedBall_subset_closedBall (by linarith : r ≤2*r) hy) z (ha hz));
     refine le_trans (mul_le_mul_of_nonneg_left ?_ (by positivity) : _ ≤ (C*(g i)⁻¹^b)*(2*(g i)^T)) ?_
     · simpa only [← dist_eq_norm,norm_sub_rev,dist_comm y] using mem_closedBall.mp hz
     rw [ha₁,inv_pow]; have hf:g i^(n+1)≤g i^n:=pow_le_pow_of_le_one hp.le hq (by omega)
     field_simp; nlinarith -- might issues
   refine hh.trans ?_; let a:=g i; have hg:g i^j≤g i^(n+T*N):= pow_le_pow_of_le_one hp.le hq (by unfold T N; simpa [add_comm n b] using hj)
   apply (mul_le_mul (mul_le_mul_of_nonneg_left hg hD) (choir y _ hy') (chime_non ..) (by positivity)).trans_eq
   change D*g i^(n+T*N)*((g i^T)⁻¹^N*R)=D*R*g i^n; rw [pow_add,pow_mul,inv_pow]; field_simp

structure Fan (f:Filter Ω)(g:Ω→ℝ)(A:Ω→F→ℂ)(V:ℕ→F→ℂ)(U:Set F): Prop where
   target : Banks V U
   -- can use phase-varying pricing even in this profile (uniform in product index)
   bound : ∀ K:Set F,IsCompact K→K⊆U→ ∃ d:ℕ, Chime f g A V K d

structure Breeze (f:Filter Ω)(g:Ω→ℝ)(A:Ω→F→ℂ)(S:Set F): Prop where
   differentiates : ∀ᶠ i in f,∀ x∈S,DifferentiableAt ℝ (A i) x
   rarity : ∀ K:Set F,IsCompact K→K⊆ S→∃ b:ℕ,TagPrice f (fun i=> fderiv ℝ (A i)) K (fun i=> (g i)⁻¹^b)

lemma Fan.power (m:Meter f g)(h : Fan f g A V S) (ho:IsOpen S)(hd:Breeze f g A S)(hk:IsCompact K)(ht:K⊆ S) : Expansion f g A V K:=by
   intro i; apply TagPrice.patch hk (m.warm.mono fun s hx=> pow_nonneg hx.le i); intro x hx
   obtain ⟨r,hr,hR⟩:=Metric.mem_nhds_iff.mp (ho.mem_nhds (ht hx)); let p:=r/4; have hh:0<p:=by unfold p; positivity
   let K:=closedBall x (2*p); have hK:IsCompact K:= isCompact_closedBall ..; have hs:K⊆ S:= (closedBall_subset_ball (by unfold p; linarith : 2*p<r)).trans hR; let U:= closedBall x p; have hx':U⊆K:= closedBall_subset_closedBall (by linarith)
   obtain ⟨b,hb⟩:=hd.rarity K hK hs; obtain ⟨d,hc⟩:= h.bound K hK hs
   have hj:= upgrade_ball m (n:=i) hh hc (fun j x hx=> h.target j x (hs hx)) hb (hd.differentiates.mono fun a ha x hx=> ha x (hs hx)) le_rfl
   let Y(y:ℕ):=TagPrice f (Rem g A V (i+y)) U (fun x=>g x^i); let T:=fun x=> g x^i -- local reuse high trunc
   have hy(j:ℕ) (hh:Y j) : TagPrice f (Rem g A V i) U T:=by
      induction j with
      | zero=> exact hh
      | succ j IH=>
        apply IH; obtain ⟨C,hC⟩:= hK.bddAbove_image (show ContinuousOn (fun x=> ‖V (i+j) x‖) K from fun x hx=>(h.target (i+j) x (hs hx)).continuousAt.norm.continuousWithinAt)
        have ht:TagPrice f (fun x s=> (g x:ℂ)^(i+j)*V (i+j) s) U T:=by
            refine ⟨|C|, abs_nonneg _,?_⟩; filter_upwards [m.short] with v ⟨hr,hH⟩ y hy
            rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hr.le,mul_comm |C|]; exact mul_le_mul (pow_le_pow_of_le_one hr.le hH (Nat.le_add_right ..)) ((hC (mem_image_of_mem _ (hx' hy))).trans (le_abs_self _)) (norm_nonneg _) (pow_nonneg hr.le _)
        unfold Y at *; apply (hh.add ht).congr; apply Eventually.of_forall; intro t l ht; unfold Rem; dsimp only; rw [← Nat.add_assoc, chart_next]; ring
   exact ⟨ball x p, isOpen_ball,mem_ball_self hh,(hy _ hj).parent ball_subset_closedBall⟩
end YM.GapsContact.Pattern
