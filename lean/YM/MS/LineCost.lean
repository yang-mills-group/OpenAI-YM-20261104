import YM.MS.Profiles

/-! Damping bounds on polynomial times Gaussian (both momentum propagators) -/
set_option autoImplicit false
noncomputable section
namespace YM.MS
open Set Function Real Momentum Filter
open scoped Topology ContDiff
variable {ι A F : Type*} [Fintype A]
variable {S : Scale ι}

section gaussian
variable (S)
lemma cost_of_spread {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Kern ι (Momentum A) E} {a : ι → ℝ}
    (h : Costs S.full S f (fun i p=> a i*spreadCost S i p)) (ha : ∀ i, 0≤ a i) :
    Line S (fun _=> firstZone A) f a ∧ Bound S f a := by
   have hD : (S.region (fun _=> firstZone A)).Le (spreadCost S) (S.damp 1) :=
      ⟨exp 1,exp_pos _,0,fun i p hp => by simpa using spread_damp i p hp⟩
   constructor
   · refine (h.localize.raise ?_).damped ha zero_lt_one
     simpa [mul_comm (a _)] using hD.cancel (fun (i:ι) (_: Momentum A) (_: _)=>ha i)
   exact h.raise (Cost.of_le fun i p _ => mul_le_of_le_one_right (ha _) (spread_limit i p))

lemma continuumLine {a : ι→ℝ} (ha : ∀ i, 0 ≤ a i) {f : Kern ι (Momentum A) ℝ} (h : Bound S f a) :
   Line S (fun _=>univ) (fun i p=> f i p * exp (-(leaf S i p).sq)) a := by
   have hg : Bound S (fun i (p : Momentum A) => - (leaf S i p).sq) fun _=>1:= S.rescaled (by
      refine HasTemperateGrowth.neg (show Function.HasTemperateGrowth (Momentum.sq (A:=A)) from ?_) -- Δ un
      unfold Momentum.sq; refine HasTemperateGrowth.sum (fun i _=>?_); exact (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : A=>ℝ) i).hasTemperateGrowth.pow 2)
   refine ((h.rmul hg.exp_full).localize.raise ?_).damped ha (c:=1) zero_lt_one
   have hw : (S.region (fun _=> (univ:Set (Momentum A)))).Le (fun i p=> exp (- (leaf S i p).sq)) (S.damp 1) := by
     refine ⟨exp 1, exp_pos _,0, fun i p _=>?_⟩
     have hp:=sup_square (leaf S i p); rw [leaf,norm_smul_of_nonneg (S.pos _).le] at hp
     simp only [pow_zero, mul_one,Scale.damp,← exp_add]; apply exp_monotone; unfold leaf; nlinarith [sq_nonneg (S.length i * ‖p‖-1)]
   simpa [mul_comm (a _)] using hw.cancel (fun (i:ι) (_: Momentum A) (_: _)=>ha i)
end gaussian
abbrev propagated (S : Scale ι) (φ : Momentum A→ℝ) : Prop :=
    profileCost S φ (fun _ _=>1) ∧ Function.HasTemperateGrowth φ
namespace propagated
variable {f g : Momentum A→ℝ}
lemma const (x : ℝ) : propagated (A:=A) S (fun _=>x):= ⟨profile_const S x, HasTemperateGrowth.const x⟩
lemma add (h : propagated S f) (H : propagated S g) : propagated S (fun x=> f x + g x):= ⟨h.1.add H.1, h.2.add H.2⟩
lemma sub (h : propagated S f) (H : propagated S g) : propagated S (fun x=> f x - g x):= ⟨h.1.sub H.1, h.2.sub H.2⟩
lemma mul (h : propagated S f) (H : propagated S g) : propagated S (fun x=> f x * g x):= ⟨by simpa using profile_mul h.1 H.1,h.2.mul H.2⟩
lemma comp (h : ∀ i, 1≤S.length i) (a:A): propagated S (fun p:Momentum A=> p a):= ⟨omega_check h a,(ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : A=>ℝ) a).hasTemperateGrowth⟩
lemma summed (h : ∀ i, 1≤S.length i) : propagated S (Momentum.sq (A:=A)) := by
    refine ⟨profile_sq h,?_⟩; unfold Momentum.sq; exact HasTemperateGrowth.sum fun i _=> (comp h i).2.pow 2
end propagated

/-- Raw multiplier builder before substituting momentum. `a` is the engineering exponent; request the
   raw numerator at unit R. Uses real coefficient. -/
def coat {A : Type*} [Fintype A] (a: ℕ) (t:ℝ) (φ : Momentum A→ℝ) (x : Momentum A) :=
  t^a * (φ (t • x)*exp (-(t • x).sq))
structure PropagatorCosts (S : Scale ι) (μ : ι → ℝ) (T P : Kern ι (Momentum A) ℝ) : Prop where
  both : Like S.full S (phaseDiff S) T P (fun i _=> μ i)
  cover : Line S (fun _=>univ) P μ
  lattice : Line S (fun _=>firstZone A) T μ
  close : Line S (fun _=>firstZone A) (fun i x=> T i x - P i x) (fun i=>μ i * phaseDiff S i)
lemma propagated.coatCost {f : Momentum A→ℝ} (h : propagated S f) (a : ℕ) (ht : ∀ i, 1≤ S.length i) : PropagatorCosts S (fun i=> S.length i ^ a)
    (fun i x=> coat a (S.length i) f (wave x)) (fun i x=> coat a (S.length i) f x) := by
   let r (i:ι) := S.length i ^ a; have hr i : 0≤ r i:= pow_nonneg (S.pos _).le _
   have he : Bound S (fun i (_:Momentum A)=> S.length i ^ a) r := Costs.scalar (p:=r) (Cost.of_le fun i _ _=> by rw [Real.norm_of_nonneg (hr i)])
   have hx := Like.same (g:=phaseDiff S) (fun i=>(pd_pos i).le) he
   let T i (x:Momentum A):= coat a (S.length i) f (wave x); let P i:= coat a (S.length i) f
   have H : Like S.full S (phaseDiff S) T P (fun i p=> r i*spreadCost S i p):= by
     convert! hx.rmul (h.1.rmul (profile_exp ht)) using 1; ext; simp
   obtain ⟨hL,hT⟩:= cost_of_spread S H.lat hr
   obtain ⟨_,hB⟩:= cost_of_spread S H.std hr
   have hb : Costs S.full S (fun i x=>T i x - P i x) (fun i p=> (r i * phaseDiff S i)*spreadCost S i p) := by
     convert H.gain using 1; ext; ring
   obtain ⟨hC,hD⟩:= cost_of_spread S hb (fun i=>mul_nonneg (hr i) (pd_pos _).le)
   refine ⟨⟨hT,hB,hD⟩,?_,hL,hC⟩
   unfold coat
   simp_rw [← mul_assoc (S.length _ ^ a)]
   apply continuumLine S hr (f:=fun i p=> S.length i ^ a*f (leaf S i p))
   simpa [r] using he.rmul H0
where
 H0 : Bound S (fun i p=> f (leaf S i p)) (fun _=>1):= h.1.std
end YM.MS
