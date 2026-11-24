import YM.FormalOPE.RG10.Transit.Meeting
import YM.FormalOPE.RG10.Transit.Turn

/-!
# A first-join-through-time estimate for approaching a remote probe

`t` is the far mesh, increasing to `b` capture and `N` top. Inputs already individually
interpreted in the stated Lenses. `P` serves here as a signed intrinsic difference (a joint
cluster minus predicted captures), assembled BEFORE joining exterior(s) X. Neither estimates on
mixed cluster differences nor on individual *graph* sums are required; ordinary LINEAR
transmission of gauge-invariant kernels, including its multiplication error, is used. Need norms
on **full capture remainder** in these polynomials after restoring factors, here `Monitor`.
Later apply through the same rootwise tests used for that norm, not all modes or profile choices
of a canonical basis implicitly. The conclusion is a terminal norm that can be probed with
any allowed scalar/profile functionals at the reading stop; we don't interpret it on contact
geometries. Doesn't assume exterior must be only one field, can carry full sum and its own tested
weights.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Transit.Far
open Route PowerSeries Finset Function Voyage Weave
open scoped Topology BigOperators Classical
variable {U J : ℕ→Type} {X : Type} {V : Voyage U J} {W : Scale X U} {A E O : Lens W.tape}
variable [∀ i,Fintype (U i)] [∀ i,Fintype (J i)] [∀ i,DecidableEq (U i)]
    {F : ∀ i, Subring (Channel (U i))} {C ξ : ℝ} {k b t N p l q n r d d₁ d₂ δ m : ℕ} {P Q : Channel (U N)}

structure Monitor (V : Voyage U J) (W : Scale X U) (F : ∀ i, Subring (Channel (U i)))
    (A E O : Lens W.tape) (C ξ : ℝ) (t b N p l q n r d d₁ d₂ δ : ℕ) (P Q : Channel (U N)) (m : ℕ) : Prop where
  regular : Regular V W (W.μ t) C δ t N r d n F O
  rankOne : Guard P r d₁
  rankTwo : Guard Q r d₂
  toprank : d₁+d₂ ≤ d
  one : P∈ F N
  two : Q∈ F N
  apart : A.Spaced E (W.μ t/C^δ)
  cheap₁ : O.m ≤ A.m
  cheap₂ : O.m ≤ E.m
  young : ∀ i∈ Icc b N,W.value i (maximumNeeded n r d) r A (V.yield i N P) ≤ tally W C (W.μ t) i p l
  exterior : ∀ i∈ Icc t N, W.value i (maximumNeeded n r d) r E (V.yield i N Q) ≤ tally W C (W.μ t) i p q
  -- `m` the announcement horizon; uniformly in all capture-age bills; after testing center profile
  restored : ∀ i∈Icc t b, W.value i (maximumNeeded n r d) r A (V.yield i N P) ≤
      (W.Y C (W.μ t) b)^p * W.fade (m+ξ) b i

-- ζ encoded here alongside μ-spacing, from the matched residual
local notation "μ" => W.μ
local notation "R" => W.μ t
local notation "Y" => W.Y C (W.μ t)
local notation "Cp" => Episode.pressure r d
local notation "ω" => W.fade (m+ξ) b
variable (M : Monitor V W F A E O C ξ t b N p l q n r d d₁ d₂ δ P Q m) (ht:t ≤ b) (hb:b ≤ N)
include M

private lemma inOne (i : ℕ) (hi:i∈Ico t N) {S : ℝ} (he:W.value (i+1) (maximumNeeded n r d) r A (V.yield (i+1) N P) ≤ S) :
    tip (R/C^δ / μ i) n * W.value i n r O (V.impulse P Q i) ≤
      (Y i^δ)^Cp * S * tally W C R (i+1) p q := by
  have hr : i+1∈ Icc t N := mem_Icc.mpr ⟨(mem_Ico.mp hi).1.trans (Nat.le_succ _),(mem_Ico.mp hi).2⟩
  obtain ⟨hk,hB⟩:=mem_Icc.mp hr
  have h:= M.regular.rank.clip hk le_rfl; have hv := M.regular.toHours.paid (mem_Ico.mp hi).1; have hw := W.positive t
  have hS:= (W.nn ..).trans he; have hC : 0 ≤ C:= by linarith [M.regular.rich];
  apply (V.event W r d n A E O M.cheap₂ M.cheap₁ M.apart (by positivity) (M.regular.fund i hi)
    (Guard.mono (positions h M.rankOne hB) ((Nat.le_add_right ..).trans M.toprank)) (Guard.mono (positions h M.rankTwo hB) ((Nat.le_add_left ..).trans M.toprank))).trans
  exact mul_le_mul (mul_le_mul_of_nonneg_left ((W.sooner _ A _ r _ _ (le_max_right ..)).trans he) (by positivity)) ((W.sooner _ E _ r _ _ (le_max_right ..)).trans (M.exterior _ hr)) (W.nn ..) (by positivity)

def tagged (r d p q l δ n:ℕ) := δ*Episode.pressure r d + δ*(p+p) + δ*(l+q) + δ*n
include ht
lemma high (i : ℕ) (hi:i∈ Ico b N) (hr:l+q ≤ n) :
    W.value i n r O (V.impulse P Q i) ≤ (Y i)^tagged r d p q l δ n * (μ i/R)^(n-(l+q)) := by
  have hu := (mem_Ico.mp hi).1; have he := ht.trans hu
  have hw : i∈ Ico t N:= mem_Ico.mpr ⟨he,(mem_Ico.mp hi).2⟩
  have h := inOne M i hw (M.young (i+1) (mem_Icc.mpr ⟨hu.trans (Nat.le_succ _),(mem_Ico.mp hi).2⟩));
  have hh:= M.regular.toHours; apply hh.reap he _ _ _ hr (le_trans h ?_)
  let T:= tally W C R (i+1); let z:= (Y i)^δ; have hY := hh.paid he
  rw [mul_assoc, show T p l * T p q = T (p+p) (l+q) from ?_]; swap
  · unfold T tally; simp only [pow_add]; ring
  apply (mul_le_mul_of_nonneg_left (hh.further _ (l+q) hw (p+p)) (by positivity)).trans
  exact Eq.le (by simp only [pow_add,pow_mul]; ring)

lemma highTail (hv : l+q+2 ≤ n) (hb:b ≤ N) :
    W.value t n r O (∑ i∈Finset.Ico b N, V.yield t i (V.impulse P Q i)) ≤
      (Y b)^Scale.absorb (δ+tagged r d p q l δ n)*(μ b/R)^(n-(l+q)) := by
  apply (W.sum' ..).trans
  have hh:= M.regular.toHours; apply le_trans _ (W.shorten R C hh.base hh.rich _ _ (by omega) ht hb)
  apply Finset.sum_le_sum; intro i hi; have hi':= Ico_subset_Ico ht le_rfl hi; obtain ⟨hy,hH⟩:=mem_Ico.mp hi'
  have hu := M.regular.selfish.clip hy le_rfl
  have hw := M.regular.rank.clip hy le_rfl; have H0 := hh.paid hy
  rw [pow_add,mul_assoc];
  apply (M.regular.stable t (mem_Icc.mpr ⟨le_rfl,ht.trans hb⟩) i (Ico_subset_Icc_self hi') _ (impulse_closed hu M.one M.two hH) (Guard.mono (impulse_guard hw M.rankOne M.rankTwo hH) M.toprank)).trans (mul_le_mul_of_nonneg_left (high M ht i hi (by omega)) (by positivity))
private lemma convert_cost (i : ℕ) (hi:i∈ Ico t b) (hb:b ≤ N) (hξ : ξ ≤ 1) :
    ω (i+1) ≤ ω t * ( (Y b)^δ * (R/μ i) )^(m+1) := by
  let y:= W.ticks t (i+1); have he : t ≤ i := (mem_Ico.mp hi).1
  have hy : 0 ≤ y := W.ticks_pos (he.trans (Nat.le_succ _));
  have hh := M.regular.toHours; have hw:= hh.paid ht; have hu := (mem_Ico.mp hi).2.le
  have hz : Real.exp ((m+ξ)*y) ≤ (R/μ (i+1))^(m+1) := by
    rw [← W.ticks_exp, ← Real.exp_nat_mul]; apply Real.exp_monotone; push_cast; change _ ≤ ((m:ℝ)+1)*y; nlinarith
  have hT:= W.positive t; have hU:=W.positive i; have hj:=W.positive (i+1)
  have hl : ω (i+1)=ω t*Real.exp ((m+ξ)*y) := by unfold Scale.fade; rw [Scale.ticks_add W (i+1) (i:=t) (N:=b),← Real.exp_add]; unfold y; ring_nf
  rw [hl]; gcongr;
  · exact W.fade_nn -- inspect
  apply hz.trans; apply pow_le_pow_left₀ (by positivity); exact (hh.exchange (Ico_subset_Ico le_rfl hb hi)).trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hh.paid he) (W.sees R C hh.base hu) _) (by positivity))

include hb
def soft (r d n δ m q p : ℕ) := δ*Episode.pressure r d +δ*n + p + p + δ*(m+1+q)
variable (hξ:ξ ≤ 1) (hn: q+m+1 ≤ n)
include hn hξ
lemma lowerPrice (i : ℕ) (hi:i∈ Ico t b) : W.value i n r O (V.impulse P Q i) ≤ (Y b)^(soft r d n δ m q p) * ω t := by
  have h':= Ico_subset_Ico le_rfl hb hi
  have hu:=(mem_Ico.mp hi).1; have hi':=(mem_Ico.mp hi).2; have hv := M.regular.toHours
  have hb':=M.restored (i+1) (mem_Icc.mpr ⟨hu.trans (Nat.le_succ _),hi'⟩)
  have hh:= inOne M i h' hb'
  let A:= R/μ i; let Z:=Y b; have hA : 1 ≤ A:= hv.near1 hu
  have hZ : 1 ≤ Z:= le_trans (by norm_num) (hv.richAt ht)
  have hz:= zero_le_one.trans hZ; have hw:= zero_lt_one.trans_le hZ
  have ha:= zero_lt_one.trans_le hA
  have hY:= hv.paid hu; have he : 0 ≤ ω t := W.fade_nn; let w:=q+m+1
  let S:= Z^δ*A; have hS : 1 ≤ S := hA.trans (le_mul_of_one_le_left ha.le (one_le_pow₀ hZ)); have hs:=zero_lt_one.trans_le hS
  have hiV : R/μ (i+1) ≤ S:= (hv.exchange h').trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hv.paid hu) (W.sees R C hv.base hi'.le) _) ha.le)
  have ht' : 0 ≤ R/μ (i+1):= div_nonneg (W.positive _).le (W.positive _).le
  have hx':= hv.paid (hu.trans (Nat.le_succ _))
  let K := ω t*(Z^(δ*Cp+p+p+δ*w))
  have hk : Z^p*ω (i+1) ≤ Z^p*(ω t*S^(m+1)) := mul_le_mul_of_nonneg_left (convert_cost M ht i hi hb hξ) (by positivity)
  have h0 : (Y i^δ)^Cp*(Z^p*ω (i+1)) ≤ (Z^δ)^Cp * (Z^p * (ω t*S^(m+1))) := mul_le_mul (pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ hY (W.sees R C hv.base hi'.le) δ) _) hk (mul_nonneg (by positivity) W.fade_nn) (by positivity)
  have hr0 : tally W C R (i+1) p q ≤ Z^p * S^q := mul_le_mul (pow_le_pow_left₀ hx' (W.sees R C hv.base (show i+1 ≤ b from hi')) _) (pow_le_pow_left₀ ht' hiV _) (by positivity) (by positivity)
  let L:=W.value i n r O (V.impulse P Q i); let U:= (R/C^δ)/μ i
  have hL : 0 ≤ L:= W.nn ..
  have hC : 0<C:=by linarith [hv.rich]
  have hU : 0<U := div_pos (div_pos (W.positive _) (pow_pos hC _)) (W.positive _)
  have hβ : (A/Z^δ)^n * L ≤ K*A^n := calc
    _ ≤ tip U n * L := by
      apply mul_le_mul_of_nonneg_right ?_ hL; apply pow_le_pow_left₀ (by positivity)
      apply le_add_of_nonneg_of_le (by norm_num : (0:ℝ) ≤ 1)
      rw [show U = A / C^δ from by unfold U A; ring]
      exact div_le_div_of_nonneg_left ha.le (by positivity) (pow_le_pow_left₀ hC.le (hv.zees ht) _)
    _ ≤ (Z^δ)^Cp*(Z^p*(ω t*S^(m+1))) * (Z^p*S^q) := hh.trans (mul_le_mul h0 hr0 (mul_nonneg (by positivity) (by positivity)) (by positivity))
    _ = K*A^w := by unfold K S w; rw [show q+m+1=m+1+q from by omega]; simp only [pow_add,pow_mul,mul_pow]; ring
    _ ≤ K*A^n := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hA hn) (by unfold K; positivity)
  change L ≤ Z^soft r d n δ m q p * ω t
  apply (mul_le_mul_iff_right₀ (pow_pos (div_pos ha (show 0 < Z^δ by positivity)) n)).mp; apply hβ.trans; unfold soft K w; apply le_of_eq; simp only [pow_add,pow_mul]; simp_rw [div_pow]; unfold A; field_simp; try ring

lemma subcost : W.value t n r O (∑ i∈Finset.Ico t b, V.yield t i (V.impulse P Q i)) ≤
    (Y b)^(2+δ+soft r d n δ m q p)*ω t := by
  have H:= M.regular; have hh:= H.toHours; have he:= hh.paid ht; have hz : 0 ≤ ω t := W.fade_nn;
  let Z:=(Y b)^(δ+soft r d n δ m q p)*ω t; have hZ : 0≤Z:=by unfold Z; positivity
  apply (W.sum' ..).trans; apply le_trans (b:=∑ i∈Ico t b,Z) (sum_le_sum fun i hi=> ?_) ?_; swap
  · have hi':=Ico_subset_Ico le_rfl hb hi; obtain ⟨hv,hy⟩:=mem_Ico.mp hi'; have hu' :=H.selfish.clip hv le_rfl
    apply (H.stable _ (mem_Icc.mpr ⟨le_rfl,hv.trans hy.le⟩) _ (Ico_subset_Icc_self hi') _ (impulse_closed hu' M.one M.two hy) (Guard.mono (impulse_guard (H.rank.clip hv le_rfl) M.rankOne M.rankTwo hy) M.toprank)).trans
    unfold Z; rw [pow_add, mul_assoc]; exact mul_le_mul (pow_le_pow_left₀ (hh.paid hv) (W.sees R C hh.base (mem_Ico.mp hi).2.le) _) (lowerPrice M ht hb hξ hn i hi) (W.nn ..) (by positivity) -- hb shadow
  rw [sum_const,nsmul_eq_mul]; apply (mul_le_mul_of_nonneg_right (W.ticks_number hh le_rfl ht) hZ).trans; unfold Z; simp only [pow_add]; exact Eq.le (by ring)

omit [∀ i,Fintype (U i)] [∀ i,Fintype (J i)] [∀ i,DecidableEq (U i)] M hb hn in
private lemma highPower (h' : l+q+2+m ≤ n) : (μ b/R)^(n-(l+q)) ≤ ω t := by
  have hk := W.ticks_pos ht
  rw [show μ b/R=(R/μ b)⁻¹ from by rw [inv_div],← Scale.ticks_exp, ← Real.exp_neg, ← Real.exp_nat_mul]; apply Real.exp_monotone
  have he : (m +1 : ℕ) ≤ n-(l+q) := by omega
  have hb : (m:ℝ)+1 ≤ ↑(n-(l+q)):= by exact_mod_cast he;
  nlinarith

def invoice (r d n δ p q l m : ℕ) :=
    max (max (p+p) (2+δ+soft r d n δ m q p)) (Scale.absorb (δ+tagged r d p q l δ n)) + 2

omit hn in
theorem looks (h' : l+q+2+m ≤ n) : W.value t n r O (V.yield t N (P*Q)) ≤ (Y b)^invoice r d n δ p q l m * ω t := by
  have hn : q+m+1 ≤ n:=by omega
  let B:=Y b
  let F:=max (max (p+p) (2+δ+soft r d n δ m q p)) (Scale.absorb (δ+tagged r d p q l δ n))
  let K:=B^F*(ω t)
  have hh:=M.regular.toHours; have h2 : 2 ≤ B:= hh.richAt ht; have hz:0 ≤ ω t:=W.fade_nn; have hB : 0≤B:=by linarith
  have hr : 0≤ K:=by unfold K; positivity
  have ht' := ht.trans hb
  have he (p:ℕ) (he:p ≤ F) : B^p * ω t ≤ K:= mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith) he) hz
  have h1 := (subcost M ht hb hξ hn).trans (he _ ((le_max_right ..).trans (le_max_left ..)))
  have h3 := (highTail M ht (by omega) hb).trans ((mul_le_mul_of_nonneg_left (highPower ht hξ h') (show 0 ≤ B^_ by positivity)).trans (he _ (le_max_right ..)))
  have hi : tally W C R t p q ≤ B^p := by unfold tally; rw [div_self (W.positive _).ne',one_pow,mul_one]; apply pow_le_pow_left₀ (hh.paid le_rfl) (W.sees R C hh.base ht)
  let P':=V.yield t N P; let Q':= V.yield t N Q
  have hp : W.value t n r O P' ≤ B^p*ω t := ((W.mono t O A n r _ M.cheap₁).trans ((W.sooner t A n r _ (maximumNeeded n r d) (le_max_left ..)).trans (M.restored _ (mem_Icc.mpr ⟨le_rfl,ht⟩))))
  have hQ : W.value t n r O Q' ≤ B^p:= ((W.mono t O E n r _ M.cheap₂).trans ((W.sooner t E n r _ (maximumNeeded n r d) (le_max_left ..)).trans ((M.exterior _ (mem_Icc.mpr ⟨le_rfl,ht'⟩)).trans hi)))
  have h0 : W.value t n r O (P'*Q')≤ K := (W.mul ..).trans ((mul_le_mul hp hQ (W.nn ..) (mul_nonneg (by positivity) hz)).trans (by rw [mul_right_comm,← pow_add]; exact he _ ((le_max_left ..).trans (le_max_left ..))))
  rw [show V.yield t N (P*Q)= V.apart P Q t+P'*Q' from (sub_add_cancel ..).symm, topdown V P Q ht', ← Finset.sum_Ico_consecutive _ ht hb] -- inspect
  apply (W.add ..).trans; apply (add_le_add ((W.add ..).trans (add_le_add h1 h3)) h0).trans
  calc
    _ ≤ B^2*K := by nlinarith [mul_le_mul_of_nonneg_right (show 4≤B^2 by nlinarith only [h2]) hr]
    _ = _ := by change _=B^(F+2)*_; unfold K; rw [pow_add]; ring
end YM.FormalOPE.RG10.Transit.Far
