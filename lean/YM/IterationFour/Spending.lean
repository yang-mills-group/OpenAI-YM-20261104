import YM.IterationFour.Running

/-!
# Per-step eta currencies

One index carries the full physical level, cutoff and period data. This is
not convergence along some cherry-picked sequence of Wilson histories. Allows
stating prices with the precise uniformity and geometry of the local uses.
A convenient normalized notation: AC(n) costs W(k)=hat^k for every k<n. A
noninteger exponent causes no difficulty. This is a *accounting* induction,
never a local output assumption supplied by a topological argument.
-/
set_option autoImplicit false
noncomputable section
namespace YM.IterationFour.Spending
open Function Filter Set Lattice Wilson RG Currency
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge}

structure Address where
    top : ℕ
    period : ℕ
    level : ℕ

def pass (D : Address → Prop) := Filter.comap Address.level atTop ⊓ Filter.principal {u|D u}
lemma pass_iff (D P : Address→Prop) : (∀ᶠ u in pass D,P u) ↔
    ∀ᶠ i in atTop,∀ (N q : ℕ), D ⟨N,q,i⟩ → P ⟨N,q,i⟩ := by
  rw [pass,eventually_inf_principal,eventually_comap]
  refine ⟨fun h=>h.mono fun i hi N q h=> hi ⟨N,q,i⟩ rfl h,fun h=>h.mono fun i hi=>?_⟩
  rintro ⟨N,q,k⟩ rfl hk; exact hi N q hk
lemma okay (D : Address→Prop) : ∀ᶠ u in pass D,D u:= eventually_inf_principal.2 (Eventually.of_forall fun _=> id)
lemma at_tail (D : Address→Prop) : Tendsto Address.level (pass D) atTop := tendsto_comap.mono_left inf_le_left

def Account {I : Type*} (a : Levels G) (m : I→ℕ) (L : Filter I) (v : I→ℝ) (n : ℝ) :=
    ∀ k : ℝ,k<n → ∀ᶠ u in L, |v u| ≤ weight a k (m u)

section
variable {I : Type*} {m : I→ℕ} {L : Filter I} {a : Levels G} {v x : I→ℝ} {c s : ℝ}
abbrev Slip (a : Levels G) (P : ℕ→ℝ) := Account a id atTop P 0
namespace Account
lemma relax (h : Account a m L v s) (hx : ∀ᶠ i in L,|x i| ≤ |v i|) : Account a m L x s :=
    fun u hu=> (hx.and (h u hu)).mono fun _ hi=> hi.1.trans hi.2
lemma lower (h : Account a m L v s) (hw : c ≤ s) : Account a m L v c := fun _ ht=> h _ (ht.trans_le hw)
lemma restrict (h : Account a m L v s) {X : Filter I} (he : X≤L) : Account a m X v s :=
    fun _ hu=> (h _ hu).filter_mono he
lemma negative (h : Account a m L v s) : Account a m L (fun u=>-v u) s :=
    h.relax (Eventually.of_forall fun i=> by simp)
lemma unsigned (h : Account a m L v s) : Account a m L (fun u=>|v u|) s :=
    h.relax (Eventually.of_forall fun i=> by simp)
lemma product (h : Account a m L v s) (hp : Account a m L x c) : Account a m L (fun i=>v i*x i) (s+c) := by
  intro k hk
  let b := (s+c-k)/2
  have hb: 0<b := by unfold b; linarith
  filter_upwards [h (s-b) (sub_lt_self s hb),hp (c-b) (sub_lt_self c hb)] with i hi hx
  rw [abs_mul,show k=_ from (show k=(s-b)+(c-b) by unfold b; ring), Currency.weight_add]
  exact mul_le_mul hi hx (abs_nonneg _) (Currency.weight_pos ..|>.le) -- maybe parse
lemma onEdge (a : Levels G) (m : I→ℕ) (L : Filter I) (s : ℝ) : Account a m L (fun u=> Currency.weight a s (m u)) s :=
    fun _ hu=> Eventually.of_forall fun i=> by rw [abs_of_pos (Currency.weight_pos ..)]; exact weight_le a (m i) hu.le
lemma gathered (j : I→ℕ) (ht : Tendsto j L atTop) {v : ℕ→ℝ} (h : Account a id atTop v s) :
    Account a j L (fun i=>v (j i)) s := fun n hn=> ht.eventually (h n hn)

variable (hG : G.Simple) (hm : Tendsto m L atTop)
include hm hG
lemma order (h : Account a m L v s) {k b : ℝ} (hk : k<s)(hb : 0<b) : ∀ᶠ i in L, |v i| ≤ b * weight a k (m i) := by
  filter_upwards [h ((k+s)/2) (by linarith),hm.eventually (buy a hG 1 hb (show k<(k+s)/2 by linarith))] with i hi h
  rw [one_mul] at h
  exact hi.trans h
lemma vanishing (h : Account a m L v s) (hp : 0 < s) (b : ℝ) (hb : 0 < b) : ∀ᶠ i in L, |v i| ≤ b := by
  simpa only [Currency.weight, Real.rpow_zero,mul_one] using Account.order hG hm h hp hb
lemma constant (a : Levels G) (x : ℝ) : Account a m L (fun _ => x) 0 := by
  intro k hk
  have h:=buy a hG |x| zero_lt_one hk
  filter_upwards [hm.eventually h] with i hi
  simpa only [one_mul, Currency.weight,Real.rpow_zero,mul_one] using hi
lemma joint (h : Account a m L v s) (hp : Account a m L x s) : Account a m L (fun i=>v i+x i) s := by
  intro k hk; filter_upwards [order hG hm h hk (half_pos zero_lt_one),order hG hm hp hk (half_pos zero_lt_one)] with i hi hv
  have hx :=abs_add_le (v i) (x i); linarith
lemma repeatOrder (h : Account a m L v s) (j : ℕ) : Account a m L (fun i=> v i^j) (j*s) := by
  induction j with
  | zero=> simp only [Nat.cast_zero,zero_mul,pow_zero]; exact constant hG hm a 1
  | succ j hj=> have he: (↑(j+1):ℝ)*s=j*s+s:=by push_cast;ring
                simpa only [pow_succ, he] using product hj h
lemma absoluteEdge {y : I→ℝ} (hK : ∃ K : ℝ,0<K ∧∀ᶠ i in L, |y i| ≤ K * weight a s (m i)) :
    Account a m L y s := by
  obtain ⟨K,hv,hp⟩:= hK
  have h := (constant hG hm a K).product (onEdge a m L s)
  rw [zero_add] at h
  exact h.relax (hp.mono fun i hi=> hi.trans (le_abs_self _))
end Account
end
open Currency

lemma monitor_cost (a : Levels G) (hg : G.Simple) : Slip a a.clock.monitor := by
  intro k hk
  filter_upwards [(Next.Rank.Station.hat_rate a hg).eventually (Vac.Numbers.cost 1 (-k/2) (by linarith))] with i hi
  rw [abs_of_pos (show 0<a.clock.monitor i from Real.exp_pos _)]
  rw [Real.rpow_one] at hi
  change _ ≤ gain (B a i)^k; rw [rpGain _ (WardBin.hot a i)]
  exact hi
lemma thermal (a : Levels G) (hg : G.Simple) : Account a id atTop a.clock.threshold 1 := by
  have h:Account a id atTop (hat a) 1 := by simpa only [Currency.weight,Real.rpow_one] using! Account.onEdge a id atTop 1
  exact h.product (monitor_cost a hg)|> (add_zero (1:ℝ) ▸ ·)
lemma cover (a : Levels G) (hg : G.Simple) : Slip a (fun i=> ((a.budget i).B:ℝ)) := by
  have he:= monitor_cost a hg
  refine he.relax ?_
  let B:= Currency.B a; let z x:=Real.log (Real.log (x:ℝ))
  have ht:= Next.Rank.Station.hat_rate a hg
  filter_upwards [(Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp ht)).eventually_ge_atTop 5] with i hi
  change 5 ≤ z (B i) at hi
  have hlog := Real.log_pos (a.fits.delayed i); change 0 < Real.log (B i) at hlog
  let Z:= Real.log (B i)
  have hs : 2 * Z^2 ≤ a.clock.monitor i := by
    apply (Real.log_le_log_iff (mul_pos zero_lt_two (sq_pos_of_pos hlog)) (Real.exp_pos _)).1
    rw [Real.log_mul (zero_lt_two.ne') (sq_pos_of_pos hlog).ne',Real.log_pow,Real.log_exp]
    change Real.log 2 + (↑(2:ℕ):ℝ) * z (B i) ≤ _
    push_cast
    change _ ≤ z (B i)^2
    nlinarith only [hi,Real.log_le_sub_one_of_pos zero_lt_two]
  rw [abs_of_nonneg (Nat.cast_nonneg _),abs_of_pos (show 0<a.clock.monitor i from Real.exp_pos _)]
  change (⌈Z^2⌉₊:ℝ) ≤ _
  have hZ : 1 ≤ Z:= by
    change 5≤ Real.log Z at hi; linarith [Real.log_le_sub_one_of_pos (show 0<Z from hlog)]
  nlinarith only [hs, hZ, Nat.ceil_lt_add_one (sq_nonneg Z)]
end YM.IterationFour.Spending
