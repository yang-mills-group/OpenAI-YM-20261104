import YM.RG04B.Fees
import YM.RG01.Vacuum.Flat

/-!
# Price currency on one Family for all-order error iteration

`Budgeted` is an **upper bound** for per-step nonnegative prices, not an
axiom of temperance. Physical instances below including version with
growing stage degree paid; use also for *upper* estimates on signed
magnitudes after modulus. No arbitrary table obtained *after* schedule
choice presumed paid. Reports omit a finite prefix uniform in N,p.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG04B
open RG Real Function Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge}

def ticket (a : Levels G) (t : ℝ) (k i : ℕ) : ℝ := exp (t * geo a i ^ k)
def Budgeted (a : Levels G) (f : ℕ → ℝ) : Prop :=
  ∃ c ≥ (0:ℝ), ∃ k : ℕ, ∀ᶠ i in atTop, 0 ≤ f i ∧ f i ≤ ticket a c k i

section Taxes
variable {a : Levels G} {f g u : ℕ → ℝ}
lemma ticket_pos (a : Levels G) (t k i) : 0 < ticket a t k i := exp_pos _
lemma cash_mono {t r : ℝ} {j k i : ℕ} (ht : 0 ≤ t) (hr : t ≤ r) (hj : j ≤ k) :
    ticket a t j i ≤ ticket a r k i :=
  exp_monotone (mul_le_mul hr (pow_le_pow_right₀ (geo_hi ..) hj)
    (pow_nonneg (zero_le_one.trans (geo_hi ..)) _) (ht.trans hr))
lemma cash_prod (c d : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d) (i j k h : ℕ) (hj : j ≤ h) (hk : k ≤ h) :
    ticket a c j i * ticket a d k i ≤ ticket a (c+d) h i := calc
  _ ≤ ticket a c h i * ticket a d h i :=
    mul_le_mul (cash_mono hc le_rfl hj) (cash_mono hd le_rfl hk) (ticket_pos ..).le (ticket_pos ..).le
  _ = _ := by unfold ticket; rw [←exp_add,add_mul]

lemma cash_add (c d : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d) (i j k h : ℕ) (hj : j ≤ h) (hk : k ≤ h) :
    ticket a c j i + ticket a d k i ≤ ticket a (2+(c+d)) h i := by
  let p : ℝ := ticket a (c+d) h i
  have ht := cash_prod (a:=a) 2 (c+d) (by norm_num) (add_nonneg hc hd) i 0 h h (Nat.zero_le _) le_rfl
  refine (add_le_add (cash_mono hc (le_add_of_nonneg_right hd) hj) (cash_mono hd (le_add_of_nonneg_left hc) hk)).trans ?_
  change p+p ≤ _
  apply le_trans _ ht
  rw [show ticket a 2 0 i = exp 2 from by simp [ticket]]
  rw [← two_mul]; exact mul_le_mul_of_nonneg_right (le_trans (le_add_of_nonneg_right (zero_le_one' ℝ)) (Real.add_one_le_exp _)) (ticket_pos ..).le

lemma Budgeted.shorten (h : Budgeted a f) (hn : ∀ᶠ i in atTop, 0≤g i ∧ g i ≤ f i) : Budgeted a g := by
  obtain ⟨c,h,k,H⟩:=h
  exact ⟨c,h,k,(hn.and H).mono fun _ hi=>⟨hi.1.1,hi.1.2.trans hi.2.2⟩⟩
lemma prepaid (a : Levels G) (c k) (hc : 0 ≤ c) : Budgeted a (ticket a c k) :=
  ⟨c,hc,k,Eventually.of_forall fun _=> ⟨(ticket_pos ..).le,le_rfl⟩⟩
lemma Budgeted.add (h : Budgeted a f) (H : Budgeted a g) : Budgeted a (fun i=>f i+g i) := by
  obtain ⟨c,h,j,hf⟩:=h; obtain ⟨d,H,k,hg⟩:=H
  exact ⟨_,show 0≤2+(c+d) by linarith,max j k,(hf.and hg).mono fun _ hi=> ⟨add_nonneg hi.1.1 hi.2.1,
    (add_le_add hi.1.2 hi.2.2).trans (cash_add c d h H _ _ _ _ (le_max_left ..) (le_max_right ..))⟩⟩
lemma Budgeted.mul (h : Budgeted a f) (H : Budgeted a g) : Budgeted a (fun i=>f i*g i) := by
  obtain ⟨c,h,j,hf⟩:=h; obtain ⟨d,H,k,hg⟩:=H
  exact ⟨_,add_nonneg h H,max j k,(hf.and hg).mono fun _ hi=>⟨mul_nonneg hi.1.1 hi.2.1,
    (mul_le_mul hi.1.2 hi.2.2 hi.2.1 (ticket_pos ..).le).trans (cash_prod c d h H _ _ _ _ (le_max_left ..) (le_max_right ..))⟩⟩
theorem Budgeted.const {x : ℝ} (h : 0 ≤ x) : Budgeted a (fun _=>x) := by
  refine ⟨x,h,0,Eventually.of_forall fun i=>⟨h,?_⟩⟩
  simpa only [ticket,pow_zero,mul_one] using (le_trans (le_add_of_nonneg_right (zero_le_one' ℝ)) (Real.add_one_le_exp x))
theorem Budgeted.pow (h : Budgeted a f) (k : ℕ) : Budgeted a (fun i=>f i^k) := by
  induction k with
  | zero => simpa only [pow_zero] using (Budgeted.const (a:=a) zero_le_one)
  | succ k ih => simpa only [pow_succ] using ih.mul h

lemma y_spend : Budgeted a (geo a) :=
  ⟨1,zero_le_one,1,Eventually.of_forall fun i=> ⟨zero_le_one.trans (geo_hi ..),le_trans
    (le_add_of_nonneg_right (zero_le_one' ℝ)) ((Real.add_one_le_exp (geo a i)).trans_eq (by simp [ticket]))⟩⟩
lemma ledger_spend (a : Levels G) : Budgeted a (logSize a) := by
  refine ⟨1,zero_le_one,1,Eventually.of_forall fun i=> ⟨zero_le_two.trans (logSize_hi ..),?_⟩⟩
  simp only [ticket,pow_one,one_mul]
  exact (exp_log (zero_lt_two.trans_le (logSize_hi ..))).symm.le.trans (exp_monotone (show Real.log (logSize a i) ≤ geo a i from le_add_of_nonneg_left zero_le_one))

-- uniform in all stages even though degrees k may be funded pre- or post-L.
lemma index_spend {T : Fees} (h : stripe T a) (e : ℕ) :
    Budgeted a (firstBill T a e) ∧ Budgeted a (finalBill T a e) := by
  have hr := common h e zero_lt_one
  have he := y_spend (a:=a)
  refine ⟨he.shorten ?_, he.shorten ?_⟩
  · filter_upwards [hr] with i hi; rw [Real.rpow_one] at hi
    exact ⟨zero_le_one.trans (atLeastOne T a e i).1,hi.1.trans (limitRatio h i)⟩
  filter_upwards [hr] with i hi; simp only [Real.rpow_one] at hi
  exact ⟨zero_le_one.trans (atLeastOne T a e i).2,hi.2⟩

/-- Post-block polynomial invoice with stage-dependent (paid) degree. -/
theorem Budgeted.graded (h : Budgeted a f) {u : ℕ → ℝ} {t : ℝ}
    (ht : 0 ≤ t) {k : ℕ} (H : ∀ᶠ i in atTop, 0 ≤ u i ∧ u i ≤ t * geo a i ^ k) :
    Budgeted a (fun i=> (f i) ^ u i) := by
  obtain ⟨c,h,n,hf⟩:= h
  refine ⟨c*t,mul_nonneg h ht,n+k,?_⟩
  filter_upwards [H,hf] with i hu hi
  refine ⟨Real.rpow_nonneg hi.1 _, (Real.rpow_le_rpow hi.1 hi.2 hu.1).trans ?_⟩
  have he:= mul_nonneg h (pow_nonneg (zero_le_one.trans (geo_hi a i)) n)
  apply (Real.rpow_le_rpow_of_exponent_le (one_le_exp he) hu.2).trans
  dsimp [ticket]; rw [Real.rpow_def_of_pos (exp_pos _), Real.log_exp,pow_add]
  exact le_of_eq (congr_arg _ (by ring))

variable (hG : G.Simple)
include hG
/-- Costs readable at both ends of each step. -/
lemma Budgeted.next (h : Budgeted a f) : Budgeted a (fun i=> f (i+1)) := by
  obtain ⟨c,h,k,H⟩:=h
  have hComp := RG01.Vacuum.Flat.nextComparable a hG
  refine ⟨c*2^k, by positivity,k,?_⟩
  filter_upwards [(tendsto_add_atTop_nat 1).eventually H,hComp] with i hi hx
  have hg := Real.log_le_log (zero_lt_one.trans (a.fits.delayed (i+1))) hx
  rw [Real.log_mul (by norm_num) (zero_lt_one.trans (a.fits.delayed i)).ne'] at hg
  have hc : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos zero_lt_two]
  have hb : logSize a (i+1) ≤ 2*logSize a i := by
    let x:= logSize a i
    change 2+Real.log (a.clock.hatBeta _) ≤ 2*x
    have he : x=2+Real.log (a.clock.hatBeta i) := rfl
    linarith only [hc,hg,he,show 2≤x from logSize_hi a i]
  have hv := Real.log_le_log (zero_lt_two.trans_le (logSize_hi ..)) hb
  rw [Real.log_mul (by norm_num) (zero_lt_two.trans_le (logSize_hi a i)).ne'] at hv
  have hy : geo a (i+1) ≤ 2*geo a i := by
    rw [geo_eq a i,geo_eq]; have hz := (geo_hi a i); rw [geo_eq] at hz; linarith
  refine ⟨hi.1,hi.2.trans (exp_monotone ?_)⟩
  calc
    _ ≤ c*(2*geo a i)^k := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans (geo_hi ..)) hy _) h
    _ = _ := by ring

/-- Typical analytic receipts on THIS actual geometry -- not pre-counting volume
proportional quantities. -/
theorem livingPrices : Budgeted a (fun i=> ((a.budget i).B : ℝ)) ∧ Budgeted a (a.clock.monitor) ∧ Budgeted a a.clock.loopCap := by
  have hr := ledger_spend a
  let m:= a.clock
  let x:= logSize a
  have hu : Budgeted a m.monitor := by
    refine ⟨1,zero_le_one,2,?_⟩
    have hS := Real.tendsto_log_atTop.comp <| Real.tendsto_log_atTop.comp (risingHat a hG)
    filter_upwards [hS.eventually_ge_atTop 0] with i hi
    refine ⟨(Real.exp_pos _).le,?_⟩
    apply Real.exp_monotone
    rw [one_mul]
    apply pow_le_pow_left₀ hi
    have hx : 0 < Real.log (m.hatBeta i) := Real.log_pos (a.fits.delayed _)
    apply (Real.log_le_log hx (show Real.log (m.hatBeta i) ≤ logSize a i from le_add_of_nonneg_left zero_le_two)).trans
    exact le_add_of_nonneg_left zero_le_one
  refine ⟨(Budgeted.add (hr.pow 2) (Budgeted.const zero_le_one)).shorten ?_,hu,?_⟩
  · apply Eventually.of_forall; intro i; refine ⟨Nat.cast_nonneg _,?_⟩
    apply (Nat.ceil_lt_add_one (sq_nonneg _)).le.trans
    exact add_le_add_left (pow_le_pow_left₀ (Real.log_pos (a.fits.delayed _)).le (le_add_of_nonneg_left zero_le_two) _) _
  apply Budgeted.mul (Budgeted.const zero_le_two) <| hu.graded (k:=1) zero_le_one ?_
  refine Eventually.of_forall fun i => ?_
  obtain ⟨hg,h'⟩:= a.fits.thetaRange i
  have hJ : 1 ≤ (a.clock.J i:ℝ) := by
    exact_mod_cast (le_trans (by decide : 1 ≤ 4) (a.clock.adm _))
  exact ⟨hg.le,(h'.trans (inv_le_one_of_one_le₀ hJ)).trans (show 1 ≤ 1*geo a i^1 by simpa using geo_hi a i)⟩

/-- Log-growth ticket costs absorbable in the indicated subpower of the
ACTUAL g (products included when ticketing an entire window). -/
lemma runway {ε : ℝ} (he : 0 < ε) (c : ℝ) (k : ℕ) : ∀ᶠ m in atTop,
    c * geo a m ^ k ≤ ε * logSize a m := by
  let ℓ := logSize a; let z (i:ℕ) := Real.log (ℓ i)
  have ht : Tendsto z atTop atTop := Real.tendsto_log_atTop.comp (persist a hG)
  have hf : geo a =O[atTop] z :=
    ((Asymptotics.isLittleO_const_left.mpr (Or.inr (by simpa using!
        (tendsto_abs_atTop_atTop.comp ht)))).isBigO).add (Asymptotics.isBigO_refl _ _)
  have hh := Asymptotics.IsBigO.trans_isLittleO (hf.pow k) ((Real.isLittleO_pow_log_id_atTop (n:=k)).comp_tendsto (persist a hG))
  have hw:= (Asymptotics.IsLittleO.const_mul_left hh c).def he
  filter_upwards [hw] with i hi
  apply (le_abs_self _).trans
  simpa only [Real.norm_eq_abs,comp_apply,id_eq,ℓ,abs_of_nonneg (zero_le_two.trans (logSize_hi a i))] using hi
end Taxes

section Path
variable {C : Family G} (hC : C.Makes) (hG : G.Simple)
include hC hG
set_option quotPrecheck false
local notation "ℓ" => logSize C.path.levels
local notation "V!" => C.path.levels
local notation "t" => C.path.levels.clock

lemma keepPaid {ε δ : ℝ} (he : 0 < ε) (hd : 0 < δ) {u}
    (h : Budgeted V! u) : ∀ᶠ m : ℕ in atTop, ∀ N p, m ≤ N → u m * gAt C N p m ^ ε ≤ δ := by
  obtain ⟨c,h0,n,H⟩:=h
  filter_upwards [runway hG (show 0 < ε/8 by linarith) c n (a:=V!),
    (persist V! hG).eventually_ge_atTop ((- Real.log δ)/(ε/8)), H, runningLogs hC hG] with m hr hl hm ht N p hN
  have hx := running_pos hC N p m hN
  rw [Real.rpow_def_of_pos hx]
  have hi := mul_le_mul_of_nonneg_right ((ht _ p hN).2) he.le
  rw [div_le_iff₀ (by linarith only [he] : 0 < ε/8)] at hl
  apply (mul_le_mul_of_nonneg_right hm.2 (Real.exp_pos _).le).trans
  unfold ticket; rw [← Real.exp_add]; apply (Real.exp_monotone ?_).trans_eq (Real.exp_log hd)
  linarith only [hr,hi,hl]

/-- Thus also losses compared in terms of the actual smaller input coupling even
when the cost is assessed at the coarser/output level. -/
lemma keepPaidStep {ε δ : ℝ} (he : 0 < ε) (hd : 0 < δ) {u}
    (h : Budgeted V! u) : ∀ᶠ m : ℕ in atTop, ∀ N p, m < N → u m * gAt C N p (m+1) ^ ε ≤ δ := by
  obtain ⟨c,h0,n,H⟩:=h
  filter_upwards [keepPaid hC hG he hd (show Budgeted V! u from ⟨c,h0,n,H⟩),H,downhill hC hG] with m hp hv hK N p hm
  exact (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (running_pos hC _ _ _ hm).le (hK _ _ hm) he.le) hv.1).trans (hp _ _ hm.le)

/-- After taking a square-root forced allowance from the actual trajectory --
only spend here *if* justified by inventory/support retained seed estimates.
Do not bound the charge `1/√w` of a long-only tail by this. -/
theorem refund {u : ℕ→ℝ} (H : Budgeted V! u) (d : ℕ) : ∀ᶠ m : ℕ in atTop,
    ∀ N p : ℕ, m < N → u m * Real.sqrt ((t).forcedAllowance m) ≤ gAt C N p (m+1) ^ d := by
  obtain ⟨D,hD,hB⟩:= RG01.Vacuum.Flat.currency V! hG (d+1) 0
  obtain ⟨c,hc,n,he⟩:= H
  have hx:= keepPaidStep hC hG zero_lt_one zero_lt_one ((show Budgeted V! u from ⟨c,hc,n,he⟩).mul (Budgeted.const hD))
  filter_upwards [hx,he] with m hm hw N p hM
  have hz := hm N p hM
  have ht := hB m _ (beta_positive hC N p (m+1) hM) (Or.inl (inBand hC N p (m+1) hM).2)
  rw [pow_zero,one_mul] at ht
  let g : ℝ := gAt C N p (m+1); change _ ≤ D * g^(d+1) at ht
  change u m * D * (g^(1:ℝ)) ≤ 1 at hz; rw [Real.rpow_one] at hz
  refine le_trans (mul_le_mul_of_nonneg_left ht hw.1) ?_
  change u m * (D * g^(d+1)) ≤ g^d
  rw [show u m * (D * g^(d+1)) = (u m*D*g)*g^d by ring]
  apply mul_le_of_le_one_left (pow_nonneg (running_pos hC _ _ _ hM).le _) hz
end Path
end YM.RG04B
