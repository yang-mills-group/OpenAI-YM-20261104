import YM.RG04B.Vac.Ledger
/-! # Paying local drag (including genuine post-ratio o(1), not rebilling each step) -/
noncomputable section
set_option autoImplicit false
namespace YM.RG04B.Vac
open Function Filter Lattice RG Real
open scoped Topology Classical BigOperators Matrix.Norms.Frobenius
variable {G : Gauge}

/-- `slide e`: each request e's fixed after-block relative o_L(1). Bind
before beta purchase. x read at coarse hatBeta. This permits o(1)
terms also known only eventually at fixed L (not uniformly in J without gate). -/
structure Drag where
  slide : ℕ → Post (ℕ → ℝ → ℝ)
  dwindles e k S L θ j : Tendsto (slide e k S L θ j) atTop (𝓝 0)

def Drag.fund (t : Drag) : Request := { Request.none with
  hat := fun k S L θ j x => ∀ e ≤ j, |t.slide e k S L θ j x| ≤ ((L j).val : ℝ)⁻¹
  eventualHat := fun k S L θ j => by
    have he : 0< (((L j).val:ℝ))⁻¹:= inv_pos.2 (Nat.cast_pos.mpr (L j).pos)
    filter_upwards [(Finset.range (j+1)).eventually_all.mpr fun e _ =>
      (by
        have h := (t.dwindles e k S L θ j).abs
        rw [abs_zero] at h
        exact h.eventually (ge_mem_nhds he) : ∀ᶠ x in atTop, |t.slide e k S L θ j x| ≤ ((L j).val:ℝ)⁻¹)] with x hp e hx
    exact hp e (Finset.mem_range.mpr (Nat.lt_succ_of_le hx)) }

def slowing (t : Drag) (e : ℕ) (a : Levels G) (m : ℕ) := abs (t.slide e a.clock.kernel a.clock.stage a.clock.factor a.clock.theta (a.clock.J (m+1)) (a.clock.hatBeta m))

lemma dwindled (t : Drag) {a : Levels G} (h : Booked t.fund a) (e : ℕ) :
    ∀ᶠ m in atTop, slowing t e a m ≤ (ratio a m)⁻¹ := by
  filter_upwards [(a.fits.deep.comp (tendsto_add_atTop_nat 1)).eventually_ge_atTop e] with m hm
  rw [ratio,← a.fits.sameFactor]; exact h.hats m _ hm

variable {C : Family G}
set_option quotPrecheck false
local notation "P" => C.path.levels
local notation "L" => ratio C.path.levels
local notation "B" => C.path.levels.clock
local notation "ℓ" => logSize C.path.levels
local notation "U" => C.path.levels.budget

abbrev temporal (a : Levels G) (i) := (a.budget i).threshold
local notation "t" => temporal C.path.levels

def zone (g : ℝ) (r : ℕ) (ε : ℝ) : ℝ := g ^ ((r:ℝ)+1-ε)
def money (C : Family G) (e N p m : ℕ) (ε : ℝ) := zone (gAt C N p m) e ε
lemma ratio_exit (C : Family G) : Tendsto (ratio C.path.levels) atTop atTop := by
  refine tendsto_atTop.2 (fun x=>?_)
  let y:=max 1 x; have hy: 0<y:= zero_lt_one.trans_le (le_max_left ..)
  filter_upwards [Trace.Physical.GermGraph.factor_large C y⁻¹ (inv_pos.mpr hy)] with m h
  exact le_trans (le_max_right ..) (inv_inv y ▸ h.1)

def toll (a : Levels G) (m : ℕ) := ratio a m ^ ((1:ℝ)/8)
local notation "z" => toll C.path.levels
lemma toll_one {a : Levels G} (j) : 1 ≤ toll a j := Real.one_le_rpow (le_trans (by norm_num : (1:ℝ) ≤ 3) (ratio_lo ..)) (by norm_num)
lemma boughtToll {tF : Fees} (h : stripe tF P) : Budgeted P z := by
  apply y_spend.shorten
  apply Eventually.of_forall
  intro m; refine ⟨zero_le_one.trans (toll_one m), le_trans ?_ (limitRatio h m)⟩
  apply le_trans _ (Real.rpow_one (ratio P m)).le
  exact Real.rpow_le_rpow_of_exponent_le ((by norm_num : (1:ℝ) ≤ 3).trans (ratio_lo ..)) (by norm_num)

lemma fades {tF : Fees} (h : stripe tF P) (D : Drag) (hD : Booked D.fund P) (e : ℕ) {δ:ℝ} (hδ:0 < δ) :
    ∀ᶠ i in atTop,
      let f:= firstBill tF P e i; z i * f * (f/L i + slowing D e P i) ≤ δ := by
  have ht:= (tendsto_rpow_atTop (by norm_num : 0 < ((1:ℝ)/8))).comp (ratio_exit C)
  filter_upwards [common h e (by norm_num: 0<(1:ℝ)/8),dwindled D hD e,
    ht.eventually_ge_atTop (2 / δ)] with i hf hg hz
  intro k
  let u:= z i; have hX: 0<u := zero_lt_one.trans_le (toll_one i)
  have hδ': 1≤u:= toll_one _
  have he: k ≤ u:= hf.1
  have h₀:0<L i:= by linarith [ratio_lo P i]
  have hK : 0≤k := zero_le_one.trans (atLeastOne tF P e i).1

  have hv : u^8 = L i := by
    unfold u toll
    rw [← Real.rpow_natCast,← Real.rpow_mul h₀.le]; norm_num
  calc
     _ ≤ u * u * (u / L i + u/L i) := by
       apply mul_le_mul
       · exact mul_le_mul_of_nonneg_left he hX.le
       · exact add_le_add (div_le_div_of_nonneg_right he h₀.le) (hg.trans (show (L i)⁻¹ ≤ u/L i from by rw [← one_div]; exact div_le_div_of_nonneg_right hδ' h₀.le))
       · exact add_nonneg (div_nonneg hK h₀.le) (abs_nonneg _)
       exact mul_nonneg hX.le hX.le
     _ = 2/(u^5) := by rw [←hv]; field_simp; ring
     _ ≤ 2/u := div_le_div_of_nonneg_left (by norm_num) hX (by simpa only [pow_one] using (pow_le_pow_right₀ hδ' (show 1≤5 by decide)))
     _ ≤ δ := (div_le_comm₀ hX hδ).mpr hz

variable (hC : C.Makes) (hG : G.Simple)
include hC hG
lemma vanishT (c : ℕ→ℝ) {ε : ℝ} (he : 0<ε) (h : Budgeted P c) : ∀ᶠ i in atTop, c i * t i ≤ ε := by
  have hp (i) : t i ≤ gAt C i 0 i * (2*(B).monitor i) := (thresholdHat hC le_rfl).1
  obtain ⟨u,K,l,hx⟩:=h
  filter_upwards [keepPaid hC hG zero_lt_one he
    (Budgeted.mul (show Budgeted P c from ⟨u,K,l,hx⟩) ((Budgeted.const zero_le_two).mul (livingPrices hG).2.1)),hx] with i hi hz
  have hy:= hi i 0 le_rfl
  refine (mul_le_mul_of_nonneg_left (hp i) hz.1).trans ?_
  rw [Real.rpow_one] at hy; linarith only [hy]

-- General calibration refund at a finer adjacency bill
lemma shift_marker {tF : Fees} (h : stripe tF P) (hc : Booked requireConversion P) (d : ℕ) {δ:ℝ} (hd : 0 < δ) :
    ∀ᶠ m in atTop, ∀ N p : ℕ, m < N → ∀ R, Remodeled C N p m R →
      |R.beta - C.path.β N p m| ≤ δ * (gAt C N p (m+1)) ^ d := by
  have hx:∀ m : ℕ, logSize P (m+1) ≤ 1*ℓ (m+1)^1:=by intro i; simp
  have he:= keepPaidStep hC hG zero_lt_one hd (Budgeted.const (a:=P) (show 0 ≤ (4:ℝ)^(d+1) by positivity))
  filter_upwards [offsets hC hG hc (d+1),(tendsto_add_atTop_nat 1).eventually
    (windowCoupling hC hG 0 1 1), he] with i hi hv he N p hN R hr
  let k:=gAt C N p (i+1); have hp : 0<k:= running_pos hC _ _ _ hN
  have hs:= limitRatio h i
  have hl : C.S.scale (i+1)-C.S.scale i ≤ 1*ℓ (i+1)^1:= by
    rw [C.S.scale_succ,add_sub_cancel_left]
    apply le_trans _ (hx i)
    have hw:=Real.log_le_self (zero_le_three.trans (ratio_lo P i))
    exact hw.trans (hs.trans ((monotone_geo P hG i.le_succ).trans (ySmall (i+1))))
  have hy : gAt C N p i ≤ 4*k := (hv N p hN i (Nat.le_succ i) hl).2.2
  have hE: 4^(d+1)*k ≤ δ:= Real.rpow_one k ▸ he N p hN
  refine (hi N hN.le p _ hr).trans ((pow_le_pow_left₀ (running_pos hC _ _ _ hN.le).le hy (d+1)).trans ?_)
  calc
    _ = 4^(d+1)*k*k^d := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hE (pow_nonneg hp.le d)

/-- Input/outgoing calibration allowances and their fixed negative-power costs.
ζ counted once here; fine variable for all. -/
lemma debts {tF : Fees} (h : stripe tF P) (hc : Booked requireConversion P)
    (d r : ℕ) {ε δ : ℝ} (he : 0 < ε) (hd : 0 < δ) {f : ℕ→ℝ} (hg : Budgeted P f) :
    ∀ᶠ m in atTop, ∀ N p, m < N →
      let G' := gAt C N p (m+1)
      let X:= money C r N p (m+1) ε
      (∀ Y, Remodeled C N p m Y → f m * (G'⁻¹ ^ d * |Y.beta-C.path.β N p m|) ≤ δ*X) ∧
      (∀ Y, Remodeled C N p (m+1) Y → f m * (G'⁻¹ ^ d * |Y.beta-C.path.β N p (m+1)|) ≤ δ*X) ∧
      f m * G'^(r+1) ≤ δ*X := by
  obtain ⟨c,hc',n,hM⟩:=hg
  filter_upwards [shift_marker hC hG h hc (d+(r+1)) zero_lt_one,(tendsto_add_atTop_nat 1).eventually (offsets hC hG hc (d+(r+1))),
    keepPaidStep hC hG he hd (show Budgeted P f from ⟨c,hc',n,hM⟩),hM] with m hs ht hh hF N p hN
  let x:= gAt C N p (m+1); let T:=money C r N p (m+1) ε
  have hx:0<x:=running_pos hC _ _ _ hN
  have hv: 0≤T := Real.rpow_nonneg hx.le _
  have ha:f m * x^(r+1) ≤ δ*T := by
    calc
     _ = f m * x ^ε * T := by unfold T money zone; rw [mul_assoc (f m) (x^ε),← Real.rpow_add hx, show ε+((r:ℝ)+1-ε)=(r:ℝ)+1 from by ring, ← Nat.cast_add_one, Real.rpow_natCast]
     _ ≤ _ := mul_le_mul_of_nonneg_right (hh N p hN) hv
  have H(y : ℝ) (hy:y ≤ x^(d+(r+1))): f m * (x⁻¹ ^d * y) ≤ δ*T := by
    apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hy (pow_nonneg (inv_nonneg.mpr hx.le) d)) hF.1).trans
    rw [pow_add,← mul_assoc (x⁻¹ ^d), inv_pow,inv_mul_cancel₀ (pow_ne_zero _ hx.ne'),one_mul]
    exact ha
  intro G' X
  exact ⟨fun Y hy=> H _ (by simpa only [one_mul] using hs N p hN Y hy),fun Y hy=>H _ (ht N hN p Y hy),ha⟩
end YM.RG04B.Vac
