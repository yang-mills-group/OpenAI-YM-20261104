import YM.WiderProfiles.Rake.Cluster
import YM.FVA2.Arrival.Schedule
/-!
# A Trial on *all* the admitted samples

WiderProfiles §F.2 (compare Schedule `showR`, `performance`/`marches`, and `Tide.qualifies`).
We will instantiate WAssembly on this geometry. No compact layout parameter and no
splicing of profiles, no `NeBot` assumption on the new filter.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.WiderProfiles
open Function Filter Set Finset Metric MeasureTheory Real Lattice
open MS MS.Tide MS.Fleet MS.Orbit MS.Vista MS.Vane MS.Tone MS.Rake MS.Land MS.Dial
open XSpace.Cirrus Arrival
open Schedule (plot theta)
open scoped Topology ContDiff Classical
variable {n a : ℕ} {c D : ℝ}

/-- Polynomial envelope and the original strictly separated-shape condition. -/
structure Admits (a : ℕ) (c D : ℝ) (s : Sample n) : Prop where
  sized : Schedule.Sized s
  extent (w : Fin n) : ‖plot (familiar s) w‖ ≤ D * (1 + theta s.F)^a
  sep (w z : Fin n) : w ≠ z → c ≤ ‖plot (familiar s) w - plot (familiar s) z‖

lemma Admits.injective {s : Sample n} (h : Admits a c D s) (hc : 0 < c) :
    Injective (plot (familiar s)) := by
  intro w z he
  by_contra hw
  have hpos := hc.trans_le (h.sep w z hw)
  rw [he, sub_self, norm_zero] at hpos
  exact lt_irrefl _ hpos

lemma Admits.conf {s : Sample n} (h : Admits a c D s) (hc : 0 < c) : familiar s ∈ YM.conf n :=
  fun _ _ h' => h.injective hc (congrArg Theater.out h')

abbrev Domain (n a : ℕ) (c D : ℝ) := {s : Sample n // Admits a c D s}
local notation "ι" => Domain n a c D

def along (n a : ℕ) (c D : ℝ) := comap (fun i : Domain n a c D => grab i.val) Front

lemma tended (n a : ℕ) (c D : ℝ) :
    Tendsto (fun i : Domain n a c D => grab i.val) (along n a c D) Front :=
  tendsto_iff_comap.mpr le_rfl

abbrev trial (n a : ℕ) (c D μ : ℝ) : MS.Dial.Trial (Domain n a c D) (Fin n) where
  profile := ⟨fun i => theta i.val.F, fun i => μ-theta i.val.F, fun _ => le_max_right ..⟩
  side i := Schedule.psi i.val.F
  head i := Schedule.bar i.val
  off u i := Schedule.σ i.val u

variable (μ : ℝ)
local notation "T" => trial n a c D μ
local notation "P" => MS.Dial.Trial.profile (trial n a c D μ)

lemma trial_diff (i : ι) (w z : Fin n) :
    (lifted (P) (T).off w - lifted (P) (T).off z) i =
      plot (familiar i.val) w - plot (familiar i.val) z := by
  change testP (Schedule.showR μ) i.val w - testP (Schedule.showR μ) i.val z = _
  rw [Schedule.planes _ μ w i.property.sized.unit,
    Schedule.planes _ μ z i.property.sized.unit]; abel

lemma test_injective (i : ι) (hc : 0 < c) : Injective (testP (T) i) := by
  intro w z he
  apply i.property.injective hc
  apply sub_eq_zero.mp; rw [← trial_diff μ i]
  change testP (T) i w-testP (T) i z=0
  rw [he, sub_self]

lemma diff_roots (i : ι) (w z : Fin n) :
    ‖(info (T).off w - info (T).off z) i‖ =
    (P).roots i * ‖plot (familiar i.val) w - plot (familiar i.val) z‖ := by
  rw [← trial_diff μ, Tide.scaleF, norm_smul_of_nonneg (exp_pos _).le,
    ← mul_assoc, Geo.roots, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]

lemma trial_mesh (n a : ℕ) (c D : ℝ) (hc : 0 < c) (hD : 1 ≤ D) :
    WMesh (trial n a c D μ).profile (info (trial n a c D μ).off) := by
  intro w z hne
  -- bounds in terms of habitat; roots factor unchanged
  let TT := trial n a c D μ
  refine ⟨⟨2 * D * (1 + |μ|)^a, by have hp : 0 < D := zero_lt_one.trans_le hD; positivity,
    a, fun i => ?_⟩, ⟨c, hc, fun i => ?_⟩⟩
  · let U := TT.profile.θ i; let X := TT.profile.habitat i
    have hu : 0 ≤ U := TT.profile.room i
    have hb : 1 + U ≤ (1 + |μ|) * X := by
      have hy : U ≤ |μ| + |μ-U| := by
        nth_rw 1 [show U = μ - (μ-U) by abel]
        exact (le_abs_self _).trans (abs_sub ..)
      change 1 + U ≤ (1 + |μ|) * (1 + |μ-U|)
      nlinarith [abs_nonneg μ, abs_nonneg (μ-U)]
    rw [diff_roots μ]; change exp U * _ ≤ 2 * D * _ * X^a * exp U
    have h := (norm_sub_le ..).trans (add_le_add (i.property.extent w) (i.property.extent z))
    change ‖plot (familiar i.val) w-plot (familiar i.val) z‖ ≤ D*(1+U)^a + D*(1+U)^a at h
    rw [← two_mul] at h; rw [mul_comm (exp U)]
    apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
    refine h.trans ((mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ 1 + U) hb a)
        (zero_le_one.trans hD)) (by norm_num : (0:ℝ) ≤ 2)).trans_eq ?_)
    rw [mul_pow]; ring
  rw [diff_roots μ, mul_comm c]
  exact mul_le_mul_of_nonneg_left (i.property.sep w z hne) (exp_pos _).le

lemma trial_clear (n a : ℕ) (c D : ℝ) : Clearance (trial n a c D μ).side (trial n a c D μ).head :=
  fun i => Schedule.cleared i.val i.property.sized

lemma trial_width (n a : ℕ) (c D : ℝ) : Vista.width (trial n a c D μ).side (trial n a c D μ).head :=
  Vista.centered_size _ _ fun i => (Schedule.bar_lift i.val i.property.sized).symm

lemma stretch (n a : ℕ) (c D : ℝ) :
    XSpace.Expense.Stretched (along n a c D) (fun i : Domain n a c D => grab i.val) :=
  frontier.wider (tended ..)

lemma trial_vanish (n a : ℕ) (c D : ℝ) :
    Tendsto (trial n a c D μ).profile.θ (along n a c D) atTop := by
  let L := along n a c D; let e := fun i : Domain n a c D => i.val.F.spacing
  have h : Tendsto (fun i => Real.log (e i)) L atBot :=
    Real.tendsto_log_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr
      ⟨(stretch n a c D).endpt, Eventually.of_forall fun i => i.val.F.positive⟩)
  exact (tendsto_neg_atBot_atTop.comp h).congr (fun i =>
    (Schedule.theta_value i.property.sized.unit).symm)

lemma trial_sparse (n a : ℕ) (c D : ℝ) (h : WMesh (trial n a c D μ).profile
    (info (trial n a c D μ).off)) : Echo.Sparse (along n a c D) (trial n a c D μ).off := by
  -- Tide.payTune with the same floor
  intro i j hi
  obtain ⟨b,hb,hx⟩ := h i j hi |>.floor
  refine tendsto_atTop_mono ?_ ((tendsto_exp_atTop.comp (trial_vanish μ n a c D)).const_mul_atTop hb)
  intro p; apply (hx p).trans_eq; simp only [Pi.sub_apply, Tone.emb_sub]; rfl

lemma trial_super (n a : ℕ) (c D : ℝ) : Super (along n a c D)
    (trial n a c D μ).side (trial n a c D μ).profile.θ := by
  -- Compare Schedule.boom on Gate
  intro b; let k := ⌈b⌉₊; let L := along n a c D; let A := trial n a c D μ
  let m := fun i : Domain n a c D => grab i.val
  have hk (i : Domain n a c D) : tickA A.side i = XSpace.Expense.sides m i := by
    unfold tickA; change ((periodN (Schedule.psi i.val.F)).val : ℝ)=_
    rw [Schedule.psi_back]; rfl
  filter_upwards [((stretch n a c D).pay k).eventually_ge_atTop 1] with i hi
  have ht : 1 ≤ i.val.F.spacing^k * tickA A.side i := by rw [← hk] at hi; exact hi
  change b * A.profile.θ i ≤ log (tickA A.side i)
  apply le_trans (mul_le_mul_of_nonneg_right (Nat.le_ceil b) (A.profile.room i))
  have hb : i.val.F.spacing = exp (- A.profile.θ i) := (Schedule.bornS i.property.sized.unit).symm
  rw [← Real.exp_le_exp, Real.exp_log (δ_p ..)]
  rw [hb, Real.exp_neg, inv_pow, ← Real.exp_nat_mul] at ht
  simpa only [mul_one] using (le_inv_mul_iff₀ (exp_pos _)).mp ht

lemma embed_bound (i : ι) (w : Fin n) :
    ‖Tone.embed ((T).off w i)‖ ≤ (D*(1+(P).θ i)^a+1)*exp ((P).θ i) := by
  have he := Schedule.approaches i.val μ w i.property.sized.unit
  have hl : ‖testP (T) i w - plot (familiar i.val) w‖ ≤ 1 := he.trans i.property.sized.unit
  have ht : ‖testP (T) i w‖ ≤ D*(1+(P).θ i)^a + 1 := by
    have hx := norm_add_le (testP (T) i w - plot (familiar i.val) w) (plot (familiar i.val) w)
    rw [sub_add_cancel] at hx
    rw [add_comm (_ * _)]; exact hx.trans (add_le_add hl (i.property.extent w))
  change ‖exp (-(P).θ i) • Tone.embed ((T).off w i)‖ ≤ _ at ht
  rw [Real.exp_neg, norm_smul_of_nonneg (by positivity)] at ht
  rw [mul_comm]; exact (inv_mul_le_iff₀ (exp_pos _)).1 ht

lemma finance (n a : ℕ) (c D : ℝ) (hD : 1 ≤ D) :
    ∃ V : Visa (Domain n a c D), WidthW V (trial n a c D μ).profile.η (trial n a c D μ).off ∧
      NearPlan (along n a c D) (trial n a c D μ).profile V (trial n a c D μ).side μ := by
  -- the polynomial envelope purchased at an exponential bank
  let P' := (trial n a c D μ).profile
  let r : ℝ := 2 + a
  let B : Domain n a c D → ℝ := fun i => exp (r * P'.θ i) * (1 + |μ|)
  have hr : 1 ≤ r := by unfold r; have : 0 ≤ (a:ℝ) := Nat.cast_nonneg _; linarith
  have h1 i : exp (P'.θ i) ≤ exp (r * P'.θ i) := by
    apply exp_monotone; exact le_mul_of_one_le_left (P'.room _) hr
  have hv i : exp (r * P'.θ i) ≤ B i := le_mul_of_one_le_right (exp_pos _).le (by simp)
  let V : Visa (Domain n a c D) :=
    ⟨B, fun i => (Real.one_le_exp (P'.room i)).trans ((h1 i).trans (hv i))⟩
  refine ⟨V, ⟨fun i => ?_, fun w => ?_⟩,
    ⟨trial_vanish μ n a c D, trial_super μ n a c D, fun _ => rfl, r+1, ?_⟩⟩
  · change 1+|μ-P'.θ i| ≤ B i
    have h : exp (P'.θ i)*(1+|μ|) ≤ B i :=
      mul_le_mul_of_nonneg_right (h1 i) (by positivity)
    apply le_trans _ h
    have ht := Real.add_one_le_exp (P'.θ i); have hb := abs_sub μ (P'.θ i)
    rw [abs_of_nonneg (P'.room i)] at hb; nlinarith [abs_nonneg μ, Real.one_le_exp (P'.room i)]
  · have hp : 0 < D := zero_lt_one.trans_le hD; refine ⟨D+1, by positivity, 1, fun i => ?_⟩
    rw [Pi.one_apply, pow_one, mul_one]; refine (embed_bound μ i w).trans ?_
    change (D*(1+P'.θ i)^a+1)*exp (P'.θ i) ≤ (D+1)*B i
    have ht := P'.room i; have he := Real.one_le_exp ht
    calc
      _ ≤ (D*(exp (P'.θ i))^a+1)*exp (P'.θ i) := by
        have hx : 1 + P'.θ i ≤ exp (P'.θ i) := by linarith [Real.add_one_le_exp (P'.θ i)]
        gcongr
      _ = D*exp (((a:ℝ)+1)*P'.θ i) + exp (P'.θ i) := by
        rw [add_mul (a:ℝ) 1 (P'.θ i), one_mul, exp_add, Real.exp_nat_mul]; ring
      _ ≤ D*B i + 1*B i := by
        rw [one_mul]; apply add_le_add _ ((h1 i).trans (hv i))
        exact mul_le_mul_of_nonneg_left ((exp_monotone (mul_le_mul_of_nonneg_right
          (by unfold r; linarith) ht)).trans (hv i)) hp.le
      _ = _ := (add_mul ..).symm
  filter_upwards [ (tendsto_exp_atTop.comp (trial_vanish μ n a c D)).eventually
    (eventually_ge_atTop (1+|μ|)) ] with i hi
  change exp (r * P'.θ i) * (1+|μ|) ≤ exp ((r+1)*P'.θ i)
  rw [add_mul r 1, one_mul, exp_add]; exact mul_le_mul_of_nonneg_left hi (exp_pos _).le

lemma height_cost (s : Sample n) (hs : Schedule.Sized s) (r : ℝ) :
    Real.exp (-r * theta s.F) = s.F.spacing ^ r := by
  rw [Real.rpow_def_of_pos s.F.positive, Schedule.theta_value hs.unit]; ring_nf
end YM.FVA2.WiderProfiles
