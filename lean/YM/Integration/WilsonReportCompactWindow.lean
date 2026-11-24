import YM.Integration.WilsonReportCompactSites
import YM.Next.RANK.Station

/-! Uniform native report distances throughout the manuscript's polylogarithmic window. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportCompactWindow
open Filter Set Lattice Wilson RG Source Extraction
open scoped Topology
variable {G : Gauge}

private theorem small_log (A : Levels G) (hG : G.Simple) (b : ℕ) {f : ℝ} (hf : 0 < f) :
    ∀ᶠ k : ℕ in atTop, f * (Real.log (A.clock.hatBeta k))^b ≤ A.clock.hatBeta k := by
  have h := Real.tendsto_log_atTop.comp (Next.Rank.Station.hat_rate A hG)
  have fee := ((Real.isLittleO_pow_exp_atTop (n:=b)).comp_tendsto h).bound (inv_pos.mpr hf)
  filter_upwards [fee,h.eventually_ge_atTop 1] with k H hk
  have hb : 0 < A.clock.hatBeta k := zero_lt_one.trans (A.fits.delayed k)
  change 1 ≤ Real.log (A.clock.hatBeta k) at hk
  change ‖Real.log (A.clock.hatBeta k)^b‖ ≤ f⁻¹*‖Real.exp (Real.log (A.clock.hatBeta k))‖ at H
  rw [Real.exp_log hb,Real.norm_of_nonneg hb.le,
    Real.norm_of_nonneg (pow_nonneg (zero_le_one.trans hk) _)] at H
  simpa only [← mul_assoc,mul_inv_cancel₀ hf.ne',one_mul] using
    mul_le_mul_of_nonneg_left H hf.le

private theorem ceiling {c t : ℝ} (hc : 0<c) (ht : 0<t) (hs : 4*t≤c) :
    let A : ℕ := ⌈c/(4*t)⌉₊
    c/4 ≤ t*(A:ℝ) ∧ t*(A:ℝ)≤ c/2 := by
  let A : ℕ := ⌈c/(4*t)⌉₊
  have l : c/(4*t) ≤ (A:ℝ) := Nat.le_ceil _
  have u : (A:ℝ) < c/(4*t)+1 := Nat.ceil_lt_add_one (by positivity)
  have eq : t*(c/(4*t)) = c/4 := by field_simp
  change c/4 ≤ t*(A:ℝ) ∧ t*(A:ℝ)≤ c/2
  constructor
  · exact eq ▸ mul_le_mul_of_nonneg_left l ht.le
  · have hh := mul_le_mul_of_nonneg_left u.le ht.le
    rw [mul_add,eq,mul_one] at hh
    linarith only [hh,hs]

/-- For the real finite torus used by the family, the lower and upper report
distance gates hold after a single level threshold, uniformly in the physical
mesh inside the specified reporting band. The later period only prevents wrapping
of the one entire compact test. -/
theorem original (C : Family G) (hG : G.Simple) {n : ℕ} {K : Set (Points n)}
    (hK : IsCompact K) (hc : K ⊆ conf n) (B : ℕ) (big : 17 ≤ B) :
    ∃ br : ℕ, 0 < br ∧ ∀ᶠ k : ℕ in atTop,
      ∀ {t : ℝ}, 0<t → Real.log (C.path.levels.clock.hatBeta k)^B ≤ t⁻¹ →
        t⁻¹ ≤ Real.log (C.path.levels.clock.hatBeta k)^(B+1) →
        ∃ dis : ℕ, (C.path.levels.budget k).B^8 ≤ dis ∧
          (dis : ℝ) ≤ C.path.levels.clock.hatBeta k ∧
          ∀ᶠ p : ℕ in atTop, ∀ x ∈ K, ∀ i j : Fin n,
            let u := wrap (C.side k p) ∘ address t x
            separation (u i) (u j) ≤ br*dis ∧ (i≠j → dis ≤ separation (u i) (u j)) := by
  obtain ⟨c,M,hc,hM,places⟩ := WilsonReportCompactSites.original C.S hK hc
  let br : ℕ := ⌈4*M/c⌉₊+1
  have hr : M ≤ (br:ℝ)*(c/4) := by
    have h : 4*M/c ≤ (br:ℝ) := (Nat.le_ceil _).trans (by unfold br; push_cast; linarith)
    linarith only [(div_le_iff₀ hc).mp h]
  refine ⟨br,Nat.succ_pos _,?_⟩
  let L := fun k => Real.log (C.path.levels.clock.hatBeta k)
  have growth : Tendsto L atTop atTop :=
    Real.tendsto_log_atTop.comp (Next.Rank.Station.hat_rate C.path.levels hG)
  filter_upwards [growth.eventually_ge_atTop (max 1 (4*2^8/c)),
    small_log C.path.levels hG (B+1) (f:=c/4+1) (by positivity)] with k admitted expensive
  let l := L k
  have h1 : 1 ≤ l := (le_max_left ..).trans admitted
  have h2 : 4*(2:ℝ)^8 ≤ c*l := by
    have h := (div_le_iff₀ hc).mp ((le_max_right ..).trans admitted)
    change 4*(2:ℝ)^8 ≤ l*c at h
    rwa [mul_comm c l]
  have h0 : 0≤l := zero_le_one.trans h1
  have ha := pow_le_pow_right₀ h1 big
  intro t ht fine coarse
  change l^B ≤ t⁻¹ at fine
  change t⁻¹ ≤ l^(B+1) at coarse
  have f : t*l^B ≤ 1 := by
    simpa only [mul_inv_cancel₀ ht.ne'] using mul_le_mul_of_nonneg_left fine ht.le
  have lb : t*((C.path.levels.budget k).B : ℝ)^8 ≤ c/4 := by
    change t*(⌈l^2⌉₊:ℝ)^8 ≤ c/4
    have up : (⌈l^2⌉₊:ℝ) ≤ 2*l^2 := by
      linarith only [(Nat.ceil_lt_add_one (sq_nonneg l)).le,one_le_pow₀ h1 (n:=2)]
    have cost : (⌈l^2⌉₊:ℝ)^8 ≤ c/4*l^B := calc
      _ ≤ (2*l^2)^8 := pow_le_pow_left₀ (Nat.cast_nonneg _) up _
      _ = 2^8*l^16 := by ring
      _ ≤ c/4*l^17 := by
        rw [pow_succ l 16]
        nlinarith only [mul_le_mul_of_nonneg_right h2 (pow_nonneg h0 16)]
      _ ≤ c/4*l^B := mul_le_mul_of_nonneg_left ha (by positivity)
    calc
      _ ≤ t*(c/4*l^B) := mul_le_mul_of_nonneg_left cost ht.le
      _ = c/4*(t*l^B) := by ring
      _ ≤ c/4 := by simpa only [mul_one] using mul_le_mul_of_nonneg_left f (by positivity : 0≤c/4)
  have groot : 1 ≤ ((C.path.levels.budget k).B:ℝ)^8 := by
    change 1 ≤ (⌈l^2⌉₊:ℝ)^8
    exact one_le_pow₀ ((one_le_pow₀ h1 (n:=2)).trans (Nat.le_ceil _))
  have hs : 4*t ≤ c := by
    linarith only [lb, mul_le_mul_of_nonneg_left groot ht.le]
  let dis : ℕ := ⌈c/(4*t)⌉₊
  have hd := ceiling hc ht hs
  change c/4 ≤ t*(dis:ℝ) ∧ t*(dis:ℝ)≤c/2 at hd
  refine ⟨dis,?_,?_,?_⟩
  · exact_mod_cast (mul_le_mul_iff_right₀ ht).mp (lb.trans hd.1)
  · have u : (dis:ℝ) ≤ c/(4*t)+1 := (Nat.ceil_lt_add_one (by positivity)).le
    calc
      _ ≤ c/4*t⁻¹+1 := u.trans_eq (by rw [div_mul_eq_div_div, div_eq_mul_inv (c/4)])
      _ ≤ (c/4+1)*l^(B+1) := by
        rw [add_mul,one_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left coarse (by positivity)) (one_le_pow₀ h1)
      _ ≤ _ := expensive
  · filter_upwards [places ht hs k] with p hp x hx i j
    obtain ⟨high,low⟩ := hp x hx i j
    have h : (br:ℝ)*(c/4) ≤ t*((br*dis:ℕ):ℝ) := by
      simpa only [Nat.cast_mul,mul_left_comm t (br:ℝ)] using
        mul_le_mul_of_nonneg_left hd.1 (Nat.cast_nonneg br)
    constructor
    · exact_mod_cast (mul_le_mul_iff_right₀ ht).mp (high.trans (hr.trans h))
    · intro hij
      exact_mod_cast (mul_le_mul_iff_right₀ ht).mp (hd.2.trans (low hij))

end YM.Integration.WilsonReportCompactWindow
end

