import YM.Integration.ConditionalAffineMeanPrice

/-! Positive physical aperture decay after unscaling the independent original fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ConditionalAffineMeanTariff
open Function Filter Set Lattice Wilson RG Precision Tree Matrix
open Pressure Pressure.Tube Pressure.Stores
open FreeResolvent FreeResolvent.Affine FreeResolvent.TestD FreeResolvent.Lever
open ConditionalTreeCovarianceJets ConditionalTreeCovarianceSums ConditionalCovarianceCutoff
open Next.SectorChange.Rows (slip)
open ConditionalAffineLoadPrices
open scoped Topology BigOperators Classical ContDiff

def panelRate (G : Gauge) (P : Patch) (Pt : Teller G) (n : ℕ) :=
  min (((n+1+1:ℕ):ℝ)*width G P Pt.bind Pt.top.clip (n+1) Pt.top.paths Pt.top.width/120)
    (Pt.top.width/800000)

def rate (G : Gauge) (P : Patch) (Pt : Teller G) (n : ℕ) :=
  min (panelRate G P Pt n) (min (ConditionalAffineSourcePrices.rate Pt P.L/100000) (Pt.top.width/4/100000))/2

lemma rate_pos {G : Gauge} (P : Patch) (Pt : Teller G) (n : ℕ) : 0<rate G P Pt n := by
  have h := (gauged G P Pt.bind Pt.top.clip (n+1) Pt.top.width_pos Pt.top.paths_pos.le).pos
  have ht := Pt.top.width_pos
  have hs := ConditionalAffineSourcePrices.rate_pos Pt P.L
  exact div_pos (lt_min (lt_min (by positivity) (by positivity)) (lt_min (by positivity) (by positivity))) (by norm_num)

lemma unscale (G : Gauge) (L : Side) (n : ℕ) (κ N : ℝ) (hκ : 0<κ) :
    ∀ᶠ x : ℝ in atTop, (max 1 (temp x)⁻¹)^n*(N*fiery G x L) ≤ Real.exp (κ*(radiusB x:ℝ)) := by
  have hf : ∀ᶠ x : ℝ in atTop, N*fiery G x L≤1 := by
    filter_upwards [Work.E01.fiery_le G L N,
      (Work.E01.largeT_tendsto G L).eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with x ha hb
    exact ha.trans hb.le
  filter_upwards [hf,eventually_ge_atTop (1:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop ((n:ℝ)/κ)] with x hF hx hlog
  have h₁ : (temp x)⁻¹≤Real.sqrt x := by
    rw [temp,_root_.mul_inv_rev,inv_inv,←Real.exp_neg]
    exact (mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))) (Real.sqrt_nonneg _)).trans_eq (one_mul _)
  have h₂ : Real.sqrt x≤x := by
    have hh := Real.sq_sqrt (zero_le_one.trans hx)
    have hh' := Real.one_le_sqrt.mpr hx
    nlinarith
  have hp : 0 ≤ max 1 (temp x)⁻¹ := zero_le_one.trans (le_max_left ..)
  have hnat : (n:ℝ)≤Real.log x*κ := (div_le_iff₀ hκ).mp hlog
  have he : (n:ℝ)*Real.log x ≤ κ*(radiusB x:ℝ) := by
    have hh : (Real.log x)^2 ≤ (radiusB x:ℝ) := Nat.le_ceil _
    nlinarith only [mul_le_mul_of_nonneg_right hnat (Real.log_nonneg hx),mul_le_mul_of_nonneg_left hh hκ.le]
  calc
    _ ≤ (max 1 (temp x)⁻¹)^n*1 := mul_le_mul_of_nonneg_left hF (pow_nonneg hp _)
    _ ≤ x^n := by rw [mul_one]; exact pow_le_pow_left₀ hp (max_le hx (h₁.trans h₂)) n
    _ = Real.exp ((n:ℝ)*Real.log x) := by rw [Real.exp_nat_mul,Real.exp_log (zero_lt_one.trans_le hx)]
    _ ≤ _ := Real.exp_monotone he

def wFee (G : Gauge) (P : Patch) (Pt : Teller G) (n : ℕ) :=
  |windowPrice G P Pt.bind Pt.top.clip (n+1) Pt.top.paths Pt.top.width 0 0+
    diminish G P Pt.bind Pt.top.clip (n+1) 0 Pt.top.paths Pt.top.width 0|

def invFee (G : Gauge) (P : Patch) (Pt : Teller G) (n : ℕ) :=
  |earnings G P Pt.bind Pt.top.clip (n+1) Pt.top.paths Pt.top.width|+1

def jTail (G : Gauge) (P : Patch) (Pt : Teller G) (n : ℕ) :=
  (max 0 ((Fintype.card Signed:ℝ)*|slip| *phasePrice G P Pt.bind n Pt.top.paths Pt.top.width))*
    Real.exp (Pt.top.width/4)

def coefficient (G : Gauge) (P : Patch) (Pt : Teller G) (n : ℕ) (D D' : ℝ) :=
  let J := jacFee G P Pt n
  let L := 1+|slip| *D
  let L' := |slip| *D'*Real.exp (ConditionalAffineSourcePrices.rate Pt P.L)
  wFee G P Pt n*(2^n*((L+L')*J))+
    invFee G P Pt n*(2^n*(L'*J)+2^n*(L*jTail G P Pt n))

/-- The exact two scalar tariffs of the changed mean have a common exponential
window price. The material supplies its ordered-panel bound independently. -/
theorem shield (G : Gauge) (P : Patch) (Pt : Teller G) (n : ℕ) {N D D' : ℝ}
    (hN : 0≤N) (hD : 0≤D) (hD' : 0≤D') : ∀ᶠ x : ℝ in atTop, ∀ w : ℝ, 0≤w →
    w≤wFee G P Pt n*Real.exp (-panelRate G P Pt n*(radiusB x:ℝ)) →
    w*ordinaryFee G P Pt n N D D' x+invFee G P Pt n*tailFee G P Pt n N D D' x ≤
      coefficient G P Pt n D D'*Real.exp (-rate G P Pt n*(radiusB x:ℝ)) := by
  let κ := rate G P Pt n
  have hk : 0<κ := rate_pos P Pt n
  let ρ := ConditionalAffineSourcePrices.rate Pt P.L
  have hρ : 0<ρ := ConditionalAffineSourcePrices.rate_pos Pt P.L
  let b := Pt.top.width/4
  have hb : 0<b := div_pos Pt.top.width_pos (by norm_num)
  have rates : 2*κ≤panelRate G P Pt n ∧ 2*κ≤ρ/100000 ∧ 2*κ≤b/100000 := by
    dsimp only [κ,rate,b,ρ]
    have cancel (y : ℝ) : 2*(y/2)=y := by ring
    rw [cancel]
    exact ⟨min_le_left ..,(min_le_right ..).trans (min_le_left ..),(min_le_right ..).trans (min_le_right ..)⟩
  filter_upwards [unscale G P.L n κ N hk] with x hx
  intro w hw hwin
  let R := (radiusB x:ℝ)
  let t := Real.exp (-κ*R)
  let Z := Real.exp (κ*R)
  have ht : 0<t := Real.exp_pos _
  have hZ : 1≤Z := Real.one_le_exp_iff.mpr (mul_nonneg hk.le (Nat.cast_nonneg _))
  have ht1 : t≤1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hk.le) (Nat.cast_nonneg _))
  have hZt : Z*t=1 := by dsimp only [Z,t]; rw [←Real.exp_add]; ring_nf; exact Real.exp_zero
  have hdis {η : ℝ} (hη : 2*κ≤η) : Real.exp (-η*R)≤t*t := by
    rw [show t*t=Real.exp (-(2*κ)*R) by dsimp only [t]; rw [←Real.exp_add]; congr 1; ring]
    exact Real.exp_monotone (mul_le_mul_of_nonneg_right (neg_le_neg hη) (Nat.cast_nonneg _))
  let J := jacFee G P Pt n
  let L := 1+|slip| *D
  let L' := |slip| *D'*Real.exp ρ
  let J' := jTail G P Pt n
  have hJ : 0≤J := le_max_left ..
  have hL : 0≤L := by dsimp [L]; positivity
  have hL' : 0≤L' := by dsimp [L']; positivity
  have hJ' : 0≤J' := by dsimp [J',jTail]; positivity
  have hFee : 0≤wFee G P Pt n := abs_nonneg _
  have hinv : 0 ≤ invFee G P Pt n := by dsimp [invFee]; positivity
  have ht2 : t*t≤t := (mul_le_mul_of_nonneg_left ht1 ht.le).trans_eq (mul_one _)
  have hh : w≤wFee G P Pt n*(t*t) := hwin.trans (mul_le_mul_of_nonneg_left (hdis rates.1) hFee)
  have disc (η : ℝ) (hη : 0≤η) (h : 2*κ≤η/100000) :
      Real.exp (-η*(till x:ℝ))≤Real.exp η*(t*t) :=
    (ConditionalAffineSourcePrices.aperture η hη (radiusB x)).trans (mul_le_mul_of_nonneg_left (hdis h) (Real.exp_pos _).le)
  have hff : fullFee G P.L n N D ρ x≤L*Z := by
    have hE : Real.exp (-ρ*(till x:ℝ))≤Z :=
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hρ.le) (Nat.cast_nonneg _))).trans hZ
    exact (add_le_add hx (mul_le_mul_of_nonneg_left hE (mul_nonneg (abs_nonneg _) hD))).trans_eq (by dsimp [L]; ring)
  have hsf : sourceFee D' ρ x≤L'*(t*t) :=
    (mul_le_mul_of_nonneg_left (disc ρ hρ.le rates.2.1) (mul_nonneg (abs_nonneg _) hD')).trans_eq (by dsimp [L']; ring)
  have hjf : jacTail G P Pt n x≤J'*(t*t) :=
    (mul_le_mul_of_nonneg_left (disc b hb.le rates.2.2) (le_max_left 0 _)).trans_eq (by dsimp [J',jTail,b]; ring)
  have haf : ordinaryFee G P Pt n N D D' x ≤ (2^n*((L+L')*J))*Z := by
    have hs := hsf.trans (mul_le_mul_of_nonneg_left (ht2.trans (ht1.trans hZ)) hL')
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (add_le_add hff hs) hJ) (by positivity)).trans_eq (by ring)
  have htf : tailFee G P Pt n N D D' x ≤ (2^n*(L'*J)+2^n*(L*J'))*t := by
    have htail0 : 0≤jacTail G P Pt n x := by unfold jacTail; positivity
    have h₁ := mul_le_mul_of_nonneg_right (hsf.trans (mul_le_mul_of_nonneg_left ht2 hL')) hJ
    have h₂ := mul_le_mul hff hjf htail0 (mul_nonneg hL (zero_le_one.trans hZ))
    have hc : (L*Z)*(J'*(t*t))=L*J'*t := by calc
      _ = (L*J'*t)*(Z*t) := by ring
      _ = _ := by rw [hZt,mul_one]
    exact (add_le_add (mul_le_mul_of_nonneg_left h₁ (by positivity))
      (mul_le_mul_of_nonneg_left (h₂.trans_eq hc) (by positivity))).trans_eq (by ring)
  have h₁ := mul_le_mul hh haf (by unfold ordinaryFee fullFee sourceFee jacFee fiery temp; positivity)
    (mul_nonneg hFee (mul_nonneg ht.le ht.le))
  have h₂ := mul_le_mul_of_nonneg_left htf hinv
  apply (add_le_add h₁ h₂).trans_eq
  have hz : t*t*Z=t := by calc
    _ = t*(Z*t) := by ring
    _ = _ := by rw [hZt,mul_one]
  calc
    _ = (wFee G P Pt n*(2^n*((L+L')*J)))*(t*t*Z)+
        (invFee G P Pt n*(2^n*(L'*J)+2^n*(L*J')))*t := by ring
    _ = _ := by rw [hz]; dsimp only [coefficient,J,L,L',J',ρ,t,κ,R]; ring

end YM.Integration.ConditionalAffineMeanTariff
