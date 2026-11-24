import YM.Integration.WilsonAddressedWeakCellFit
import YM.Next.RANK.Allowance

/-! The real compact pair test fits the reflected chamber on the actual weak calendar. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonAddressedWeakStationRoom
open Filter Set MeasureTheory Metric Lattice Wilson RG Source Cells RG12 Extra.Histories
open Push PhysicalNext.Repeat.Legato WilsonLimitConstruction MergeProof Next.Extract Next.Rank
open OPE Spec OPE.Orbits XSpace XSpace.Normalize Trace Trace.Pilot
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) (simple:G.Simple)
local notation "A!" => R.family.path.levels
set_option quotPrecheck false

include simple

private theorem fine (b δ:ℝ) (positive:0<b) (sep:0<δ) :
    ∀ᶠ k:ℕ in atTop, (32:ℝ)+4*(((A!).budget k).B^2:ℕ) < Station.mag (A!) b k*δ := by
  let z k:=Real.log (Real.log ((A!).clock.hatBeta k))
  have climb : Tendsto z atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp (Station.hat_rate (A!) simple))
  have enough := (Real.tendsto_exp_atTop.comp climb).eventually (eventually_gt_atTop (49/δ))
  filter_upwards [enough,climb.eventually (eventually_ge_atTop (5/b)),
    (Real.tendsto_log_atTop.comp (Station.hat_rate (A!) simple)).eventually (eventually_gt_atTop 0)]
    with k money high logpos
  let e:=Real.exp (z k)
  have ez : 0≤z k := (by positivity : 0≤5/b).trans high
  have one : 1≤e := by simpa [e] using Real.exp_monotone ez
  have value : Real.log ((A!).clock.hatBeta k) = e := (Real.exp_log logpos).symm
  have root : (((A!).budget k).B:ℝ) ≤ e^2+1 := by
    change (⌈(Real.log ((A!).clock.hatBeta k))^2⌉₊:ℝ) ≤ _
    rw [value]
    exact (Nat.ceil_lt_add_one (by positivity)).le
  have two : (((A!).budget k).B:ℝ) ≤ 2*e^2 :=
    root.trans (by nlinarith [sq_nonneg (e-1)])
  have squared : (((A!).budget k).B:ℝ)^2 ≤ (2*e^2)^2 := by gcongr
  have funds : 49<e*δ := (div_lt_iff₀ sep).mp money
  have chart : Real.exp (5*z k) ≤ Station.mag (A!) b k := by
    change _ ≤ (Real.exp ((z k)^2))^b
    rw [←Real.exp_mul]
    have prod := mul_le_mul_of_nonneg_right ((div_le_iff₀ positive).mp high) ez
    exact Real.exp_monotone (by nlinarith only [prod])
  have physical : (32:ℝ)+4*(((A!).budget k).B^2:ℕ) ≤ 48*e^4 := by
    push_cast
    nlinarith only [squared,show 1≤e^4 from one_le_pow₀ one]
  calc
    _ ≤ _ := physical
    _ < (e*δ)*e^4 := mul_lt_mul_of_pos_right (by linarith only [funds]) (by positivity)
    _ = Real.exp (5*z k)*δ := by
      rw [show Real.exp (5*z k) = Real.exp (z k)^5 from Real.exp_nat_mul (z k) 5]
      dsimp only [e]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right chart sep.le

private theorem stationSpan (b M:ℝ) :
    ∀ᶠ k:ℕ in atTop, ∀ _:Station.Allowed (A!) b k, ∀ p:ℕ,
      (4*M+8)*Station.mag (A!) b k ≤
        ((R.family.S.toDepth ((Station.wider (A!) b k).trans (Station.before ..)) p).count.val:ℝ) := by
  have heat : Tendsto ((A!).clock.monitor) atTop atTop := by
    have r := Station.mag_rate (A!) simple (b:=1) (by norm_num)
    change Tendsto (fun k=>(A!).clock.monitor k^(1:ℝ)) atTop atTop at r
    simpa only [Real.rpow_one] using r
  have hot := ((tendsto_pow_atTop (n:=2) (by norm_num)).comp heat).eventually (eventually_ge_atTop (4*M+8))
  filter_upwards [hot] with k hearth
  intro h p
  let a:=Station.width (A!) b k
  let c:=Station.middle (A!) b k
  have ac : a≤c := Station.wider ..
  have ck : c≤k := Station.before ..
  have wid := h.delta p a k le_rfl (ac.trans ck) le_rfl
  have mid := h.scales c k ac ck le_rfl
  rw [wid]
  refine (mul_le_mul_of_nonneg_right hearth (Station.mag_pos (A!) b k).le).trans ?_
  rw [mul_comm]
  refine h.dilation.trans ?_
  rw [mid]
  exact pow_le_pow_right₀ h.large.le (Nat.sub_le_sub_left ac k)

theorem original (φ:Test 2) (b:ℝ) (positive:0<b) :
    ∀ᶠ k:ℕ in atTop, ∀ _:Station.Allowed (A!) b k, ∀ N p:ℕ, k ≤ N →
      let χ := Station.width (A!) b k
      let ρ := Station.gap (A!) b k
      ∃ Q:ℕ,0<ρ ∧ (((A!).budget k).B^2+2*Q <
        (R.family.S.toDepth ((Station.wider (A!) b k).trans (Station.before ..)) p).count.val) ∧
        ∀ x∈tsupport φ,
        (32+4*(((A!).budget k).B^2:ℕ))*(R.family.S.a k/ρ) < dist (x 0) (x 1) ∧
        2*(dist (x 0) (x 1)+32*(R.family.S.a k/ρ)) < (R.family.side k p:ℝ)*(R.family.S.a k/ρ) ∧
        (∀ i,‖x i‖+16*(R.family.S.a k/ρ) ≤ (R.family.S.a k/ρ)*Q) ∧
        (∀ i,ρ*‖x i‖+R.family.S.a N≤R.family.S.a χ/4) := by
  obtain ⟨M,δ,_,sep,_,room⟩ := WilsonAddressedWeakCellFit.original R φ
  filter_upwards [fine R simple b δ positive sep,stationSpan R simple b M] with k small large
  intro h N p live
  exact room ((Station.wider (A!) b k).trans (Station.before ..)) live _ small (large h p)

end YM.Integration.WilsonAddressedWeakStationRoom
