import YM.Integration.WilsonPinnedWidthTransport
import YM.Integration.WilsonTrueProjectedNaturalFee

/-! The physical calendar turns polynomial weak and gross bills for one pinned
field into a subpower exponential-width salary before both regulators. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPinnedWidthCalendar
open Filter Finset Lattice Wilson RG Source Labels Next
open PhysicalNext Repeat Legato Graces Roost WilsonPinnedWidthTransport
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G)
local notation "S" => R.family.S
local notation "V" => R.family.path.levels
local notation "H" => (V).clock.hatBeta
local notation "Λ" => RG16.Lambda (V)

def room (i : ℕ) := 1+Real.log (Λ i)

private theorem log_rise {x y : ℝ} (hx : 1 ≤ x) (xy : x ≤ y) :
    Real.log y - Real.log x ≤ y-x := by
  have xp := zero_lt_one.trans_le hx
  have yp := xp.trans_le xy
  have bound := Real.log_le_sub_one_of_pos (div_pos yp xp)
  rw [Real.log_div yp.ne' xp.ne'] at bound
  apply bound.trans
  rw [show y/x-1=(y-x)/x by field_simp]
  exact div_le_self (sub_nonneg.mpr xy) hx

theorem increase (simple : G.Simple) {i j : ℕ} (ij : i ≤ j) (start : 1 ≤ H i) :
    0 ≤ elapsed S i j ∧ 1 ≤ H j ∧ room R i ≤ room R j ∧
    room R j ≤ room R i+G.slopeConstant*elapsed S i j := by
  have d := blocks S i (j-i)
  rw [show i+(j-i)=j by omega] at d
  have t := (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))).trans d
  have spread : H j - H i = G.slopeConstant*elapsed S i j := by
    change (V).clock.bar+G.slopeConstant*(S).scale j-((V).clock.bar+G.slopeConstant*(S).scale i)=_
    unfold elapsed; ring
  have β := (G.slopeConstant_pos simple).le
  have hj : H i ≤ H j := sub_nonneg.mp (spread ▸ mul_nonneg β t)
  have lo := Real.log_le_log (zero_lt_one.trans_le start) hj
  have rise := log_rise start hj
  have l1 : 1 ≤ Λ i := by change 1 ≤ 2+Real.log (H i); linarith [Real.log_nonneg start]
  have lm : Λ i ≤ Λ j := by change 2+_ ≤ 2+_; linarith only [lo]
  have upper := log_rise l1 lm
  have diff : Λ j-Λ i=Real.log (H j)-Real.log (H i) := by change 2+_- (2+_)=_;ring
  rw [diff] at upper
  unfold room
  exact ⟨t,start.trans hj,add_le_add_right (Real.log_le_log (zero_lt_one.trans_le l1) lm) _,
    by linarith only [upper,rise,spread]⟩

theorem neighbor (simple : G.Simple) (slow : ∀ j, (((S).block j).val : ℝ) ≤ Real.log (Λ j))
    {j : ℕ} (start : 1 ≤ H j) :
    room R (j+1) ≤ (1+G.slopeConstant)*room R j := by
  have step := (increase R simple (j:=j+1) (Nat.le_succ _) start).2.2.2
  have t : elapsed S j (j+1)=Real.log (((S).block j).val : ℝ) := by
    unfold elapsed;rw [Schedule.scale_succ];ring
  have Lpos : 0 < (((S).block j).val : ℝ) := by exact_mod_cast ((S).block j).pos
  have d : elapsed S j (j+1) ≤ room R j := by
    rw [t];unfold room
    linarith only [Real.log_le_self Lpos.le,slow j]
  nlinarith only [step,mul_le_mul_of_nonneg_left d (G.slopeConstant_pos simple).le]

/-- The price is fixed before choosing the finite height, period, or itinerary. -/
theorem subpower (simple : G.Simple) {J η : ℝ} (hJ : 0 ≤ J) (hη : 0 < η) :
    ∀ᶠ i : ℕ in atTop, 1 ≤ H i ∧ J*(1+room R i)^2 ≤ η*Real.log (H i) := by
  have grow := Next.Rank.Station.hat_rate (V) simple
  have logs := Real.tendsto_log_atTop.comp grow
  have field : Tendsto (Λ) atTop atTop := by
    apply tendsto_atTop.2
    intro u
    filter_upwards [logs.eventually_ge_atTop u] with j hj
    change u ≤ 2+Real.log (H j)
    change u ≤ Real.log (H j) at hj
    linarith
  let K := 8*(1+J)
  have hK : 0 < K := by dsimp only [K];positivity
  have small := (Real.isLittleO_pow_log_id_atTop (n:=2)).bound (div_pos hη hK)
  filter_upwards [field.eventually small,field.eventually_ge_atTop (Real.exp 2),
    logs.eventually_ge_atTop 2,grow.eventually_ge_atTop 1] with j paid large hot start
  have lambdaPos : 0 < Λ j := (Real.exp_pos _).trans_le large
  have l2 : 2 ≤ Real.log (Λ j) := (Real.le_log_iff_exp_le lambdaPos).mpr large
  have β : 2 ≤ Real.log (H j) := hot
  have window : Λ j ≤ 2*Real.log (H j) := by change 2+Real.log (H j) ≤ _;linarith
  change ‖(Real.log (Λ j))^2‖ ≤ η/K * ‖Λ j‖ at paid
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),Real.norm_eq_abs,abs_of_nonneg lambdaPos.le] at paid
  rw [div_mul_eq_mul_div] at paid
  have bill := (le_div_iff₀ hK).mp paid
  have compare : (1+room R j)^2 ≤ 4*(Real.log (Λ j))^2 := by
    have bound : 1+room R j ≤ 2*Real.log (Λ j) := by dsimp only [room];linarith
    have pos : 0 ≤ 1+room R j := by dsimp only [room];linarith
    exact (pow_le_pow_left₀ pos bound 2).trans_eq (by ring)
  refine ⟨start,?_⟩
  have half := mul_le_mul_of_nonneg_left window hη.le
  dsimp only [K] at bill
  nlinarith only [mul_le_mul_of_nonneg_left compare hJ,half,bill,sq_nonneg (Real.log (Λ j))]

/-- The full fixed-child field has one marked input with an interpolated
width. Weak prices and the terminal compact field are charged at their actual
dates. No pair of differingly positioned digits is identified. -/
theorem original (simple : G.Simple) (slow : ∀ j, (((S).block j).val : ℝ) ≤ Real.log (Λ j))
    (w : ℕ) {M η : ℝ} (hM : 1 ≤ M) (hη : 0 < η) :
    ∀ᶠ i : ℕ in atTop, ∀ (n : ℕ) (b B A D : ℕ → ℝ), b i ≤ 1 →
      (∀ j, i ≤ j → j ≤ i+n → 0 < b j ∧ (b j)⁻¹ ≤ room R j ∧ 0 < B j ∧
        0 < A j ∧ A j ≤ M*(Λ j)^w) →
      (∀ j, i ≤ j → j < i+n → 0 < D j ∧ D j ≤ M*(Λ j)^w ∧
        B j ≤ (D j*A (j+1))*B (j+1)^(fraction S b j)) →
      B (i+n) ≤ M*(Λ (i+n))^w → B i ≤ (H i)^η := by
  let c := G.slopeConstant
  let E := 1 + 2*Real.log M + 2*(w:ℝ)*(1+c)^2
  let r := Real.exp (-(Real.log 3)/2)
  let J := 16*(1+c)*E/(1-r)
  have hc : 0 ≤ c := (G.slopeConstant_pos simple).le
  have hm : 0 < M := zero_lt_one.trans_le hM
  have m0 := Real.log_nonneg hM
  have he : 0 ≤ E := by dsimp only [E]; positivity
  have hr : 0 < 1-r := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith [Real.log_pos (by norm_num : (1:ℝ)<3)]))
  have hj : 0 ≤ J := by dsimp only [J];positivity
  filter_upwards [subpower R simple hj hη] with i bought
  intro n b B A D cap resources push bare
  let cost (j : ℕ) := 2*Real.log M + 2*(w:ℝ)*room R (j+1)
  have l0 (j : ℕ) (fj : i ≤ j) : 1 ≤ Λ j := by
    have h := (increase R simple fj bought.1).2.1
    change 1 ≤ 2+Real.log (H j);linarith [Real.log_nonneg h]
  have z1 : 1 ≤ room R i := by dsimp only [room];linarith [Real.log_nonneg (l0 i le_rfl)]
  have logWallet (j : ℕ) (fj : i≤j) {price : ℝ} (pos : 0 < price) (fee : price ≤ M*(Λ j)^w) :
      Real.log price ≤ Real.log M+(w:ℝ)*room R j := by
    have l := zero_lt_one.trans_le (l0 j fj)
    have h := Real.log_le_log pos fee
    rw [Real.log_mul hm.ne' (pow_pos l w).ne',Real.log_pow] at h
    unfold room
    nlinarith only [h,(show (0:ℝ) ≤ w from Nat.cast_nonneg w)]
  have envelope (j : ℕ) (fj : i ≤ j) : cost j ≤ E*(1+room R i+elapsed S i j) := by
    have ⟨time,hot,_,grow⟩ := increase R simple fj bought.1
    have near := neighbor R simple slow hot
    have base : room R i+c*elapsed S i j ≤ (1+c)*(1+room R i+elapsed S i j) := by
      nlinarith only [hc,z1,time,mul_nonneg hc (zero_le_one.trans z1)]
    have zpaid := near.trans (mul_le_mul_of_nonneg_left (grow.trans base) (by positivity : 0 ≤ 1+c))
    have space : 1 ≤ 1+room R i+elapsed S i j := by linarith only [z1,time]
    dsimp only [cost,E]
    nlinarith only [mul_le_mul_of_nonneg_left zpaid (show 0 ≤ 2*(w:ℝ) by positivity),
      mul_le_mul_of_nonneg_left space (show 0 ≤ 2*Real.log M by positivity),space]
  have τ := quadratic S b (fun j => Real.log (B j)) cost i n (zero_le_one.trans z1) hc he cap
    (fun j ij jn => (resources j ij jn).1)
    (fun j ij jn => (resources j ij jn).2.1.trans (increase R simple ij bought.1).2.2.2)
    (fun j ij _ => envelope j ij)
  have result := τ (fun j ij jn => by
    have ⟨dp,paid,one⟩ := push j ij jn
    have ⟨_,_,yp,_,_⟩ := resources j ij jn.le
    have ⟨_,_,bn,aa,weak⟩ := resources (j+1) (by omega) (by omega)
    have actual := log_step S b j yp bn (mul_pos dp aa) one
    rw [Real.log_mul dp.ne' aa.ne'] at actual
    have l := logWallet j ij dp paid
    have r' := logWallet (j+1) (by omega) aa weak
    have inc := (increase R simple (i:=j) (j:=j+1) (by omega) (increase R simple ij bought.1).2.1).2.2.1
    dsimp only [cost]
    linarith only [actual,l,r',mul_le_mul_of_nonneg_left inc (Nat.cast_nonneg w)])
    (by
      have last := resources (i+n) (by omega) le_rfl
      have endFee := logWallet (i+n) (by omega) last.2.2.1 bare
      have hot := (increase R simple (i:=i) (j:=i+n) (by omega) bought.1).2.1
      have inc := (increase R simple (i:=i+n) (j:=i+n+1) (by omega) hot).2.2.1
      have zp : 0 ≤ room R (i+n+1) := (zero_le_one.trans z1).trans
        (increase R simple (i:=i) (j:=i+n+1) (by omega) bought.1).2.2.1
      dsimp only [cost]
      nlinarith only [endFee,m0,mul_le_mul_of_nonneg_left inc (Nat.cast_nonneg w),mul_nonneg (Nat.cast_nonneg w) zp])
  have total : Real.log (B i) ≤ J*(1+room R i)^2 := result.trans_eq (by dsimp only [J,r]; ring)
  have bp := (resources i le_rfl (by omega)).2.2.1
  rw [←Real.exp_log bp,Real.rpow_def_of_pos (zero_lt_one.trans_le bought.1)]
  apply Real.exp_le_exp.mpr
  exact (total.trans bought.2).trans_eq (mul_comm _ _)

end YM.Integration.WilsonPinnedWidthCalendar
