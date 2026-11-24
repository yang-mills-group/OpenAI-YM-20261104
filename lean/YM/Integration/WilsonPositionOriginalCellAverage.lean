import YM.Integration.WilsonPositionCompactEpochSampling

/-! Compare full signed center averages. All children of the submitted compact source
retain their individual continuous positions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalCellAverage
open Filter Set Finset Function Metric MeasureTheory Lattice Maxwell XSpace XSpace.Cirrus XSpace.Normalize
open XSpace.Structure1 FVA2 FVA2.Register MS MS.Land
open WilsonPositionEpochCellTariff WilsonPositionProtectedTuplePrice
open scoped Topology BigOperators Classical
variable {n : ℕ} (m : Mesh) (φ : Test n) (A : m.Tuple (n:=n)→ℂ)

def average : ℂ := (m.vol:ℂ)⁻¹*∫c in m.Box,submitted m φ A c

private theorem measurable_source : Measurable (submitted m φ A) := by
  have room : Continuous (fun c:Four ℝ=>Mesh.room (n:=n) c) := by
    unfold Mesh.room points
    exact (PiLp.continuous_toLp ..).comp (continuous_pi (fun _=>PiLp.continuous_toLp ..))
  have cast : Measurable (fun t:Four ℝ × Points n=>t.2+Mesh.room t.1) :=
    (continuous_snd.add (room.comp continuous_fst)).measurable
  have stair : Measurable (fun t:Four ℝ × Points n=>m.levels t.1 A t.2) := by
    simp only [Mesh.levels,Finset.sum_apply]
    apply Finset.measurable_fun_sum
    intro x _
    let X := (fun t:Four ℝ × Points n=>t.2+Mesh.room t.1) ⁻¹' Extraction.segment m.spacing (m.back x)
    have hx : MeasurableSet X := (Extraction.measurable_segment m.positive _).preimage cast
    exact (measurable_const (a:=A x)).indicator hx
  let F := fun t:Four ℝ × Points n=>φ t.2*m.levels t.1 A t.2
  have hf : Measurable F := (φ.continuous.comp continuous_snd).measurable.mul stair
  exact (hf.stronglyMeasurable.integral_prod_right' (ν:=volume)).measurable

private theorem compare (Y : Sample n → ℂ) {B : ℝ}
    (diff : ∀c∈m.Box, ‖paths m φ Y c - submitted m φ A c‖≤B) :
    ‖Deposit m Y φ-average m φ A‖ ≤ B := by
  let f := paths m φ Y
  let a := submitted m φ A
  have hf : IntegrableOn f m.Box := on_board m φ Y
  have ha : Measurable a := measurable_source m φ A
  have sub : IntegrableOn (f-a) m.Box :=
    (integrableOn_const (C:=B) m.compact_box.measure_ne_top).mono'
      (hf.aestronglyMeasurable.sub ha.aestronglyMeasurable)
      ((ae_restrict_mem m.compact_box.measurableSet).mono diff)
  have ha' : IntegrableOn a m.Box := by
    simpa only [sub_sub_cancel] using hf.sub sub
  rw [homeward,average,←mul_sub]
  change ‖(m.vol:ℂ)⁻¹ * ((∫c in m.Box,f c)-(∫c in m.Box,a c))‖≤B
  rw [←integral_sub hf ha',norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos m.vol_pos]
  have bound := norm_setIntegral_le_of_norm_le_const (μ:=volume) m.compact_box.measure_lt_top diff
  have h := mul_le_mul_of_nonneg_left bound (inv_nonneg.mpr m.vol_pos.le)
  change m.vol⁻¹*‖∫c in m.Box,_‖≤B
  refine h.trans_eq ?_
  change m.vol⁻¹*(B*m.vol) = B
  field_simp [m.vol_pos.ne']

variable {G : Gauge} (Z : WilsonPrescription G) {g : G.Simple}
    {M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {T : Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match Z g M T dial)
    {d : ℕ} (q : ℕ) (v : Tags G d n)

include H in
theorem actual :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ i : ℕ in atTop, ∀ {B} (P : Handoff.Directory Z i B),
      Handoff.Directory.budget G n d + q ≤ B → ∀ (u : ℝ), |u|≤1 →
      ‖(∑ k∈range (q+1),WilsonPositionRawEpoch.row Z P d φ v k*(u:ℂ)^k)-
          average (Z.run.step i) φ (data P d q v (u:ℂ))‖ ≤ C*weight Z q (Z.run.step i)^q*(Z.run.step i).spacing := by
  obtain ⟨C,hC,fees⟩ := WilsonPositionCompactEpochSampling.centers Z H q φ v
  refine ⟨C,hC,?_⟩
  filter_upwards [fees] with i paid B P cap u hu
  let m := Z.run.step i
  let Y (s:Sample n) := ∑ k∈range (q+1),WilsonPositionOriginalEpochQuadrature.point P d v s.layout k*(u:ℂ)^k
  rw [WilsonPositionOriginalEpochQuadrature.whole]
  change ‖Deposit m Y φ - average m φ (data P d q v (u:ℂ))‖≤_
  refine compare m φ _ Y (fun c hc=>?_ )
  rw [stroll]
  exact paid P cap u hu c hc

private theorem spacing (m : Mesh) (hm : m.spacing ≤ 1) {t : ℝ} (ht : 0 ≤ t) (small : t ≤ 1)
    (cost : m.spacing ^ MS.Tide.mildG ≤ t^(q+1)) : m.spacing ≤ t^(q+1)*t := by
  have e := Real.rpow_le_rpow_of_exponent_ge m.positive hm
    (show MS.Tide.mildG*(2:ℝ) ≤ 1 by norm_num [MS.Tide.mildG,MS.High.eps_gain])
  rw [Real.rpow_one,Real.rpow_mul m.positive.le,Real.rpow_two] at e
  calc
    _ ≤ (t^(q+1))^2 := e.trans (pow_le_pow_left₀ (Real.rpow_nonneg m.positive.le _) cost 2)
    _ ≤ t^(q+1)*t := by
      rw [pow_two]
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg ht _)
      rw [pow_succ,mul_comm]
      exact mul_le_of_le_one_right ht (pow_le_one₀ ht small)

include H in
theorem paid (l : Filter ℝ) {t : ℝ → ℝ} (pos : ∀ᶠ r in l, 0<t r) (small : Tendsto t l (𝓝 0))
    (A : ℝ) (b : ℕ) {δ : ℝ} (hd : 0<δ) :
    ∀ᶠ r in l, ∀ i ≥ WilsonPositionAuxiliaryMesh.floor Z.run q (t r), (i:ℝ) ≤ A*(-Real.log (t r))^b →
      ∀ {B} (P : Handoff.Directory Z i B), Handoff.Directory.budget G n d + q ≤ B →
      ∀ (u : ℝ), |u|≤1 → ‖(∑ k∈range (q+1),WilsonPositionRawEpoch.row Z P d φ v k*(u:ℂ)^k)-
        average (Z.run.step i) φ (data P d q v (u:ℂ))‖ ≤ δ*(t r)^(q+1) := by
  obtain ⟨C,hC,rows⟩ := actual φ Z H q v
  let V := C*((q+1:ℕ):ℝ)^q
  have hV : 0≤V := by dsimp [V];positivity
  have hp : 0<1+V := by linarith
  let e := δ/(1+V)
  have he : 0<e := div_pos hd hp
  have hs : V*e ≤ δ := by
    calc _ ≤ (1+V)*e := mul_le_mul_of_nonneg_right (by linarith) he.le
         _ = δ := by dsimp [e];field_simp
  obtain ⟨j,hj⟩ := eventually_atTop.mp (rows.and (H.onSchedule.eventually frontier.smaller))
  have cleared := (WilsonPositionAuxiliaryMesh.grows Z.run q l pos small).eventually_ge_atTop j
  have prices := WilsonPositionBareScalarDiagonal.paid Z H q b A l pos small he
  filter_upwards [pos,small.eventually_lt_const zero_lt_one,cleared,prices] with r positive tiny high price
  intro i low upper B P qualify u unit
  let m := Z.run.step i
  let h := hj i (high.trans low)
  let x := 1+WilsonPositionRawMesh.mass Z m q
  have hx : 0 ≤ x := by
    have h0 : 0≤WilsonPositionRawMesh.mass Z m q := sum_nonneg fun _ _=>abs_nonneg _
    dsimp only [x];linarith
  have taken : x^q * t r ≤ e := by simpa only [abs_of_pos positive] using price i low upper
  have shape := spacing q m h.2 positive.le tiny.le (WilsonPositionAuxiliaryMesh.cost Z.run q positive low)
  refine (h.1 P qualify u unit).trans ?_
  calc
    C * weight Z q m ^ q * m.spacing = (V*x^q)*m.spacing := by dsimp only [weight,V,x];rw [mul_pow];ring
    _ ≤ (V*x^q)*((t r)^(q+1)*t r) := mul_le_mul_of_nonneg_left shape (mul_nonneg hV (pow_nonneg hx _))
    _ = (V*(x^q*t r))*(t r)^(q+1) := by ring
    _ ≤ δ*(t r)^(q+1) := mul_le_mul_of_nonneg_right
      ((mul_le_mul_of_nonneg_left taken hV).trans hs) (pow_nonneg positive.le _)

end YM.Integration.WilsonPositionOriginalCellAverage
