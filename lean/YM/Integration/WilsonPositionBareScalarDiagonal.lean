import YM.Integration.WilsonPositionBareDetectorGrowth

/-! The independent bare thermometer is controlled at every fixed order throughout the
polylogarithmic auxiliary cutoff window. The cutoff inside this window can be selected
before either physical regulator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionBareScalarDiagonal
open Filter Set Maxwell XSpace XSpace.Cirrus FVA2 FVA2.Register FVA2.Scale MS MS.Land
open scoped Topology BigOperators Classical Polynomial
variable {G : Gauge} (Z : WilsonPrescription G) {g : G.Simple}
    {M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {σ : Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match Z g M σ dial)

private theorem runs {l : Filter ℝ} {t : ℝ→ℝ} (pos : ∀ᶠ r in l,0<t r)
    (small : Tendsto t l (𝓝 0)) : Tendsto (fun r=>-Real.log (t r)) l atTop :=
  tendsto_neg_atTop_iff.mpr (Real.tendsto_log_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr ⟨small,pos⟩))

/-- The original lower bound on the auxiliary date itself fits a logarithmic window. -/
theorem feasible (q : ℕ) (l : Filter ℝ) {t : ℝ→ℝ}
    (pos : ∀ᶠ r in l,0<t r) (small : Tendsto t l (𝓝 0)) :
    ∃ C>0,∀ᶠ r in l, (WilsonPositionAuxiliaryMesh.floor Z.run q (t r):ℝ) ≤ C*(-Real.log (t r)) := by
  have hl : 1<(Z.run.ratio:ℝ) := by exact_mod_cast (show 1<Z.run.ratio from (by decide : 1<3).trans_le Z.run.large)
  let a := ((q+1:ℕ):ℝ)/(Tide.mildG*Real.log Z.run.ratio)
  have ha : 0<a := div_pos (by positivity) (mul_pos Tide.mild_p (Real.log_pos hl))
  refine ⟨a+1,by positivity,?_⟩
  filter_upwards [(runs pos small).eventually_ge_atTop 1] with r hr
  have h := Nat.ceil_lt_add_one (show 0≤a*(-Real.log (t r)) from mul_nonneg ha.le (by linarith))
  unfold WilsonPositionAuxiliaryMesh.floor
  rw [show -((q+1:ℕ):ℝ)*Real.log (t r)/(Tide.mildG*Real.log Z.run.ratio)=a*(-Real.log (t r)) by
    dsimp only [a];ring]
  nlinarith only [h,hr]

include H in
theorem paid (q d : ℕ) (C : ℝ) (l : Filter ℝ) {t : ℝ→ℝ}
    (pos : ∀ᶠ r in l,0<t r) (small : Tendsto t l (𝓝 0)) {δ : ℝ} (hd : 0<δ) :
    ∀ᶠ r in l, ∀ i ≥ WilsonPositionAuxiliaryMesh.floor Z.run q (t r),
      (i:ℝ) ≤ C*(-Real.log (t r))^d →
      (1+WilsonPositionRawMesh.mass Z (Z.run.step i) q)^q*|t r| ≤ δ := by
  obtain ⟨p,hp⟩ := WilsonPositionBareDetectorGrowth.mass Z H q
  let b : ℝ[X] := (1+p)^q
  have deg : b.degree ≤ ((Polynomial.X:ℝ[X])^b.natDegree).degree := by
    rw [Polynomial.degree_X_pow];exact Polynomial.degree_le_natDegree
  obtain ⟨B,hB,h⟩ := (b.isBigO_atTop_of_degree_le _ deg).exists_pos
  have nat := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually h.bound
  have lim : ∀ᶠ i:ℕ in atTop,
      (1+WilsonPositionRawMesh.mass Z (Z.run.step i) q)^q ≤ B*(i:ℝ)^b.natDegree := by
    filter_upwards [nat,hp] with i y x
    have nonneg : 0≤WilsonPositionRawMesh.mass Z (Z.run.step i) q := by
      unfold WilsonPositionRawMesh.mass; positivity
    calc
      _ ≤ (1+p.eval (i:ℝ))^q := pow_le_pow_left₀ (by linarith) (by linarith) q
      _ = b.eval (i:ℝ) := by simp [b]
      _ ≤ ‖b.eval (i:ℝ)‖ := Real.le_norm_self _
      _ ≤ B*(i:ℝ)^b.natDegree := by simpa using y
  obtain ⟨j,hj⟩ := eventually_atTop.mp lim
  let D := d*b.natDegree
  have van : Tendsto (fun x:ℝ=>x^D*Real.exp (-x)) atTop (𝓝 0) := by
    simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (D:ℝ) 1 zero_lt_one
  have curve : Tendsto (fun r=>B*C^b.natDegree*((-Real.log (t r))^D*Real.exp (-(-Real.log (t r))))) l (𝓝 0) := by
    simpa using (van.comp (runs pos small)).const_mul (B*C^b.natDegree)
  have floors := (WilsonPositionAuxiliaryMesh.grows Z.run q l pos small).eventually_ge_atTop j
  filter_upwards [floors,pos,curve.eventually_lt_const hd] with r index hr low i large short
  rw [abs_of_pos hr]
  rw [neg_neg,Real.exp_log hr] at low
  calc
    _ ≤ (B*(i:ℝ)^b.natDegree)*t r := by gcongr; exact hj i (index.trans large)
    _ ≤ (B*(C*(-Real.log (t r))^d)^b.natDegree)*t r := by gcongr
    _ = B*C^b.natDegree*((-Real.log (t r))^D*t r) := by rw [mul_pow,←pow_mul];ring
    _ ≤ δ := low.le

include H in
theorem at_floor (q : ℕ) (l : Filter ℝ) {t : ℝ→ℝ} (pos : ∀ᶠ r in l,0<t r)
    (small : Tendsto t l (𝓝 0)) {δ : ℝ} (hd : 0<δ) :
    ∀ᶠ r in l,(1+WilsonPositionRawMesh.mass Z (Z.run.step (WilsonPositionAuxiliaryMesh.floor Z.run q (t r))) q)^q
      *|t r|≤δ := by
  obtain ⟨C,_,window⟩ := feasible Z q l pos small
  filter_upwards [window,paid Z H q 1 C l pos small hd] with r h price
  exact price _ le_rfl (by simpa using h)

end YM.Integration.WilsonPositionBareScalarDiagonal
