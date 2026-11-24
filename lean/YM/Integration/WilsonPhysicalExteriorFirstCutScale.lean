import YM.Integration.WilsonPhysicalExteriorActualSides

/-! The engineering and subtraction-log prices on the original, prespecified
far and ultraviolet stop. Both stops are measured from the same Wilson k. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorFirstCutScale
open Filter Real RG RG16 MS MS.Tide PhysicalNext.Repeat.Legato
open WilsonPhysicalExteriorMeshStops
open scoped Topology

variable {G:Gauge} (R:Run G)
local notation "C₀" => R.family
local notation "Λ₀" => RG16.Lambda R.family.path.levels
local notation "s₀" => R.family.S.scale
local notation "β₀" => R.family.path.levels.clock.hatBeta

/-- The first point on the true far annulus, in units of the held scale. -/
def ratio (c':ℝ) (j:ℕ) : ℝ := exp (s₀ j-s₀ (far C₀ c' j))

private theorem absorb (hG:G.Simple) {a b:ℝ} (hab:a<b) (A δ:ℝ) (hd:0<δ) :
    ∀ᶠ j:ℕ in atTop,A*(Λ₀ j)^a≤δ*(Λ₀ j)^b := by
  have grow:=((tendsto_rpow_atTop (sub_pos.mpr hab)).comp (Literal.lambda_leads C₀ hG)).eventually_ge_atTop (A/δ)
  filter_upwards [grow] with j hj
  have h:=mul_le_mul_of_nonneg_right ((div_le_iff₀ hd).mp hj) (rpow_nonneg (Literal.lambda_pos C₀ j).le a)
  have prod: (Λ₀ j)^(b-a)*(Λ₀ j)^a=(Λ₀ j)^b := by
    rw [← rpow_add (Literal.lambda_pos C₀ j),sub_add_cancel]
  calc
    A*(Λ₀ j)^a≤((Λ₀ j)^(b-a)*δ)*(Λ₀ j)^a := h
    _=δ*((Λ₀ j)^(b-a)*(Λ₀ j)^a) := by ring
    _=δ*(Λ₀ j)^b := by rw [prod]

/-- The original absolute MS subtraction scale grows at most exponentially
in Lambda, with no choice of subtraction point after the first cutoff. -/
theorem shift (hG:G.Simple) (μ:ℝ) :
    ∀ᶠ j:ℕ in atTop,1+|μ+s₀ j|≤exp (2*Λ₀ j) := by
  let b:=G.slopeConstant
  have hb:0<b:=Gauge.slopeConstant_pos hG
  let A:=1+|μ|+(1+|R.family.path.levels.clock.bar|)/b
  have rise: Tendsto (fun j=>exp (Λ₀ j)) atTop atTop:=tendsto_exp_atTop.comp (Literal.lambda_leads C₀ hG)
  filter_upwards [rise.eventually_ge_atTop A,rise.eventually_ge_atTop 1] with j hA h1
  have hβ:0<β₀ j:=zero_lt_one.trans (R.family.path.levels.fits.delayed j)
  have he:β₀ j≤exp (Λ₀ j) := by
    conv_lhs=>rw [←exp_log hβ]
    exact exp_le_exp.mpr (by unfold RG16.Lambda;linarith)
  have bill:s₀ j≤((1+|R.family.path.levels.clock.bar|)/b)*exp (Λ₀ j) := by
    calc
      s₀ j ≤ ((1+|R.family.path.levels.clock.bar|)*exp (Λ₀ j))/b := by
        apply (le_div_iff₀ hb).2
        have eq:β₀ j=R.family.path.levels.clock.bar+b*s₀ j:=rfl
        nlinarith only [he,eq,neg_abs_le R.family.path.levels.clock.bar,
          mul_le_mul_of_nonneg_left h1 (abs_nonneg R.family.path.levels.clock.bar)]
      _ = _ := by ring
  have hs:=abs_add_le μ (s₀ j)
  have hsj : 0 ≤ s₀ j := by simpa only [R.family.S.scale_zero] using (OPE.scale_mono R.family.S).monotone (Nat.zero_le j)
  rw [abs_of_nonneg hsj] at hs
  have B:1+|μ+s₀ j|≤A*exp (Λ₀ j) := by
    dsimp only [A]
    have hn:0≤1+|μ|:=by positivity
    nlinarith only [bill,hs,mul_le_mul_of_nonneg_left h1 hn]
  rw [two_mul,exp_add]
  exact B.trans (mul_le_mul_of_nonneg_right hA (exp_pos _).le)

theorem paid (hG:G.Simple) {c c':ℝ} (hl:1<c) (hfar:c'<c)
    (hs:∀m,((R.family.S.block m).val:ℝ)≤log (Λ₀ m))
    (μ A q:ℝ) (d h:ℕ) :
    ∀ᶠ j:ℕ in atTop,
      (ratio R c' j)^h * (A*(1+|μ+s₀ j|)^d*exp (-mildG*WilsonPhysicalExteriorActualSides.time R c j))
        ≤exp (-q*Λ₀ j) := by
  have ep:0 < mildG/2:=half_pos mild_p
  have h₁:=absorb R hG hl ((2*(d:ℝ)+1)+q) (mildG/2) ep
  have h₂:=absorb R hG hfar (h:ℝ) (mildG/2) ep
  have hp:=far_window C₀ hG hs c'
  have rise: Tendsto (fun j=>exp (Λ₀ j)) atTop atTop:=tendsto_exp_atTop.comp (Literal.lambda_leads C₀ hG)
  filter_upwards [h₁,h₂,hp,shift R hG μ,rise.eventually_ge_atTop A] with j h₁ h₂ hp hμ hAj
  rw [rpow_one] at h₁
  have hz:=WilsonPhysicalExteriorActualSides.time_at_least R c j
  have hf:=mul_le_mul_of_nonneg_left hp.2.2 (Nat.cast_nonneg h : 0≤(h:ℝ))
  have he:=mul_le_mul_of_nonneg_left hz mild_p.le
  have hcost : (h:ℝ)*(s₀ j-s₀ (far C₀ c' j))+Λ₀ j+(d:ℝ)*(2*Λ₀ j)-mildG*WilsonPhysicalExteriorActualSides.time R c j ≤ -q*Λ₀ j := by
    have X:(h:ℝ)*(s₀ j-s₀ (far C₀ c' j))+((2*(d:ℝ)+1)+q)*Λ₀ j ≤
        mildG*WilsonPhysicalExteriorActualSides.time R c j := by
      apply (add_le_add (hf.trans h₂) h₁).trans
      calc
        _=mildG*(Λ₀ j)^c := by ring
        _≤_ := he
    calc
      _ = ((h:ℝ)*(s₀ j-s₀ (far C₀ c' j))+((2*(d:ℝ)+1)+q)*Λ₀ j-
        mildG*WilsonPhysicalExteriorActualSides.time R c j)+(-q)*Λ₀ j := by ring
      _ ≤ 0+(-q)*Λ₀ j := add_le_add (sub_nonpos.mpr X) le_rfl
      _ = _ := zero_add _
  have hd:=pow_le_pow_left₀ (show 0≤1+|μ+s₀ j| by positivity) hμ d
  have bp:=mul_le_mul hAj hd (by positivity) (exp_pos _).le
  unfold ratio
  rw [←exp_nat_mul]
  apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right bp (exp_pos _).le) (exp_pos _).le).trans
  rw [←exp_nat_mul,←exp_add,←exp_add,←exp_add]
  exact exp_le_exp.mpr (by linarith only [hcost])

theorem at_fixed (hG:G.Simple) {c c':ℝ} (hl:1<c) (hfar:c'<c)
    (hs:∀m,((R.family.S.block m).val:ℝ)≤log (Λ₀ m))
    (μ A q:ℝ) (ha:0≤A) (d h:ℕ) :
    ∀ᶠ j:ℕ in atTop,
      (ratio R c' j)^h * (A*(1+|μ|)^d*exp (-mildG*WilsonPhysicalExteriorActualSides.time R c j))
        ≤exp (-q*Λ₀ j) := by
  filter_upwards [paid R hG hl hfar hs μ A q d h,
    R.family.S.divergent.eventually_ge_atTop (2*|μ|)] with j hj hs
  have hw:|μ|≤|μ+s₀ j|:=by linarith only [hs,neg_abs_le μ,le_abs_self (μ+s₀ j)]
  have hd:=pow_le_pow_left₀ (show 0≤1+|μ| by positivity) (add_le_add le_rfl hw) d
  exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hd ha) (exp_pos _).le) (pow_nonneg (exp_pos _).le h)).trans hj

end YM.Integration.WilsonPhysicalExteriorFirstCutScale
end
