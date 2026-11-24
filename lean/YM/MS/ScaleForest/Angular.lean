import YM.MS.ScaleForest.OpenTensor
/-!
# Both angular log moments at the regulated scale

Compute the Taylor power at q, with external legs kept open. This is the
calculation at one log derivative with ordered scales on the two lines, one
use of each half-kernel. Includes `(4π)^-2` in this normalization. Use
as a building block in the two-line integrals (`RoseValue`,
`LongPrice`/`TTPrice`).
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest.SquareShift
open Function Filter Set Finset MeasureTheory Metric
open MS Plane Koszul Heat Flux Landau Tone Momentum Real Frame Wire Color Detect Native
open Complex (I)
open WilsonMS.BetaValue WilsonMS.BetaValue.HeatPapers
open scoped Topology ContDiff BigOperators ENNReal

variable (q p : QP) (i j : Axis) (a b x t : ℝ)

abbrev secondScale (t : ℝ) := t^3 * (6*(ν t)^2-40*ν t+40)/(4*(ν t)^6)

def logArea : ℝ := ((4*Real.pi)^2)⁻¹

theorem heat_smooth (Q p r d : ℝ) : ContDiff ℝ ∞ (fun x : ℝ × ℝ => heatValue Q p r d x.2 x.1) := by
  unfold heatValue pairValue squareValue firstValue gaussS ν slope volume4
  unfold ν
  fun_prop (disch:= intros; positivity)

theorem sample_sextic (p a b c d : ℝ) :
    iteratedDeriv 2 (fun x : ℝ=> exp (p*x^2)*(a+b*x^2+c*x^4+d*x^6)) 0 = 2*(b+p*a) := by
  let H (x : ℝ):= exp (p*x^2); let F (x:ℝ) := a+b*x^2+c*x^4+d*x^6
  let U (x:ℝ) := 2*b*x+4*c*x^3+6*d*x^5; let V (x:ℝ):=2*p*x
  have hE (x:ℝ) : HasDerivAt H (V x * H x) x := by
    unfold H V; convert (config := {transparency := .default}) ((hasDerivAt_pow 2 x |>.const_mul _).exp) using 1; norm_num; ring
  have hF (x:ℝ) : HasDerivAt F (U x) x := by
    unfold F U; convert (config := {transparency := .default}) ((((hasDerivAt_pow 2 x |>.const_mul b).const_add a).add
      ((hasDerivAt_pow 4 x).const_mul c)).add ((hasDerivAt_pow 6 x).const_mul d)) using 1 <;> first | rfl |  (norm_num; ring)
  have hD (x:ℝ) : HasDerivAt (H*F) ((V x * H x) * F x + H x * U x) x := (hE x).mul (hF x)
  change iteratedDeriv (1+1) (H*F) 0 = _
  rw [iteratedDeriv_succ',funext (fun x=>(hD x).deriv),iteratedDeriv_one]; apply HasDerivAt.deriv
  have hU : HasDerivAt U (2*b) 0 := by
    unfold U; convert (config := {transparency := .default}) ((( (hasDerivAt_id' 0).const_mul (2*b)).add ((hasDerivAt_pow 3 0).const_mul (4*c))).add
      ((hasDerivAt_pow 5 0).const_mul (6*d))) using 1 <;> first | rfl |  norm_num
  have hV : HasDerivAt V (2*p) 0 := by convert (config := {transparency := .default}) (hasDerivAt_id' 0).const_mul (2*p) using 1 <;> first | rfl |  simp
  convert (config := {transparency := .default}) (((hV.mul (hE 0)).mul (hF 0)).add ((hE 0).mul hU)) using 1 <;> first | rfl |  (simp [H,V,F,U]; ring)

-- Keep t arbitrary; no exchanging Taylor with a sharp momentum cut.
theorem second_heat (Q p r d t : ℝ) : iteratedDeriv 2 (fun x : ℝ => heatValue Q p r d x t) 0 =
    2*(d*Q+2*p*r)*logArea*secondScale t := by
  let u:=ν t; let s' := gaussS u
  let A:= slope t; let B:=A+1; let C:= t^3*volume4 t
  let S2:=4*(A^2+B^2+A*B)*s'*Q; let S4:=(A*B)^2*Q^2
  let a := C*(48*s'^3*d)
  let b := C*(s'*d*S2 + s'^2*(2*(A^2+B^2)*Q*d+8*A*B*p*r) + p*r*(12*(A+B)^2*s'^2+A*B*(24*s'^2)))
  let c := C*(s'*d*S4+p*r*(2*A*B*(A+B)^2*s'*Q+A*B*S2))
  let e := C*(p*r*(A*B*S4))
  rw [show (fun x : ℝ=> heatValue Q p r d x t)=
      (fun x : ℝ => exp ((A*Q)*x^2)*(a+b*x^2+c*x^4+e*x^6)) from ?_, sample_sextic]
  · unfold b a C S2 B A s' u logArea secondScale volume4 gaussS slope ν; field_simp; ring
  funext x
  have he (s A B : ℝ) : pairValue Q p r d s (A*x) (B*x)=
      (48*s^3*d) + (s*d*(4*(A^2+B^2+A*B)*s*Q) + s^2*(2*(A^2+B^2)*Q*d+8*A*B*p*r) + p*r*(12*(A+B)^2*s^2+A*B*(24*s^2)))*x^2 +
        (s*d*((A*B)^2*Q^2)+p*r*(2*A*B*(A+B)^2*s*Q+A*B*(4*(A^2+B^2+A*B)*s*Q)))*x^4 +
          p*r*(A*B*((A*B)^2*Q^2))*x^6 := by
    unfold pairValue squareValue firstValue; ring
  unfold heatValue
  rw [he]; change _ * exp _ * _ * _ = _
  unfold a b c e S2 S4 B A s' u C; rw [mul_right_comm (slope t)]; ring

theorem seconds : (∫ t in (0:ℝ)..1, secondScale t) = -(1/48:ℝ) := by
  let H (t:ℝ) := (1/8:ℝ)*(-(3/(ν t)^2)+46/(3*(ν t)^3)-20/(ν t)^4+8/(ν t)^5)
  have he (t:ℝ) : HasDerivAt H (secondScale t) t := by
    have hh (t:ℝ) : HasDerivAt ν (2*t) t := by convert (config := {transparency := .default}) (hasDerivAt_pow 2 t).const_add 1 using 1 <;> first | rfl |  norm_num
    unfold H
    obtain hp := ν_pos t
    have hx (k:ℝ)(a:ℕ) : HasDerivAt (fun t => k/(ν t)^a) (-k*((a:ℝ)*(ν t)^(a-1)*(2*t))/((ν t)^a)^2) t := by
      convert (config:={transparency:=.default}) (hasDerivAt_const t k).div ((hh t).pow a) (show (ν ^ a) t ≠ 0 from pow_ne_zero a hp.ne') using 1 <;> first | rfl |  simp [Pi.pow_apply]

    have ht : HasDerivAt (fun t => 46/(3*(ν t)^3)) _ t := ((hasDerivAt_const t (46:ℝ)).div (((hh t).pow 3).const_mul 3) ?_)
    swap
    · change 3*(ν t)^3≠0; positivity
    convert (config:={transparency:= .default}) ((((((hx 3 2).neg).add ht).sub (hx 20 4)).add (hx 8 5)).const_mul (1/8)) using 1 <;> try rfl
    unfold secondScale; norm_num; unfold ν; field_simp; ring
  have hc : Continuous secondScale := by unfold secondScale ν; fun_prop (disch:= intros; positivity)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _=> he t) (hc.intervalIntegrable ..)]
  norm_num [H,ν]

abbrev momentTensor (q : QP) (i j : Axis) := ∫ t in (0:ℝ)..1, tune q (tensorPol q i j) t

theorem payment_line : momentTensor (x•q) i j =∫ t in (0:ℝ)..1, heatValue q.sq (q i) (q j) (kk i j) x t := by
  unfold momentTensor; simp_rw [two_rank]

lemma cour1 : Heat.Cour mint :=
   ⟨Set.Icc 0 1,isCompact_Icc,(show ∀ᵐ t ∂mint,t ∈ Set.Ioc 0 1 from ae_restrict_mem measurableSet_Ioc).mono
      (fun _ hi => Ioc_subset_Icc_self hi)⟩

theorem moment_smooth : ContDiff ℝ ∞ (fun x : ℝ=> momentTensor (x•q) i j) := by
  simp_rw [payment_line,intervalIntegral.integral_of_le zero_le_one]; exact
    (Heat.Lot mint cour1 (heat_smooth ..)).contDiff

def angularMoment (q : QP) (i j : Axis) := logArea * (kk i j * q.sq +2*q i*q j)

theorem angular_average : iteratedDeriv 2 (fun x : ℝ => momentTensor (x•q) i j) 0 = -angularMoment q i j/24 := by
  have he (F : ℝ×ℝ→ℝ) (hF : ContDiff ℝ ∞ F) : iteratedDeriv 2 (fun x=> ∫ t in (0:ℝ)..1,F (t,x)) 0 =
      ∫ t in (0:ℝ)..1, iteratedDeriv 2 (fun x => F (t,x)) 0 := by
    let h := Heat.Lot mint cour1 hF
    simp only [iteratedDeriv,intervalIntegral.integral_of_le zero_le_one]
    rw [show iteratedFDeriv ℝ 2 (fun x=> ∫ t in Set.Ioc 0 1,F (t,x)) 0=_ from
        (show _ from congr_fun (h.identity 2) 0),ContinuousMultilinearMap.integral_apply (h.integ 2 0)]
  rw [funext (fun x=> payment_line q i j x)]
  obtain ht:= he _ (heat_smooth q.sq (q i) (q j) (kk i j))
  dsimp only at ht
  rw [ht]; simp_rw [second_heat,intervalIntegral.integral_const_mul,seconds]; unfold angularMoment; ring

def twin (q : QP) (i j : Axis) (t : ℝ) (p : QP) := ((Pill t q p * tensorPol q i j p:ℝ):ℂ)

def evenTwin (q : QP) (i j : Axis) (t : ℝ) (p : QP) := twin q i j t p+twin q i j t (-p)

/-- Both signs of loop momentum. Keep the factor two. -/
theorem from_integral : (∫ p, (∫ t in (0:ℝ)..1, evenTwin q i j t p) ∂mplane)= 2 * (momentTensor q i j:ℂ) ∧
    Integrable (fun p=>∫ t in (0:ℝ)..1, evenTwin q i j t p) mplane := by
  have he : HeatPapers.Sheet (tensorPol q i j) :=
    (((HeatPapers.Sheet.heat_sq.mul (HeatPapers.Sheet.heat_sq.wave q)).mul ((HeatPapers.Sheet.read i).wave q)).mul
      (HeatPapers.Sheet.read j))
  exact (mul_one (2:ℂ) ▸ (paymentμ q (tensorPol q i j) he (twin q i j) 1 (fun _ _ => (one_mul _).symm)))
end YM.MS.ScaleForest.SquareShift
