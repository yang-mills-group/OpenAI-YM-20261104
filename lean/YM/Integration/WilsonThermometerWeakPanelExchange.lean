import YM.Integration.WilsonThermometerWeakPanelBasis
import YM.Integration.WilsonThermometerSmallPanelRead
import YM.Integration.WilsonThermometerIntrinsicRoster

/-! Re-express the entire bare function of the same displaced source in the genuine
smaller panel. Only a finite original angular frame is inverted at the receiving date. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakPanelExchange
open Function Filter Lattice Wilson Labels RG Source Extraction Extra.Histories
open RG05Readout Native Address Many MergeProof Next.Rank Next.Rank.Price
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetField
open WilsonThermometerSmallPanelRead WilsonThermometerOwnOffsetTale
open scoped Classical Topology BigOperators
variable {G:Gauge} (C:Family G)
private theorem small {k N p : ℕ} (built : C.Makes) (late : k ≤ N)
    (monitor : 1 ≤ C.path.levels.clock.monitor k) : shrink C k N p ≤ 2 := by
  let X := C.path.levels.clock.hatBeta k
  let B := C.path.β N p k
  have posX : 0 < X := zero_lt_one.trans (C.path.levels.fits.delayed k)
  have posB : 0 < B := Overlay.beta_positive built.wilson late
  have band : X/2 ≤ B := (built.wilson.represents N p k late).band.1
  have sqrtX : Real.sqrt X ≤ 2*Real.sqrt B := by
    nlinarith [Real.sq_sqrt posX.le,Real.sq_sqrt posB.le,Real.sqrt_nonneg X,Real.sqrt_nonneg B]
  change (Real.sqrt B)⁻¹ / ((Real.sqrt X)⁻¹ * C.path.levels.clock.monitor k) ≤ 2
  have posM : 0 < C.path.levels.clock.monitor k := zero_lt_one.trans_le monitor
  field_simp [(Real.sqrt_pos.2 posB).ne',(Real.sqrt_pos.2 posX).ne',posM.ne']
  nlinarith [mul_nonneg (Real.sqrt_nonneg B) (sub_nonneg.mpr monitor)]


theorem priced {d k N p:ℕ} (built:C.Makes) (late:k≤N) (monitor:1≤C.path.levels.clock.monitor k)
    (b:ℝ) (hb:1≤b) (T:C.label d≃ₗ[ℂ]C.label d) (forward:∀u,(C.labels.level d).coeffSize (T u)≤2*(C.labels.level d).coeffSize u)
    (v:C.label d) : (C.labels.level d).coeffSize (column C d k N p b T.toLinearMap v)≤
      (2*scaleCost C d)*(C.labels.level d).coeffSize v:=by
  let F:=C.labels.level d
  let t:=shrink C k N p
  have tpos:=shrink_pos C built late p
  have tmax:=small C (p:=p) built late monitor
  have positive:0<b:=lt_of_lt_of_le zero_lt_one hb
  have tariff (i : F.Index) :
      ‖column C d k N p b T.toLinearMap v i‖ ≤ (scaleCost C d)*‖T v i‖ := by
    change ‖((b⁻¹:ℝ):ℂ)^(F.grades i).1 * (((t^(F.grades i).2 : ℝ):ℂ) * T v i)‖ ≤ _
    rw [norm_mul,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_inv,abs_of_pos positive,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg tpos.le _),← mul_assoc]
    have first : b⁻¹ ^ (F.grades i).1 ≤ 1 :=
      pow_le_one₀ (inv_nonneg.mpr positive.le) (inv_le_one_of_one_le₀ hb)
    have second : t^(F.grades i).2 ≤ (2:ℝ)^(F.grades i).2 :=
      pow_le_pow_left₀ tpos.le tmax _
    have weight : (2:ℝ)^(F.grades i).2 ≤ scaleCost C d :=
      Finset.single_le_sum (f:=fun j : F.Index => (2:ℝ)^(F.grades j).2)
        (fun _ _ => by positivity) (Finset.mem_univ i)
    exact mul_le_mul_of_nonneg_right
      ((mul_le_mul first second (pow_nonneg tpos.le _) zero_le_one).trans
        (by simpa using weight)) (norm_nonneg _)
  calc
    _ ≤ ∑ i, (scaleCost C d) * ‖T v i‖ := Finset.sum_le_sum (fun i _ => tariff i)
    _ = scaleCost C d * F.coeffSize (T v) := by rw [Labels.Frame.coeffSize,Finset.mul_sum]
    _ ≤ scaleCost C d * (2 * F.coeffSize v) :=
      mul_le_mul_of_nonneg_left (forward v) (Finset.sum_nonneg (fun _ _ => by positivity))
    _ = _ := by ring

def refine {d:ℕ} (h b:ℝ) (T:C.label d≃ₗ[ℂ]C.label d) : Module.End ℂ (C.label d) :=
  T.symm.toLinearMap.comp (((C.labels.level d).scaled h).comp (weightTag C d b))

theorem exact {d k N p:ℕ} (built:C.Makes) (late:k≤N) (b:ℝ) (hb:b≠0)
    (T:C.label d≃ₗ[ℂ]C.label d) (v:C.label d) :
    v=∑ i,(column C d k N p b T.toLinearMap v i)•
      refine C (shrink C k N p)⁻¹ b T (Size.axis (C.labels.level d) i):=by
  let F:=C.labels.level d
  let h:=shrink C k N p
  let w:=column C d k N p b T.toLinearMap v
  have tags:weightTag C d b w=F.scaled h (T v):=by
    funext i
    change (b:ℂ)^_ * (((b⁻¹:ℝ):ℂ)^_*_)=_
    rw [←mul_assoc,←mul_pow,←Complex.ofReal_mul,mul_inv_cancel₀ hb,Complex.ofReal_one,one_pow,one_mul]
    rfl
  have rev:(refine C h⁻¹ b T) w=v:=by
    change T.symm (F.scaled h⁻¹ (weightTag C d b w))=v
    rw [tags]
    have inv:=F.scaled_inv (inv_ne_zero (shrink_pos C built late p).ne') (T v)
    rw [inv_inv] at inv;rw [inv,LinearEquiv.symm_apply_apply]
  let U:=refine C h⁻¹ b T
  have image:U w=∑ i,w i•U (Size.axis F i):=by
    have result:=congrArg U (Size.sum_axes F w)
    simpa only [map_sum,map_smul] using result.symm
  exact rev.symm.trans image

end YM.Integration.WilsonThermometerWeakPanelExchange
end
