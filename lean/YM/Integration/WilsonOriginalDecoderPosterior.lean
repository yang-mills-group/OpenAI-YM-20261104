import YM.Integration.WilsonOriginalDecoderSpring

/-! Compare the positive original Wilson posteriors for a local decoder and
the flat field. Both last-spring normalizations are retained throughout. -/
set_option autoImplicit false
set_option maxHeartbeats 450000
noncomputable section
namespace YM.Integration.WilsonOriginalDecoderPosterior
open Set Filter MeasureTheory Lattice Wilson RG Source Extraction Push.GridApprox OPE OPE.Therm
open PhysicalNext.Repeat.Legato WilsonMacroscopicRichFlatFibre WilsonMacroscopicRichFlatPosteriorLaw
open scoped Classical ENNReal BigOperators
open private YM.Integration.WilsonMacroscopicRichFlatPosteriorLaw.mass from YM.Integration.WilsonMacroscopicRichFlatPosteriorLaw

variable {G:Gauge} (R:Run G) {u k N per:ℕ}

private theorem ordered (c d:ℝ) (V₀ V₁:Config G (R.family.side u per))
    (start:∀U,c*raw R u N per V₀ U≤d*raw R u N per V₁ U)
    (uk:u+1≤k) (W:Config G (R.family.side k per)) :
    c*price R N per uk V₀ W≤d*price R N per uk V₁ W := by
  induction k,uk using Nat.le_induction with
  | base => simpa only [price,likelihood,backTo_self,last,Complex.ofReal_re] using start W
  | succ j uj ih =>
    let S:=R.family.path.levels.clock.op j per
    let β:=R.family.path.β N per (j+1)
    let h (V:Config G (R.family.side u per)) (U:Config G (R.family.side j per)) :=
      (S.density β W U:ℂ)*likelihood R N per uj V U
    have cash (V):Integrable (h V) (prior G _) :=
      (back_slice (R.family.path.levels.transition_mass ..) (enrolled R N per uj V) W).integrableC _
    have step (V):price R N per (Nat.le_succ_of_le uj) V W=(∫U,(h V U).re ∂prior G _) := by
      unfold price likelihood
      rw [backTo_next R.family.path N per uj]
      exact (integral_re (cash V)).symm
    rw [step,step,←integral_const_mul,←integral_const_mul]
    apply integral_mono ((cash V₀).re.const_mul _) ((cash V₁).re.const_mul _)
    intro U
    change c*((S.density β W U:ℂ)*likelihood R N per uj V₀ U).re ≤ d*((S.density β W U:ℂ)*likelihood R N per uj V₁ U).re
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    rw [mul_left_comm c,mul_left_comm d]
    exact mul_le_mul_of_nonneg_left (ih U) (S.density_positive β W U)

local notation "Hist" => R.family.path
local notation "S" => R.family.path.levels.clock.op u per
local notation "β" => R.family.path.β N per (u+1)
local notation "BB" => WilsonOriginalDecoderSpring.bill (S) (β)

theorem density (uk:u+1≤k) (live:k≤N) (V:Config G (R.family.side u per)) (W:Config G (R.family.side k per)) :
    price R N per uk V W/dose (H:=Hist) (p:=per) u V N ≤ (Real.exp (BB V))^2 *
      (price R N per uk 1 W/dose (H:=Hist) (p:=per) u 1 N) := by
  let x:=BB V
  let T:=Real.exp x
  let D:=dose (H:=Hist) (p:=per) u V N
  let D₀:=dose (H:=Hist) (p:=per) u 1 N
  let μ:=scene Hist N per k
  letI:IsProbabilityMeasure μ:=probability (H:=Hist) R.makes.wilson live
  have gate (U:Config G (R.family.side (u+1) per)):=WilsonOriginalDecoderSpring.original (S) (β) U V
  have left (U):Real.exp (-x)*price R N per uk 1 U ≤ price R N per uk V U := by
    simpa only [one_mul] using ordered R (Real.exp (-x)) 1 1 V (fun Z=>by simpa only [one_mul,WilsonMacroscopicRichFlatFibre.raw,x] using (gate Z).1) uk U
  have right : price R N per uk V W ≤ T*price R N per uk 1 W := by
    simpa only [one_mul] using ordered R 1 T V 1 (fun Z=>by simpa only [one_mul,WilsonMacroscopicRichFlatFibre.raw,T,x] using (gate Z).2) uk W
  have payable (V):Integrable (price R N per uk V) μ := ((enrolled R N per uk V).integrableC μ).re
  have base : Real.exp (-x)*D₀ ≤ D := by
    have p:=integral_mono ((payable 1).const_mul (Real.exp (-x))) (payable V) left
    rw [integral_const_mul,YM.Integration.WilsonMacroscopicRichFlatPosteriorLaw.mass R uk live,
      YM.Integration.WilsonMacroscopicRichFlatPosteriorLaw.mass R uk live] at p
    exact p
  have dpos : 0<D := dose_positive (H:=Hist) R.makes.wilson ((Nat.le_succ u).trans (uk.trans live)) V
  have zpos : 0<D₀ := dose_positive (H:=Hist) R.makes.wilson ((Nat.le_succ u).trans (uk.trans live)) 1
  have gain : D₀ ≤ T*D := by
    have h:=mul_le_mul_of_nonneg_left base (Real.exp_pos x).le
    rwa [←mul_assoc,←Real.exp_add,add_neg_cancel,Real.exp_zero,one_mul] at h
  have p0:0≤price R N per uk 1 W:=(positive R N per uk 1 W).1
  change _/D ≤ T^2*(_/D₀)
  rw [←mul_div_assoc,div_le_div_iff₀ dpos zpos]
  calc _ ≤ (T*price R N per uk 1 W)*D₀ := mul_le_mul_of_nonneg_right right zpos.le
       _ ≤ (T*price R N per uk 1 W)*(T*D) := mul_le_mul_of_nonneg_left gain (mul_nonneg (Real.exp_pos x).le p0)
       _ = _ := by ring

private theorem mass_event (uk:u+1≤k) (live:k≤N) (V:Config G (R.family.side u per))
    {E:Set (Config G (R.family.side k per))} (hm:MeasurableSet E) :
    (law R N per uk V).real E = ∫U in E, price R N per uk V U/dose (H:=Hist) (p:=per) u V N ∂scene Hist N per k := by
  let μ:=scene Hist N per k
  letI:IsProbabilityMeasure μ:=probability (H:=Hist) R.makes.wilson live
  have dp:=dose_positive (H:=Hist) (p:=per) R.makes.wilson ((Nat.le_succ u).trans (uk.trans live)) V
  have stock:Integrable (price R N per uk V) μ:=((enrolled R N per uk V).integrableC μ).re
  unfold Measure.real WilsonMacroscopicRichFlatPosteriorLaw.law
  rw [withDensity_apply _ hm,←ofReal_integral_eq_lintegral_ofReal (stock.restrict.div_const _)
      (ae_of_all _ fun U=>div_nonneg (positive R N per uk V U).1 dp.le)]
  apply ENNReal.toReal_ofReal
  exact integral_nonneg (fun U=>div_nonneg (positive R N per uk V U).1 dp.le)

/-- Transfer a positive failed-crown event, with no placement or period
factor from unchanged links, to the normalized decoder posterior. -/
theorem original (uk:u+1≤k) (live:k≤N) (V:Config G (R.family.side u per))
    {E:Set (Config G (R.family.side k per))} (hm:MeasurableSet E) :
    (law R N per uk V).real E ≤ (Real.exp (BB V))^2 * (law R N per uk 1).real E := by
  let μ:=scene Hist N per k
  letI:IsProbabilityMeasure μ:=probability (H:=Hist) R.makes.wilson live
  have stock (V):Integrable (fun U=>price R N per uk V U/dose (H:=Hist) (p:=per) u V N) μ :=
    ((enrolled R N per uk V).integrableC μ).re.div_const _
  rw [mass_event R uk live V hm,mass_event R uk live 1 hm,←integral_const_mul]
  exact integral_mono (stock V).restrict ((stock 1).restrict.const_mul _) (density R uk live V)

end YM.Integration.WilsonOriginalDecoderPosterior
end
