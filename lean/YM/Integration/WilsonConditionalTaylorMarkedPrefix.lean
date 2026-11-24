import YM.Integration.WilsonConditionalTaylorFieldBalance

/-! All paid marked normalized Wick coefficients are invariant under the
actual unresolved scalar vacuum and the unpaid input tail. Both numerator
and its own unit denominator are compared before division. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorMarkedPrefix
open Matrix PowerSeries Lattice RG Push.Uniform Wilson Tree Exterior Precision
open PertExtension.Chart MSbar MSbar.Cacao MSbar.Rolling MSbar.Bakery
open FormalBulk08 Series WilsonConditionalTaylorWick WilsonConditionalTaylorFieldBalance
open scoped Classical Matrix
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {m : ℕ}

private theorem reciprocal {a b : PowerSeries ℝ} (same : Through m a b) (ha : coeff 0 a=1) (hb : coeff 0 b=1) :
    Through m (PowerSeries.invOfUnit a 1) (PowerSeries.invOfUnit b 1) :=by
  have one (v : PowerSeries ℝ) (h : coeff 0 v=1) : v*PowerSeries.invOfUnit v 1=1:=
    PowerSeries.mul_invOfUnit _ _ (by rw [←coeff_zero_eq_constantCoeff_apply,h];rfl)
  have h:=((Through.exact_eq (PowerSeries.invOfUnit a 1) m).mul same).mul (Through.exact_eq (PowerSeries.invOfUnit b 1) m)
  rw [mul_comm (PowerSeries.invOfUnit a 1) a,one _ ha,one_mul,mul_assoc,one _ hb,mul_one] at h
  exact fun e he=>(h e he).symm

omit [Fintype J] [DecidableEq J] in
theorem quotientPaid (B : Matrix J I ℝ) (x : J→ℝ) (Q : Matrix I I ℝ) (pos : Q.PosDef)
    {f g T U : PowerSeries (MvPolynomial J ℝ)} (hf : Kind f) (hg : Kind g)
    (old : Through m f g) (row : Through m T U) :
    Through m (quotient B x Q f T) (quotient B x Q g U) :=by
  have exponent :=old.expan_congr hf
  rw [WilsonMovingExponentialConvention.exp f hf,WilsonMovingExponentialConvention.exp g hg] at exponent
  have integral {a b : PowerSeries (MvPolynomial J ℝ)} (h : Through m a b) :
      Through m (contract B x Q a) (contract B x Q b):=beam_through _ (h.map_left _)
  exact (integral (row.mul exponent)).mul (reciprocal (integral exponent)
    (WilsonConditionalTaylorVacuumPrefix.initial B x Q pos f hf)
    (WilsonConditionalTaylorVacuumPrefix.initial B x Q pos g hg))

variable {G : Gauge} {c f : Side} {S : StepData c f}

theorem complete (F : Forest S.ratio) (tag : S.Choices) (O : ChartRatio G)
    {A V : Nesting G f} (hA : Kind A) (hV : Kind V) (income : Fields m A V)
    (P : Matrix (Joint F G) I ℝ) (x : (Joint F G)→ℝ) (Q : Matrix I I ℝ) (pos : Q.PosDef)
    {T U : PowerSeries (MvPolynomial (Joint F G) ℝ)} (paid : Through m T U) :
    Through m (quotient P x Q (barbed F tag O A) T) (quotient P x Q (barbed F tag O V) U) :=by
  obtain ⟨s,low,port⟩:=account income hA hV
  have scalar : PowerSeries.map (rail (taps F G)).toRingHom (WilsonMovingVacuumConstant.scalar (Primary f G) s)
      = WilsonMovingVacuumConstant.scalar (Joint F G) s:=by
    ext1 e
    simp only [WilsonMovingVacuumConstant.scalar,coeff_map]
    exact (rail (taps F G)).commutes _
  have mixed : Through m (barbed F tag O A) (barbed F tag O V + WilsonMovingVacuumConstant.scalar _ s):=by
    unfold barbed
    rw [add_assoc,←scalar,←map_add]
    exact (Through.exact_eq _ m).add (port.map_left _)
  have clean : Kind (barbed F tag O V + WilsonMovingVacuumConstant.scalar _ s):=by
    change coeff 0 (_+_)=0
    rw [map_add,well F tag O V hV,WilsonMovingVacuumConstant.scalar,coeff_map,low,map_zero,add_zero]
  have compare := quotientPaid P x Q pos (well F tag O A hA) clean mixed paid
  rw [WilsonMovingVacuumConstant.invariant P x Q (Matrix.isHermitian_iff_isSymm.mp pos.isHermitian) pos U _ (well F tag O V hV) s low] at compare
  exact compare

end YM.Integration.WilsonConditionalTaylorMarkedPrefix

