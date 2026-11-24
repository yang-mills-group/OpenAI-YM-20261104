import YM.Integration.WilsonVacuumPreResetDepositedIntegrand
import YM.Integration.OriginalFiniteWickReadout

/-! The genuine finite conditional vacuum at every finite order.  All
letters use the same retained forest and its original Wick covariance. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetDepositedMass
open Function Finset Marker Multi Comparison.RG02 Order Cumulants PowerSeries
open Next.Rank Valence FreeResolvent Lattice Wilson RG Precision Tree Matrix Exterior PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedRay
open WilsonVacuumPreResetDepositedGeometric WilsonVacuumPreResetDepositedLetters
open WilsonVacuumPreResetFiniteRegister WilsonVacuumPreResetDepositedIntegrand
open scoped Classical BigOperators Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner

variable {G:Gauge}(R:Run G)(N m p:ℕ)(hm:m<N)(F:Forest (step R m p).ratio)
variable (tag:(step R m p).Choices)(Z:SeriesA G)
variable {T:Type}[DecidableEq T][Fintype T]{J:Census T}(Q:Bulk.Colors J G (fine R m p))
variable (cash:BudgetPoint)(cap:ℕ){σ C:ℝ}(width:0<σ)(draw:Draw Z σ C)
    (low:∀a∈Z,3≤a.grade)(high:∀a∈Z,a.grade≤cap)
    (x:fieldDir G (coarse R m p) 1)(r:ℕ)

def mass:=Wick (Woods G (coarse R m p)) ((model R N m p hm).covariance F tag)
  (raiseE (opened R N m p hm F Z))

private theorem scaled {I Y:Type}[Fintype I][DecidableEq I][Fintype Y]
    (B:Y→ℝ)(q:Matrix I I ℝ)(h:q.IsSymm)(P:Ink (I⊕Y))(j:ℕ)(A:Normal.poly I)
    (c:ℂ)(hc:c≠0)(hp:∀z:I→ℝ,Cloud.paint z A=c*(MvPolynomial.eval (Sum.elim z B) (coeff j P):ℝ)):
    Cloud.wick q h 0 A=c*(MvPolynomial.eval B (coeff j (Wick Y q P)):ℝ):=by
  have law (z:I→ℝ):Cloud.paint z (c⁻¹ • A)=(MvPolynomial.eval (Sum.elim z B) (coeff j P):ℝ):=by
    rw [map_smul,smul_eq_mul,hp,inv_mul_cancel_left₀ hc]
  have w:=OriginalFiniteWickReadout.painted B q h P j (c⁻¹ • A) law
  rw [map_smul,smul_eq_mul] at w
  have hh:=congrArg (fun a:ℂ=>c*a) w
  simpa only [←mul_assoc,mul_inv_cancel₀ hc,one_mul] using hh

private theorem observed {Y:Type}(B:Y→ℝ)(P:Ink Y)(j:ℕ):
    coeff j (OriginalRadialSeries.observed B P)=MvPolynomial.eval B (coeff j P):=rfl

private theorem table {I Y:Type}[Fintype I][DecidableEq I][Fintype Y](r:ℕ)
    (B:Y→ℝ)(q:Matrix I I ℝ)(h:q.IsSymm)(P:Ink (I⊕Y))(f:Hot (Board J r)→Normal.poly I)
    (law:∀(u:Index r)(z:I→ℝ),Cloud.paint z (Cloud.integrand f (Join.pair J.quiet u))=
      (u.val.card.factorial:ℂ)*(MvPolynomial.eval (Sum.elim z B) (coeff u.val.card P):ℝ)):
    denominator (Cloud.prescription q h 0 f)=register J r (OriginalRadialSeries.observed B (Wick Y q P)):=by
  apply Join.both_parts
  intro t u
  rw [denominator,bottom_value,WilsonVacuumPreResetFiniteRegister.read]
  by_cases ht:t=J.quiet
  · subst t
    rw [if_pos rfl,if_pos rfl,observed]
    change Cloud.wick q h 0 (Cloud.integrand f (Join.pair J.quiet u))=_
    exact scaled B q h P u.val.card _ (u.val.card.factorial:ℂ)
      (by exact_mod_cast (Nat.factorial_pos u.val.card).ne') (law u)
  · simp only [if_neg ht,mul_zero]

include cash width draw low high in
theorem original (well:Bulk.Well Q):
    denominator (Bulk.Fk (model R N m p hm) F tag (source R m p Z Q cap) x r)=
    register J r (OriginalRadialSeries.observed (flatten x) (mass R N m p hm F tag Z)):=by
  let f:=family R N m p hm F tag Z Q cap x r
  let P:=raiseE (opened R N m p hm F Z)
  have law (u:Index r)(z:Key F G→ℝ):Cloud.paint z (Cloud.integrand f (Join.pair J.quiet u))=
      (u.val.card.factorial:ℂ)*(MvPolynomial.eval (Sum.elim z (flatten x)) (coeff u.val.card P):ℝ):=by
    exact WilsonVacuumPreResetDepositedIntegrand.original R N m p hm F tag Z Q cash cap
      width draw low high x r z well u
  simpa only [mass,Bulk.Fk,Assembly.prescription,f,family,P] using
    table r (flatten x) ((model R N m p hm).covariance F tag) ((model R N m p hm).symm F tag) P f law

include cash width draw low high in
theorem normalized (well:Bulk.Well Q):
    logVac (Bulk.Fk (model R N m p hm) F tag (source R m p Z Q cap) x r)=
    register J r (logOf (OriginalRadialSeries.observed (flatten x) (mass R N m p hm F tag Z))):=by
  let K:=model R N m p hm
  let W:=source R m p Z Q cap
  have eq:=original R N m p hm F tag Z Q cash cap width draw low high x r well
  refine WilsonVacuumPreResetFiniteRegister.heard J r _ ?_ _ eq
  have h: (denominator (Bulk.Fk K F tag W x r)).part (Join.pair J.quiet (indices r).quiet)=1:=by
    rw [Join.pair_quiet]
    exact (bottom_quiet _).trans (Bulk.fk_unit ..)
  rw [eq,WilsonVacuumPreResetFiniteRegister.read] at h
  rw [show (indices r).quiet.val.card=0 from rfl] at h
  exact Complex.ofReal_injective (by simpa [coeff_zero_eq_constantCoeff_apply] using h)

end YM.Integration.WilsonVacuumPreResetDepositedMass
