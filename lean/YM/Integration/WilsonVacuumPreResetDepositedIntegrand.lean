import YM.Integration.WilsonVacuumPreResetFiniteRegister

/-! The complete finite exponential of the original deposited vacuum
vertices on the same free field, before committing its shared Wick sum. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetDepositedIntegrand
open Function Finset Marker Multi Comparison.RG02 Order Cumulants PowerSeries
open Lattice Wilson RG Precision Tree Matrix Exterior PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedRay
open WilsonVacuumPreResetDepositedGeometric WilsonVacuumPreResetDepositedLetters
open WilsonVacuumPreResetFiniteRegister
open scoped Classical BigOperators Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner

variable {G:Gauge}(R:Run G)(N m p:ℕ)(hm:m<N)(F:Forest (step R m p).ratio)
variable (tag:(step R m p).Choices)(Z:SeriesA G)
variable {T:Type}[DecidableEq T][Fintype T]{J:Census T}(Q:Bulk.Colors J G (fine R m p))
variable (cash:BudgetPoint)(cap:ℕ){σ C:ℝ}(width:0<σ)(draw:Draw Z σ C)
    (low:∀a∈Z,3≤a.grade)(high:∀a∈Z,a.grade≤cap)
    (x:fieldDir G (coarse R m p) 1)(r:ℕ)(z:Key F G→ℝ)

def family :=
  let W:=source R m p Z Q cap
  Assembly.generator (Bulk.stage (model R N m p hm) F x) (Bulk.hinge F)
    W.power (Bulk.markFn (step R m p) F W) (Bulk.geometric (model R N m p hm) F tag W) r

include cash width draw low high in
private theorem filed (well:Bulk.Well Q):
    let v:=profile R m p F x z
    bottom J r (Multi.lit (Board J r) (fun i=>Cloud.paint z
      (family R N m p hm F tag Z Q cap x r i)))=
    register J r (OriginalRadialSeries.observed v (opened R N m p hm F Z)):=by
  intro v
  apply Join.both_parts
  intro t u
  rw [bottom_value,WilsonVacuumPreResetFiniteRegister.read]
  by_cases ht:t=J.quiet
  · subst t
    rw [if_pos rfl,if_pos rfl]
    unfold family
    rw [Assembly.colors,Order.polarization,Assembly.affine,map_add,Poly.part_plus,
      Assembly.mark_curve_quiet,add_zero,Assembly.realCoeff,Assembly.beads,if_pos rfl]
    apply congrArg (fun a:ℂ=>(u.val.card.factorial:ℂ)*a)
    have price:=WilsonVacuumPreResetDepositedLetters.original R N m p hm F tag Z Q cash cap
      width draw low high x z well u.val.card
    rw [Assembly.readingVacuum] at price
    exact price
  · simp only [if_neg ht,mul_zero]

include cash width draw low high in
theorem original (well:Bulk.Well Q)(u:Index r):
    Cloud.paint z (Cloud.integrand (family R N m p hm F tag Z Q cap x r) (Join.pair J.quiet u))=
      (u.val.card.factorial:ℂ)*(MvPolynomial.eval (profile R m p F x z)
        (coeff u.val.card (raiseE (opened R N m p hm F Z))):ℝ):=by
  let v:=profile R m p F x z
  let L:=Multi.lit (Board J r) (fun i=>Cloud.paint z
      (family R N m p hm F tag Z Q cap x r i))
  let P:=opened R N m p hm F Z
  let see:=OriginalRadialSeries.observed v
  have nil:constantCoeff P=0:=WilsonVacuumPreResetDepositedLetters.leading R N m p hm F Z
  have trivial:constantCoeff (see P)=0:=by
    change (MvPolynomial.eval v) (constantCoeff P)=0
    rw [nil,map_zero]
  have mc:see (raiseE P)=raiseE (see P):=by
    exact raise_map see (by simp [see,OriginalRadialSeries.observed]) nil
  have exp:bottom J r (Poly.pass L)=register J r (see (raiseE P)):=by
    rw [mc,exponential J r _ trivial,←filed R N m p hm F tag Z Q cash cap width draw low high x r z well]
    simp only [L,Poly.pass,map_sum,map_smul,map_pow]
  have result:=congrArg (fun b:Grade J r=>b.part (Join.pair J.quiet u)) exp
  rw [bottom_value,if_pos rfl,WilsonVacuumPreResetFiniteRegister.read,if_pos rfl] at result
  rw [Cloud.before_log]
  exact result

end YM.Integration.WilsonVacuumPreResetDepositedIntegrand
