import YM.Integration.WilsonIndependentSpoutMuralBoard
import YM.Integration.WilsonIndependentSpoutReportedQuiet

/-! Scalar readings of a finite symmetric bank determine each ordered tensor,
also after folding several fine stencils to the same retained link. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutAtomicPolar
open Function PowerSeries Lattice RG WilsonCoeffUV WilsonCoeffUV.Blue
open RegulatorIR RegulatorIR.Budget RegulatorIR.Budget.Packet RegulatorIR.Prim
open RegulatorIR.Diagram RegulatorIR.Geometry RegulatorIR.Oracle
open Tree FreeResolvent Metric Precision Exterior
open WilsonIndependentSpoutFiniteStencil (Raw)
open WilsonIndependentSpoutPrimitiveReport (axis)
open scoped Classical BigOperators

variable {I J:Type}
private def turn (f:I→J){r:ℕ}(σ:Equiv.Perm (Fin r))(x:Tuple J r):
    Stalk (fun z:Tuple I r=>f∘z) x≃Stalk (fun z:Tuple I r=>f∘z) (x∘σ):=
  Equiv.subtypeEquiv (Tuple.perm I σ) (fun z=>by
    change f∘z=x ↔ (f∘z)∘σ=x∘σ
    constructor
    · intro h;rw [h]
    · intro h;funext j;simpa only [Function.comp_apply,Equiv.apply_symm_apply] using congrFun h (σ.symm j))

theorem symmetric (f:I→J){r:ℕ}{T:Packet I r}(symm:IsSym T):
    IsSym (Stalk.collect (fun z:Tuple I r=>f∘z) T):=by
  intro σ x
  unfold Stalk.collect
  rw [←(turn f σ x).tsum_eq]
  apply tsum_congr
  intro i
  exact symm σ i.val

theorem supported (f:I→J){T:Ranked I}{h:ℕ}(scope:Within h T):
    Within h (fun r=>Stalk.collect (fun z:Tuple I r=>f∘z) (T r)):=by
  intro r hr
  apply scope r
  intro zero
  apply hr
  ext1 x
  simp [zero,Stalk.collect]

theorem held [Fintype I][Fintype J](σ:I≃J)(P:Gen ℝ J)(h:ℕ)(band:∀r,h<r→P r=0)(y:J→ℝ):
    drums (fun r q=>P r (σ∘q)) h (y∘σ)=MvPolynomial.eval y (totalR P):=by
  rw [visible (n:=h+1) (fun r hr=>band r (by omega))]
  unfold drums
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro r _
  unfold strum
  rw [tsum_fintype]
  change _=MvPolynomial.aeval y (∑ u:Tuple J r,P r u • ∏ j,MvPolynomial.X (u j))
  simp only [map_sum,map_smul,map_prod,MvPolynomial.aeval_X,smul_eq_mul]
  let e:Tuple I r≃Tuple J r:=Equiv.arrowCongr (Equiv.refl _) σ
  exact Equiv.sum_comp e (fun u=>P r u*∏j,y (u j))

def seats {G:Gauge}(n:Side):Raw G n≃Woods G n:=
  (Equiv.prodAssoc _ _ _).trans (Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr axisEquiv (Equiv.refl _)))

theorem seats_apply {G:Gauge}(n:Side)(p:Raw G n):
    seats n p=WilsonIndependentSpoutPostedAction.seat n p:=rfl

theorem all {G:Gauge}(n:Side)(x:Raw G n→ℝ):∃y:TreeVars G n,axis y=x:=by
  refine ⟨x∘(seats n).symm,?_⟩
  funext i
  exact congr_arg x ((seats n).symm_apply_apply i)

end YM.Integration.WilsonIndependentSpoutAtomicPolar
