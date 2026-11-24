import YM.Integration.WilsonMarkedRegulatorGaugeRays

/-! The whole signed half-torus orbit table, including the constant tensor. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMarkedRegulatorOrbitTable
open Function Filter Finset Lattice Exterior RG Laurent Wilson PertExtension Orb
open FormalBulk08 FormalBulk08.Orb Reef Jets Kemp Lava Stationary AllOrder
open WilsonCoeffUV WilsonCoeffUV.Mer RegulatorIR.Geometry RegulatorIR.Geometry.Field
open RegulatorIR.Laplace RegulatorIR.Binding RegulatorIR.Ward RegulatorIR.Quadratic
open RegulatorIR.Diagram RegulatorIR.Diagram.Formal RegulatorIR.Budget
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{r:ℕ}

def bond (i:wire G n):Edge (Site n):=(i.1,axisEquiv.symm i.2.1)
def name (i:wire G n):Book G n:=(index (bond i),i.2.2)
def sign (i:wire G n):ℝ:=if eR (bond i)=bond i then 1 else -1

theorem coordinate (x:Horizon G n)(i:wire G n):
    WilsonMarkedRegulatorGaugeRays.lift x i=sign i*((paper G n) x (name i)):=by
  have up:edgeColor (WilsonMarkedRegulatorGaugeRays.lift x)=fire x:=edgeColor.apply_symm_apply _
  have slot:=congrArg (fun a:Edge (Site n)→G.Color=>a (bond i) i.2.2) up
  change WilsonMarkedRegulatorGaugeRays.lift x (i.1,axisEquiv (axisEquiv.symm i.2.1),i.2.2)=_ at slot
  rw [axisEquiv.apply_symm_apply] at slot
  rw [slot]
  by_cases keep:eR (bond i)=bond i
  · simp only [fire,sign,keep,if_true,one_mul];rfl
  · simp only [fire,sign,if_neg keep,neg_one_mul];rfl

def orbit (T:chain (wire G n) r→ℝ):RegulatorIR.Budget.Packet (Book G n) r:=
  fun z=>∑ w:chain (wire G n) r,if name ∘ w=z then T w*∏i,sign (w i) else 0

/-- Restrict the native finite angular polynomial to the actual signed
physical regulator coordinates. Sum all genuine preimages, including ties. -/
theorem read (T:chain (wire G n) r→ℝ)(x:Horizon G n):
    MvPolynomial.eval (paper G n x) (render (orbit T))=
      traceP (WilsonMarkedRegulatorGaugeRays.lift x) (facade r T):=by
  classical
  simp only [render,facade_eq,traceP,MvPolynomial.aeval_eq_eval,map_sum,map_mul,MvPolynomial.eval_C,
    RegulatorIR.Diagram.word,Lava.cards,map_prod,MvPolynomial.eval_X]
  unfold orbit
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  rw [Finset.sum_eq_single (name ∘ w)]
  · simp [coordinate,Finset.prod_mul_distrib,mul_assoc]
  · intro b _ different;rw [if_neg (Ne.symm different),zero_mul]
  · simp

end YM.Integration.WilsonMarkedRegulatorOrbitTable
end
