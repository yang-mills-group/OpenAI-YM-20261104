import YM.Integration.WilsonIndependentSpoutPostedSuffix
import YM.Integration.WilsonOlderFreshSoftSocketKinetic

/-! Recovering the complete marked scalar in its measured kinetic variable from the reported scalar. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentSpoutScalarLedger
open Function Lattice Wilson RG PowerSeries WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Blue WilsonCoeffUV.Bank
open WilsonCoeffUV.Power WilsonCoeffUV.Soil PertExtension Metric Precision Exterior
open WilsonCoeffUV.Cosmos (reelQuote)
open RegulatorIR RegulatorIR.Diagram RegulatorIR.Geometry RegulatorIR.Budget
open RegulatorIR.Budget.Layer RegulatorIR.Ledger RegulatorIR.Ledger.Sky RegulatorIR.Prim RegulatorIR.Clocks
open WilsonIndependentSpoutFundedClocks (age clock)
open WilsonIndependentSpoutOriginalMarkedJourney (source)
open WilsonOlderFreshSoftSocketKinetic (reading)
open scoped Classical BigOperators
variable {G:Gauge}{W:Type}{M:W→ℕ}(A:W→Levels G)(O:ChartRatio G)(s:W→ℕ)

def ground (X:Era G ℝ):Cost:=reading X.2 (r:=0) Fin.elim0
def scalar {J:Type}(rows:Orders J):Cost:=PowerSeries.mk fun e=>note (rows e 0)
def prior (v:Page M):Cost:=relativeF (A v.bindW) O (s v.bindW+M v.bindW) (age s v) v.downW

theorem reported (v:Page M)(X:Era G ℝ):
    scalar (source A s O v X)=reel (clock A O s v) (ground X):=by
  ext e
  rw [scalar,PowerSeries.coeff_mk,reelQuote]
  let α:=clock A O s v
  change (mix α X.2 e 0) (WilsonIndependentConditionalNativeLinks.coarse G ∘ Fin.elim0)=_
  rw [show (WilsonIndependentConditionalNativeLinks.coarse G ∘ Fin.elim0)=
    (Fin.elim0:Fin 0→_) from funext fun i=>i.elim0]
  simp only [mix,ground,WilsonOlderFreshSoftSocketKinetic.reading,PowerSeries.coeff_mk,pow_zero,mul_one,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  exact Finset.sum_congr rfl fun _ _=>mul_comm _ _

theorem original (simple:G.Simple)(valid:LocalRatio O)(v:Page M)(X:Era G ℝ):
    reel (prior A O s v) (scalar (source A s O v X))=ground X:=by
  rw [reported]
  change ((reel (prior A O s v)).comp (reel (clock A O s v))) _=_
  rw [reel_chart]
  have room:age s v+v.downW ≤ s v.bindW+M v.bindW:=by
    have h:=v.good
    dsimp only [age]
    omega
  rw [show chartB (clock A O s v) (prior A O s v)=1 from (direction simple valid room).2,reel_one]

theorem measured (simple:G.Simple)(valid:LocalRatio O)(v:Page M)(X:Era G ℝ)(p:ℕ)(rows:Orders (Foot G))
    (same:Clocks.Matches p rows (source A s O v X))(q:ℕ)(hq:q ≤ p):
    coeff q (reel (prior A O s v) (scalar rows))=coeff q (ground X):=by
  rw [←original A O s simple valid v X,reelQuote,reelQuote]
  apply Finset.sum_congr rfl
  intro i hi
  have fee:=same i (by have:=Finset.mem_range.mp hi;omega)
  simp only [scalar,PowerSeries.coeff_mk]
  rw [fee]

end YM.Integration.WilsonIndependentSpoutScalarLedger
