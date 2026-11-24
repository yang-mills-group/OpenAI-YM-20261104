import YM.Integration.WilsonMarkedRegulatorSeries
import YM.Integration.WilsonMarkedRegulatorOrbitTable

/-! The actual finite and covered charged tables in regulator order notation. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMarkedRegulatorProgram
open Function Filter Finset Lattice Exterior RG Laurent Wilson PertExtension Orb
open FormalBulk08 FormalBulk08.Orb Reef Jets Kemp Lava Stationary AllOrder AllOrder.Response
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Mer WilsonCoeffUV.Blue RegulatorIR.Geometry
open RegulatorIR.Laplace RegulatorIR.Binding RegulatorIR.Ward RegulatorIR.Quadratic
open RegulatorIR.Diagram RegulatorIR.Diagram.Formal PowerSeries PositionX.Jet
open WilsonMarkedRegulatorOrbitTable WilsonFormalGaugeCurve
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge}{n:Side}{V:Type}[NormedAddCommGroup V][NormedSpace ℝ V]{k:ℕ}{K:Era G V}

def table (S:Pal ℝ (wire G n)):Orders (Book G n):=fun j r=> orbit (S j r)
def compiled (k:ℕ)(S:Pal ℝ (wire G n)):Pap (wire G n):=
    PowerSeries.mk fun j=>∑r∈range (j+k+1),facade r (S j r)
def copied (T:Pal ℝ (Cloth (Loc G 1)))(n:Side):Pal ℝ (wire G n):=fun j r=>sieve n (T j r)

theorem grade (S:Pal ℝ (wire G n))(cap:shellK k S): compiled k S=Blue.flash S:=by
  ext1 j
  simp only [compiled,Blue.flash,coeff_mk]
  rw [visible (n:=j+k+1) (P:=S j) (fun r hr=>cap j r (by omega))]
  exact Finset.sum_congr rfl fun r _=>(WilsonConditionalTaylorWheelTensors.painted r (S j r)).symm

theorem folded (T:Pal ℝ (Cloth (Loc G 1)))(k:ℕ)(n:Side):
    compiled k (copied T n)=Kemp.banner k T n:=by
  unfold compiled Kemp.banner copied;congr 1;funext j;rw [Nat.add_comm j k]

theorem measured (S:Pal ℝ (wire G n))(k:ℕ)(x:ℝ→ Horizon G n)(hx:ContDiffAt ℝ ω x 0)(e:ℕ):
    coeff e (reel (table S) k x)=weigh (WilsonMarkedRegulatorGaugeRays.lift ∘ x)
      (WilsonFormalGaugeCurve.evaluation (compiled k S)) e:=by
  have smooth:ContDiffAt ℝ ω (peel x) 0:=(paper G n).toLinearMap.toContinuousLinearMap.contDiff.contDiffAt.comp 0 hx
  rw [RegulatorIR.Ward.reel,WilsonMarkedRegulatorSeries.coefficient (peel x) smooth]
  unfold weigh;apply Finset.sum_congr rfl
  intro d _
  apply congrArg (fun a:ℝ→ℝ=>someJ a (e-d))
  funext t
  simp only [Function.comp_apply,WilsonFormalGaugeCurve.evaluation,rated_v,packed,traceP,
    MvPolynomial.aeval_eq_eval,map_sum,compiled,coeff_mk]
  apply Finset.sum_congr rfl
  intro r _
  exact WilsonMarkedRegulatorOrbitTable.read (S d r) (x t)

/-- This is the actual RegulatorIR.reel of the named original marked angular
table, at every grade. Its gauge may vary nonsmoothly in the parameter. -/
theorem original (bought:Auth k K)(o:Loc G 1)(f:V→L[ℝ]ℝ)
    (x y:ℝ→ Horizon G n)(hx:ContDiffAt ℝ ω x 0)(hy:ContDiffAt ℝ ω y 0)
    (meeting:reel_prop x y)(e:ℕ):
    let P:=tuftV f K
    coeff e (reel (table (P.1 n)) k y)=coeff e (reel (table (P.1 n)) k x) ∧
    coeff e (reel (table (copied P.2 n)) k y)=coeff e (reel (table (copied P.2 n)) k x):=by
  intro P
  have both:=WilsonMarkedRegulatorGaugeRays.original bought o f x y hx hy meeting e
  constructor
  · rw [measured _ k y hy,measured _ k x hx,grade (P.1 n) ((bought.tuft f).span n)]
    exact both.1
  · rw [measured _ k y hy,measured _ k x hx,folded]
    exact both.2

end YM.Integration.WilsonMarkedRegulatorProgram
end
