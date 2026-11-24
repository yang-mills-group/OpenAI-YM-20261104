import YM.Integration.WilsonIndependentSpoutPostedAction
import YM.Integration.WilsonIndependentSpoutKineticToken

/-! The actual quiet history in bare coordinates, with its native
finite-to-cover wage and the normalized quadratic removed at order zero. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutReportedQuiet
open Filter Function Matrix PowerSeries Lattice RG WilsonCoeffUV WilsonCoeffUV.Blue
open PertExtension Tree FreeResolvent Metric Precision Exterior Next.Free Wilson WilsonCoeffUV.Power
open RegulatorIR.Budget RegulatorIR.Diagram RegulatorIR.Geometry.Field
open WilsonCoeffUV.Bank WilsonCoeffUV.Mer RegulatorIR RegulatorIR.Geometry RegulatorIR.Prim
open RegulatorIR.Budget.Packet RegulatorIR.Diagram.Formal RegulatorIR.Oracle
open WilsonIndependentSpoutFiniteStencil (Raw coordinates)
open WilsonIndependentSpoutKineticToken (placed)
open WilsonIndependentSpoutPostedAction (seat)
open scoped Classical BigOperators Topology Matrix
variable {G:Gauge}

private theorem rotated {P:Mantle G}{H:FaceRow}(h:Hier H P)(α:Cost)(e r:ℕ):
    Yields (fun n=>mix α (P.1 n) e r) (mix α P.2 e r):=by
  have t:=Yields.sum (Finset.range (e+1)) (fun i _=>(h.patch i r).smul (coeff (e-i) (α^i*(α⁻¹)^r)))
  convert t using 1 <;> first | rfl | (funext n x;simp only [Blue.mix,Finset.sum_apply,Pi.smul_apply])

def finite (A:Levels G)(Ñ:ChartRatio G)(N m:ℕ)(α:Cost)(e r:ℕ):raw (Hooks G) ℝ r:=
  if e=0 then 0 else fun n=>-mix α ((story A Ñ N m).1 n) e r

def cover (A:Levels G)(Ñ:ChartRatio G)(N m:ℕ)(α:Cost)(e r:ℕ):Ten ℝ (YForest G) r:=
  if e=0 then 0 else -mix α (story A Ñ N m).2 e r

def port (A:Levels G)(Ñ:ChartRatio G)(N m:ℕ)(α:Cost):Orders (Foot G):=
  fun e r q=>cover A Ñ N m α e r (placed∘q)

def exposed (A:Levels G)(Ñ:ChartRatio G)(N m:ℕ)(α:Cost)(n:Side):Orders (Raw G n):=
  fun e r q=>finite A Ñ N m α e r n (seat n∘q)

theorem earned (A:Levels G)(Ñ:ChartRatio G)(simple:G.Simple)(ratio:LocalRatio Ñ)(N m:ℕ)(age:m≤N)
    (α:Cost)(e r:ℕ):Yields (finite A Ñ N m α e r) (cover A Ñ N m α e r):=by
  unfold finite cover
  split
  · exact Yields.zero
  · exact (rotated (old A Ñ simple ratio N m age) α e r).neg

theorem positive (A:Levels G)(Ñ:ChartRatio G)(simple:G.Simple)(ratio:LocalRatio Ñ)(N m:ℕ)(age:m≤N)
    (α:Cost)(e r:ℕ)(hr:0<r)(q:Tuple (Foot G) r):
    Tendsto (fun n=>exposed A Ñ N m α n e r (coordinates n∘q)) atTop (𝓝 (port A Ñ N m α e r q)):=by
  have t:=(earned A Ñ simple ratio N m age α e r).point (placed∘q)
  have rows (n:Side):foldUnder n∘(placed∘q)=WilsonIndependentSpoutPostedAction.seat n∘(coordinates n∘q):=by funext i;rfl
  simpa only [exposed,port,Bank.dilute,if_neg (Nat.ne_of_gt hr),rows] using t

theorem angular (A:Levels G)(Ñ:ChartRatio G)(N m:ℕ)(α:Cost)(e r:ℕ)(he:0<e)(n:Side)(q:Tuple (Raw G n) r):
    exposed A Ñ N m α n e r q = -mix α ((story A Ñ N m).1 n) e r (seat n∘q):=by
  simp only [exposed,finite,if_neg (Nat.ne_of_gt he),Pi.neg_apply]

end YM.Integration.WilsonIndependentSpoutReportedQuiet
