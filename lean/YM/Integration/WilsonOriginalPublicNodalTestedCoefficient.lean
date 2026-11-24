import YM.Integration.WilsonOriginalPublicNodalTestedProbe

/-! The measured coefficient after its original pole has been cleared at the K birth. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalTestedCoefficient
open PowerSeries Laurent Bloch Precision Function Finset Lattice Wilson RG Source Labels Marker WilsonCoeffUV
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Embroider WilsonCoeffUV.Blue WilsonCoeffUV.Soil
open XSpace XSpace.Rose RegulatorIR RegulatorIR.Cluster PhysicalNext.Repeat.Legato
open WilsonIndependentMatchedOpeningPayment (affiled)
open WilsonOriginalPublicNodalTestedCore (roots)
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonOriginalPublicNodalTestedFunctional (deposit power charge)
open WilsonOriginalPublicNodalTestedChronology (registered rank funded)
open WilsonIndependentRawPhysicalFaces (ordered)
open WilsonIndependentSpoutScalarLedger (ground)
open WilsonIndependentSpoutDoseBoundary (into measure)
open WilsonOlderFreshSoftCoverScalar (clock)
open scoped Classical BigOperators

variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I](R:Run G)(W:Initialize G)(D d:I→ℕ)
    (b:∀i,(R.family.labels.level (d i)).Index)(κ:(i:I)→Knob (D i))(pt:I→Chamber)


theorem clear (A:Levels G)(O:ChartRatio G)(N K h q:ℕ)(u:ℝ)(E:Cost):
    coeff (q+h) (into A O N K (PowerSeries.C u*(PowerSeries.X:Cost)^h)*E)=
      u*coeff q ((relativeC A O N K (N-K))^h*E):=by
  let B:=relativeC A O N K (N-K)
  change coeff (q+h) ((reel B (PowerSeries.C u*PowerSeries.X^h))*E)=_
  rw [map_mul (reel B),map_pow (reel B),reel_C,reel_X,mul_pow]
  rw [show PowerSeries.C u*(B^h*PowerSeries.X^h)*E=PowerSeries.X^h*(PowerSeries.C u*(B^h*E)) by ring]
  simp [PowerSeries.coeff_X_pow_mul',B]

theorem scalar (A:Levels G)(O:ChartRatio G)(simple:G.Simple)(valid:LocalRatio O)
    (N K h:ℕ)(KN:K≤N)(u:ℝ)(E:Cost):
    coeff h (into A O N K (PowerSeries.C u*(PowerSeries.X:Cost)^h)*E)=u*coeff 0 E:=by
  have eq:=clear A O N K h 0 u E
  have unit:constantCoeff (relativeC A O N K (N-K))=1:=angularC simple valid (by omega)
  simpa only [Nat.zero_add,coeff_zero_eq_constantCoeff_apply,map_mul,map_pow,unit,one_pow,one_mul] using eq

variable {stamps:I→ℕ}(cut:∀i,d i<stamps i)

theorem original (A:Levels G)(O:ChartRatio G)(simple:G.Simple)(valid:LocalRatio O)
    (N:ℕ)(cells:Digits A I)(v c K:ℕ)(vc:v≤c)(cK:c≤K)(KN:K≤N)
    (y:I → Cover)(S:Finset I)[Nonempty S](test:Pen D S→L[ℝ] ℝ)(q:ℕ):
    let h:=rank R d b S
    let raw:=registered R W d b cut (roots A cells (K-c) c y) S
    let value:=test (deposit D κ pt S)
    let observed:=cruises A O N (mass d S) c v
      (WilsonOlderFreshSoftOrdinary.material D d A O (WilsonOlderFreshSoftFigures.stencil R D d b κ pt)
        N cells c K y S test)
    coeff (q+h) (into A O N v (ground observed))=
      value*coeff q ((relativeC A O N K (N-K))^h*measure A O N h K v raw) ∧ ‖value‖≤‖test‖:=by
  dsimp only
  constructor
  · rw [(WilsonOriginalPublicNodalTestedProbe.original R W D d b κ pt cut A O simple valid N cells v c K
      vc cK KN y S test).2, WilsonOriginalPublicNodalTestedProbe.valuation R D d b κ pt S test]
    exact clear A O N K _ q _ _
  · exact WilsonOriginalPublicNodalTestedProbe.bounded D κ pt S test

end YM.Integration.WilsonOriginalPublicNodalTestedCoefficient
end
