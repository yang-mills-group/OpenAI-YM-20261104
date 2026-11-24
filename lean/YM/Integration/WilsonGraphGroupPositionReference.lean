import YM.Integration.WilsonGraphPositionExtensional
import YangMills.WilsonProof.NativeSupport.ContinuumConstruction.StandaloneCorrelation
import YM.FVA2.XReg.Continuum
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphCoefficients
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedEveryBareSlope
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedAppointedConversionValid

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonGraphGroupPositionReference
open YangMills YangMills.MSbar
open YM YM.Integration YM.XSpace YM.FVA2 YM.FVA2.Scale YM.FVA2.Register
open YM.MS YM.MS.Land YM.MS.Fleet
open YM.Answer.ContinuumLimit
open WilsonGraphStandaloneCorrelation
open scoped BigOperators Classical

variable {g : YangMills.GaugeGroup}

theorem capLe (g : YangMills.GaugeGroup) {n : ℕ} (a : Fin n → Label g) :
    cutoff a ≤ _root_.IssuedMaxwell.GraphCorrelation.sky g a :=
  Finset.sup_le fun i _ => Finset.single_le_sum (f := fun j => (a j).1)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

theorem sameMarks (g : YangMills.GaugeGroup) {n : ℕ} (a : Fin n → Label g) :
    XSpace.Normalize.up (capLe g a) ∘ marks a (within a) =
      _root_.IssuedMaxwell.GraphCorrelation.stamped g a := rfl

theorem agreement (g : YangMills.GaugeGroup) (n k : ℕ) (a : Fin n → Label g)
    (x : YangMills.Points n) (hx : x ∈ YangMills.separated n) :
    (_root_.IssuedMaxwell.GraphCoefficients.issued g).correlation n k a x = bare g n k a x := by
  change _root_.IssuedMaxwell.GraphCorrelation.read g n k a x = bareAt a x k
  rw [_root_.IssuedMaxwell.GraphCorrelation.regular g k a x hx,
    identified a x hx k (WilsonCapturedPhysicalMSDatum.original g.core), ← sameMarks g a]
  exact YM.FVA2.Reg.State.initial_chain (Teller.logNu 1)
    (WilsonCapturedPhysicalMSDatum.original g.core) (k := k) (capLe g a) x (marks a (within a))

theorem positions (hg : g.IsSimple) (M : Coefficients (maxwellReference g))
    (reads : M.correlation = bare g) :
    (∀ t : YangMills.MSbar.Position.Triangle (maxwellReference g), t.Admissible → t.RawSlopeAgrees M) ∧
      ConversionValid M (_root_.IssuedMaxwell.ElectedPrescription.prior g hg).val
        (_root_.IssuedBridge.PostedAppointedConversionFields.filed hg true) :=
  WilsonGraphPositionExtensional.forEveryBare (_root_.IssuedMaxwell.GraphCoefficients.issued g)
    (agreement g) (_root_.IssuedMaxwell.ElectedPrescription.prior g hg).val
    (_root_.IssuedBridge.PostedAppointedConversionFields.filed hg true)
    (_root_.IssuedBridge.PostedEveryBareSlope.original hg)
    (_root_.IssuedBridge.PostedAppointedConversionValid.original hg true) M reads

def external (g : YangMills.GaugeGroup) (hg : g.IsSimple) : WilsonGraphStandaloneCorrelation.External g where
  menu := (_root_.IssuedMaxwell.ElectedPrescription.prior g hg).val
  admissible := (_root_.IssuedMaxwell.ElectedPrescription.prior g hg).property
  conversion := _root_.IssuedBridge.PostedAppointedConversionFields.filed hg true
  realization := _root_.IssuedBridge.PostedAppointedConversionValid.realized hg true
  everyBareSlope M reads := (positions hg M reads).1
  valid M reads := (positions hg M reads).2

theorem filed (hg : g.IsSimple) :
    (external g hg).conversion = _root_.IssuedBridge.PostedPositionConversion.filed
      (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonCapturedPhysicalMSDatum.original g.core)
      (_root_.IssuedBridge.PostedAppointedConversionFields.elected hg true) (Teller.logNu 1) := rfl

private theorem matchedAt {H₁ H₂ : g.core.Simple}
    {Z : WilsonPrescription g.core}
    {A D : MS_Data g.core (YM.FVA2.Position.OpenAxis.Plot (Press.portDeck g.core))}
    {σ τ : Prescription (Press.portDeck g.core)} {l m : Bool}
    (same : A = D) (left : Main.Match Z H₁ A σ l) (right : Main.Match Z H₂ D τ m) (μ : ℝ) :
    _root_.IssuedBridge.PostedPositionConversion.filed Z A left μ =
      _root_.IssuedBridge.PostedPositionConversion.filed Z D right μ := by
  cases same
  rfl

theorem atPerspective (hg : g.IsSimple) {H : g.core.Simple} {lamp : Bool}
    (Q : Perspective H (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) lamp)
    (reads : Q.MS = WilsonCapturedPhysicalMSDatum.original g.core) :
    (external g hg).conversion = _root_.IssuedBridge.PostedPositionConversion.filed
      (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) Q.MS Q.matching (Teller.logNu 1) := by
  rw [filed hg]
  exact matchedAt reads.symm (_root_.IssuedBridge.PostedAppointedConversionFields.elected hg true)
    Q.matching (Teller.logNu 1)

end YM.Integration.WilsonGraphGroupPositionReference
end
