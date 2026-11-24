import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphCoefficients
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphLeading
import FormalConversion
import MSReference
import YangMills.WilsonProof.NativeSupport.YangMills.FreeFields

set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace PhysicalMatching.H7IndependentGroupFirstWardTree
open YM YangMills YangMills.Matching
open scoped Classical BigOperators
variable {g : YangMills.GaugeGroup} {n : ℕ}

theorem inputsZero (S : YangMills.Matching.Conversion (_root_.IssuedMaxwell.Reports.B g))
    (a : Fin n → YangMills.Matching.Label (_root_.IssuedMaxwell.Reports.B g)) (ν : Fin n → Fin 1) :
    S.inputs a ν = a := by
  funext i
  have h : (ν i).val = 0 := by omega
  simp [YangMills.Matching.Conversion.inputs, h, S.leading]

theorem unchangedAtZero (S : YangMills.Matching.Conversion (_root_.IssuedMaxwell.Reports.B g))
    (M : YangMills.MSbar.Coefficients (_root_.IssuedMaxwell.Reports.B g))
    (a : Fin n → YangMills.Matching.Label (_root_.IssuedMaxwell.Reports.B g)) (x : YangMills.Points n) :
    S.correlation M 0 a x = M.correlation n 0 a x := by
  classical
  have hz (j : Fin 1) : j.val = 0 := by omega
  simp [YangMills.Matching.Conversion.correlation, Fintype.sum_unique,
    hz, inputsZero, YangMills.Matching.couplingPower]

theorem groupLeading (S : YangMills.Matching.Conversion (_root_.IssuedMaxwell.Reports.B g))
    (a : Fin n → YangMills.Matching.Label (_root_.IssuedMaxwell.Reports.B g))
    (x : YangMills.Points n) (hx : x ∈ YM.conf n) :
    S.correlation (_root_.IssuedMaxwell.GraphCoefficients.issued g) 0 a x =
      (_root_.IssuedMaxwell.Reports.B g).moment x (fun i => (a i).2.val) := by
  rw [unchangedAtZero]
  exact _root_.IssuedMaxwell.GraphLeading.original g a x hx

theorem localLeading (S : YangMills.Matching.Conversion (_root_.IssuedMaxwell.Reports.B g))
    (M : YangMills.MSbar.Coefficients (_root_.IssuedMaxwell.Reports.B g))
    (a : Fin n → YangMills.Matching.Label (_root_.IssuedMaxwell.Reports.B g))
    (x : YangMills.Points n) (hx : x ∈ YM.conf n)
    (read : M.correlation n 0 a x =
      (_root_.IssuedMaxwell.GraphCoefficients.issued g).correlation n 0 a x) :
    S.correlation M 0 a x = (_root_.IssuedMaxwell.Reports.B g).moment x (fun i => (a i).2.val) := by
  rw [unchangedAtZero,read]
  exact _root_.IssuedMaxwell.GraphLeading.original g a x hx

end PhysicalMatching.H7IndependentGroupFirstWardTree
end
