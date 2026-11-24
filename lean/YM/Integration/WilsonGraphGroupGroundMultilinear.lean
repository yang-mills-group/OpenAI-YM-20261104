import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphCoefficients
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphLeading

set_option autoImplicit false
set_option warningAsError true

noncomputable section
open scoped BigOperators Classical

namespace YM.Integration.WilsonGraphGroupGroundMultilinear

variable {n : ℕ}

abbrev labels (g : YangMills.GaugeGroup) (d : Fin n → ℕ)
    (v : (i : Fin n) → (_root_.IssuedMaxwell.Reports.B g).sector (d i)) :
    Fin n → YangMills.MSbar.Ordinary.Label (_root_.IssuedMaxwell.Reports.B g) :=
  fun i => ⟨d i, v i⟩

def groundMap (g : YangMills.GaugeGroup) (d : Fin n → ℕ) (x : YangMills.Points n) :
    MultilinearMap ℂ (fun i : Fin n => (_root_.IssuedMaxwell.Reports.B g).sector (d i)) ℂ :=
  (_root_.YM.FVA2.Dframe.meteor (_root_.YM.FVA2.Teller.logNu 1)
    (_root_.YM.Integration.WilsonCapturedPhysicalMSDatum.original g.core) (∑ i, d i) x 0).compLinearMap
    (fun i => _root_.YM.XSpace.Normalize.up
      (Finset.single_le_sum (f := d) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)))

theorem graphValue (g : YangMills.GaugeGroup) (d : Fin n → ℕ) (x : YangMills.Points n)
    (hx : x ∈ YangMills.separated n)
    (v : (i : Fin n) → (_root_.IssuedMaxwell.Reports.B g).sector (d i)) :
    (_root_.IssuedMaxwell.GraphCoefficients.issued g).correlation n 0 (labels g d v) x =
      groundMap g d x v :=
  _root_.IssuedMaxwell.GraphCorrelation.regular g 0 (labels g d v) x hx

theorem maxwellValue (g : YangMills.GaugeGroup) (d : Fin n → ℕ) (x : YangMills.Points n)
    (hx : x ∈ YangMills.separated n)
    (v : (i : Fin n) → (_root_.IssuedMaxwell.Reports.B g).sector (d i)) :
    (_root_.IssuedMaxwell.Reports.B g).moment x (fun i => (v i).val) = groundMap g d x v :=
  (_root_.IssuedMaxwell.GraphLeading.original g (labels g d v) x hx).symm.trans
    (graphValue g d x hx v)

theorem graphUpdateAdd (g : YangMills.GaugeGroup) (d : Fin n → ℕ) (x : YangMills.Points n)
    (hx : x ∈ YangMills.separated n) (v : (i : Fin n) → (_root_.IssuedMaxwell.Reports.B g).sector (d i))
    (i : Fin n) (a b : (_root_.IssuedMaxwell.Reports.B g).sector (d i)) :
    (_root_.IssuedMaxwell.GraphCoefficients.issued g).correlation n 0
        (labels g d (Function.update v i (a + b))) x =
      (_root_.IssuedMaxwell.GraphCoefficients.issued g).correlation n 0
        (labels g d (Function.update v i a)) x +
      (_root_.IssuedMaxwell.GraphCoefficients.issued g).correlation n 0
        (labels g d (Function.update v i b)) x := by
  simpa only [graphValue g d x hx] using (groundMap g d x).map_update_add v i a b

theorem graphUpdateSMul (g : YangMills.GaugeGroup) (d : Fin n → ℕ) (x : YangMills.Points n)
    (hx : x ∈ YangMills.separated n) (v : (i : Fin n) → (_root_.IssuedMaxwell.Reports.B g).sector (d i))
    (i : Fin n) (c : ℂ) (a : (_root_.IssuedMaxwell.Reports.B g).sector (d i)) :
    (_root_.IssuedMaxwell.GraphCoefficients.issued g).correlation n 0
        (labels g d (Function.update v i (c • a))) x =
      c • (_root_.IssuedMaxwell.GraphCoefficients.issued g).correlation n 0
        (labels g d (Function.update v i a)) x := by
  simpa only [graphValue g d x hx] using (groundMap g d x).map_update_smul v i c a

theorem maxwellUpdateAdd (g : YangMills.GaugeGroup) (d : Fin n → ℕ) (x : YangMills.Points n)
    (hx : x ∈ YangMills.separated n) (v : (i : Fin n) → (_root_.IssuedMaxwell.Reports.B g).sector (d i))
    (i : Fin n) (a b : (_root_.IssuedMaxwell.Reports.B g).sector (d i)) :
    (_root_.IssuedMaxwell.Reports.B g).moment x (fun k => (Function.update v i (a + b) k).val) =
      (_root_.IssuedMaxwell.Reports.B g).moment x (fun k => (Function.update v i a k).val) +
      (_root_.IssuedMaxwell.Reports.B g).moment x (fun k => (Function.update v i b k).val) := by
  calc
    _ = groundMap g d x (Function.update v i (a + b)) := maxwellValue g d x hx _
    _ = groundMap g d x (Function.update v i a) + groundMap g d x (Function.update v i b) :=
      (groundMap g d x).map_update_add v i a b
    _ = _ := congrArg₂ (· + ·) (maxwellValue g d x hx (Function.update v i a)).symm
      (maxwellValue g d x hx (Function.update v i b)).symm

theorem maxwellUpdateSMul (g : YangMills.GaugeGroup) (d : Fin n → ℕ) (x : YangMills.Points n)
    (hx : x ∈ YangMills.separated n) (v : (i : Fin n) → (_root_.IssuedMaxwell.Reports.B g).sector (d i))
    (i : Fin n) (c : ℂ) (a : (_root_.IssuedMaxwell.Reports.B g).sector (d i)) :
    (_root_.IssuedMaxwell.Reports.B g).moment x (fun k => (Function.update v i (c • a) k).val) =
      c • (_root_.IssuedMaxwell.Reports.B g).moment x (fun k => (Function.update v i a k).val) := by
  calc
    _ = groundMap g d x (Function.update v i (c • a)) := maxwellValue g d x hx _
    _ = c • groundMap g d x (Function.update v i a) :=
      (groundMap g d x).map_update_smul v i c a
    _ = _ := congrArg (fun z : ℂ => c • z)
      (maxwellValue g d x hx (Function.update v i a)).symm

theorem firstSlotAdd (g : YangMills.GaugeGroup) (d : Fin (n + 1) → ℕ)
    (x : YangMills.Points (n + 1)) (hx : x ∈ YangMills.separated (n + 1))
    (v : (i : Fin (n + 1)) → (_root_.IssuedMaxwell.Reports.B g).sector (d i))
    (a b : (_root_.IssuedMaxwell.Reports.B g).sector (d 0)) :
    (_root_.IssuedMaxwell.Reports.B g).moment x (fun k => (Function.update v 0 (a + b) k).val) =
      (_root_.IssuedMaxwell.Reports.B g).moment x (fun k => (Function.update v 0 a k).val) +
      (_root_.IssuedMaxwell.Reports.B g).moment x (fun k => (Function.update v 0 b k).val) :=
  maxwellUpdateAdd g d x hx v 0 a b

theorem firstSlotSMul (g : YangMills.GaugeGroup) (d : Fin (n + 1) → ℕ)
    (x : YangMills.Points (n + 1)) (hx : x ∈ YangMills.separated (n + 1))
    (v : (i : Fin (n + 1)) → (_root_.IssuedMaxwell.Reports.B g).sector (d i))
    (c : ℂ) (a : (_root_.IssuedMaxwell.Reports.B g).sector (d 0)) :
    (_root_.IssuedMaxwell.Reports.B g).moment x (fun k => (Function.update v 0 (c • a) k).val) =
      c • (_root_.IssuedMaxwell.Reports.B g).moment x (fun k => (Function.update v 0 a k).val) :=
  maxwellUpdateSMul g d x hx v 0 c a

end YM.Integration.WilsonGraphGroupGroundMultilinear
end
