import YM.Integration.WilsonThermometerWeightedCapture
import YM.Integration.WilsonThermometerCourseHot
import YM.Integration.IntrinsicProductLinearity

/-! At the actual finite cutoff, delete source markers from the same
three inverse-calibrated Wilson fields. The resulting weighted cylinder is
the exact horizon-zero credit on every earlier original representation. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerLiteralCredit
open Finset MeasureTheory Table Spec Lattice Wilson RG Source Marker Extraction Climb Trace.Pilot
open Next.UVStress Next.Rank RG12 RG17 PhysMS PhysicalNext.Repeat.Legato MergeProof MergeProof.Accent MergeProof.East
open FVA1 OriginalForcedAddresses XSpace XSpace.Normalize XSpace.Rose Cells Push.GridApprox
open RG16.Literal WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open WilsonPositionThermometerGradedReading WilsonThermometerCourseIntake WilsonThermometerCenteredAlgebra
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G) (A : Group R.family 6) (simple : G.Simple) {N per : ℕ}
local notation "J" => Stock.census (Fin 3)
local notation "C" => R.family
local notation "Y" => Config G (R.family.side N per)
variable (o : Positions (Fin 3) (R.family.side N per)) (Q : Poly J)
local notation "face" s => WilsonThermometerCourseHot.bare R A o s

def cut : Cut C N per := ∑ s : (J).Mode, weight Q s • (face s)

theorem continuous_face (s : (J).Mode) : Continuous (face s) :=
  continuous_finsetProd _ fun _ _ => (C).continuousO N per _ _ _

theorem continuous_cut : Continuous (cut R A o Q) := by
  rw [cut,show (∑ s : (J).Mode,weight Q s • (face s))=_ from
    funext fun U=>sum_apply U _ _]
  exact continuous_finsetSum _ fun s _ => (continuous_face R A o s).const_smul (weight Q s)

private theorem scalar_push {j i : ℕ} (hi : i≤j) (f : Config G (R.family.side j per) → ℂ) :
    gust R.family.path N per j f i hi = pushTo R.family.path N per hi f := by
  induction hi using Nat.decreasingInduction with
  | self => rw [gust_base,pushTo_self]
  | of_succ i hi ih => rw [gust_step R.family.path N per j f hi,Birth.push_first R.family.path N per hi,ih]

theorem returned (refs : ∀ j : Fin 3, (C).ref (grade j) ≤ N) {i : ℕ} (upper : i ≤ N) :
    credit C N per 0 (cut R A o Q) i upper =
      fun U => (total (incoming R A simple upper o U) Q).part full := by
  have each (s : (J).Mode) (U : Config G (R.family.side i per)) :
      (incoming R A simple upper o U).part s = credit C N per 0 (face s) i upper U := by
    rw [incoming,WilsonPositionThermometerDepositedFaces.deposited R simple N per A.station
      (fun j : Fin 3=>index A (grade j)) (vector A univ) o refs upper s U,
      actualTransport_unnormalize C R.makes le_rfl,scalar_push]
    have top (W : Y) : (R.family.path.rep N per N).eval W = Wilson.bare (R.family.beta N per) W :=
      congrFun (R.makes.wilson.starts N per).2 W
    simp only [credit,pow_zero,one_smul,top,Complex.real_smul,WilsonThermometerCourseHot.bare]
  rw [cut,IntrinsicProductLinearity.credit_sum C N per 0 i upper (weight Q)
    (fun s : (J).Mode=>(face s)) (continuous_face R A o)]
  funext U
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,WilsonThermometerCenteredAlgebra.affine,each]

end YM.Integration.WilsonThermometerLiteralCredit
