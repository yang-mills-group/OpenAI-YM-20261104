import YM.Integration.WilsonOriginalTwoFlatRoseIdentity
import YM.Integration.WilsonMaxwellThermometerNominatedSecant
import YM.Integration.WilsonPositionThermometerGradedSource
import YM.Integration.WilsonCenteredCompactBooking

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatRoseSecant
open WilsonCenteredPhysicalPanel Source Labels Extra.Histories Planned.GuardedAtom RG16.Literal Trace.Physical.GermGraph
open WilsonThermometerUnitFilingFlatTelescope WilsonOriginalTwoFlatGridScaling WilsonOriginalTwoFlatRoseIdentity
open OPE OPE.Orbits Extraction Spec Table
open Finset Marker Function MeasureTheory Lattice RG Wilson
open MergeProof MergeProof.Accent Climb XSpace XSpace.Rose Next.Foundations RG16
open PhysicalNext.Repeat.Legato WilsonPositionThermometerGradedSource
open WilsonThermometerCenteredAlgebra WilsonPositionThermometerConnected
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){N per:ℕ}

def field (Y:(v:Fin 3) → R.family.label (grade v))
    (o:Sites R (N,per) 3)(s:Finset (Fin 3)):Cut R.family N per:=
  fun U=>∏i∈s,R.family.O N per (Y i) (o i) U

theorem regular (Y:(v:Fin 3) → R.family.label (grade v))
    (o:Sites R (N,per) 3)(s:Finset (Fin 3)):Continuous (field R (N:=N) (per:=per) Y o s):=
  continuous_finsetProd _ fun i _=>R.family.continuousO N per _ (Y i) (o i)

local notation "C" => R.family
local notation "F₀" => Finset (Fin 3)
local notation "P₀" => Sites R (N,per) 3
local notation "X₀" j:max => Config G ((C).side j per)
theorem ordered (Y:(i:Fin 3) → R.family.label (WilsonPositionThermometerGradedSource.grade i))
    (M:Sites R (N,per) 3 → Finset (Fin 3) → (j:ℕ) → Config G (R.family.side j per) → ℂ)
    (Q:Sites R (N,per) 3 → Finset (Fin 3) → ℂ) {K c u v:ℕ}(uc:u≤c)(vc:v≤c)(ck:c≤K)(kn:K≤N)
    (paid:∀(o:P₀)(s:F₀)(j:ℕ),min u v≤j → j≤K → Integrable (numerator R N per j (M o s j)) (prior G _))
    (φ:Test 3)(r:ℝ):
    ∑o:P₀,WilsonCenteredCompactBooking.mass R φ r (N,per) o*(WilsonPositionThermometerConnected.value (fun s=>(C).omega N per (field R (N:=N) (per:=per) Y o s))-WilsonPositionThermometerConnected.value (Q o)) =
      ∑o:P₀,WilsonCenteredCompactBooking.mass R φ r (N,per) o*∑s:F₀,WilsonMaxwellThermometerNominatedSecant.bill (fun t=>(C).omega N per (field R (N:=N) (per:=per) Y o t)) (Q o) s*
        (gap R N per u ((uc.trans ck).trans kn) (field R (N:=N) (per:=per) Y o s)+WilsonOriginalTwoFlatRoseIdentity.entry R (N:=N) (per:=per) (uc.trans ck) kn (field R (N:=N) (per:=per) Y o s) (M o s)+
          (∑j∈Ico c K,feeAt R N per u (M o s) j)+WilsonOriginalTwoFlatRoseIdentity.cross R (N:=N) (per:=per) uc vc (M o s)+
          (∑j∈Ico v c,feeAt R N per v (M o s) j)+(M o s v 1-Q o s)):=by
  apply sum_congr rfl
  intro o _
  apply congrArg (_*·)
  rw [WilsonMaxwellThermometerNominatedSecant.signed]
  apply sum_congr rfl
  intro s _
  exact congrArg (_*·) (figure R uc vc ck kn (field R (N:=N) (per:=per) Y o s) (regular R (N:=N) (per:=per) Y o s) (M o s) (paid o s) (Q o s))

private theorem empty_free (a b:F₀ → ℂ):WilsonMaxwellThermometerNominatedSecant.bill a b ∅=0:=by
  have none (t:Fin 7): (∅:F₀)≠WilsonMaxwellThermometerNominatedSecant.faceKey t:=by
    fin_cases t <;> decide
  simp [WilsonMaxwellThermometerNominatedSecant.bill,none]

theorem estimate (Y:(i:Fin 3) → R.family.label (WilsonPositionThermometerGradedSource.grade i))
    (M:Sites R (N,per) 3 → Finset (Fin 3) → (j:ℕ) → Config G (R.family.side j per) → ℂ)
    (Q:Sites R (N,per) 3 → Finset (Fin 3) → ℂ) {K c u v:ℕ}(uc:u≤c)(vc:v≤c)(ck:c≤K)(kn:K≤N)
    (paid:∀(o:P₀)(s:F₀)(j:ℕ),min u v≤j → j≤K → Integrable (numerator R N per j (M o s j)) (prior G _))
    (φ:Test 3)(r:ℝ)
    (phase upper shift:P₀ → F₀ → ℝ)
    (truePhase:∀(o:P₀)(s:F₀),WilsonCenteredCompactBooking.mass R φ r (N,per) o≠0 → s.Nonempty → ‖gap R N per u ((uc.trans ck).trans kn) (field R (N:=N) (per:=per) Y o s)‖ ≤ phase o s)
    (trueUpper:∀(o:P₀)(s:F₀),WilsonCenteredCompactBooking.mass R φ r (N,per) o≠0 → s.Nonempty → ‖WilsonOriginalTwoFlatRoseIdentity.entry R (N:=N) (per:=per) (uc.trans ck) kn (field R (N:=N) (per:=per) Y o s) (M o s)‖ ≤ upper o s)
    (trueShift:∀(o:P₀)(s:F₀),WilsonCenteredCompactBooking.mass R φ r (N,per) o≠0 → s.Nonempty → ‖WilsonOriginalTwoFlatRoseIdentity.cross R (N:=N) (per:=per) uc vc (M o s)‖ ≤ shift o s):
    ‖∑o:P₀,WilsonCenteredCompactBooking.mass R φ r (N,per) o*(WilsonPositionThermometerConnected.value (fun s=>(C).omega N per (field R (N:=N) (per:=per) Y o s))-WilsonPositionThermometerConnected.value (Q o))‖ ≤
      ∑o:P₀,‖WilsonCenteredCompactBooking.mass R φ r (N,per) o‖*∑s:F₀,‖WilsonMaxwellThermometerNominatedSecant.bill (fun t=>(C).omega N per (field R (N:=N) (per:=per) Y o t)) (Q o) s‖*
        (phase o s+upper o s+(∑j∈Ico c K,‖feeAt R N per u (M o s) j‖)+shift o s+
          (∑j∈Ico v c,‖feeAt R N per v (M o s) j‖)+‖M o s v 1-Q o s‖):=by
  apply (norm_sum_le ..).trans
  apply sum_le_sum
  intro o _
  rw [norm_mul, WilsonMaxwellThermometerNominatedSecant.signed]
  by_cases live:WilsonCenteredCompactBooking.mass R φ r (N,per) o=0
  · simp [live]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (norm_sum_le ..).trans
  apply sum_le_sum
  intro s _
  rw [norm_mul]
  by_cases yes:s.Nonempty
  · exact mul_le_mul_of_nonneg_left (price R uc vc ck kn (field R (N:=N) (per:=per) Y o s) (regular R (N:=N) (per:=per) Y o s) (M o s)
      (paid o s) (Q o s) (truePhase o s live yes) (trueUpper o s live yes) (trueShift o s live yes)) (norm_nonneg _)
  · rw [not_nonempty_iff_eq_empty.mp yes,empty_free];simp

end YM.Integration.WilsonOriginalTwoFlatRoseSecant
