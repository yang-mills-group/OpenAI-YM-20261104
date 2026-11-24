import YM.Integration.WilsonReceivedChronologicalFixedRoseVariation
import YM.Integration.WilsonReceivedChronologicalFixedRoseGradeReturn

/-! The connected difference is formed at its submitted positions and kept inside the same signed test. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalFixedRoseTestProducts
open Finset Lattice Wilson RG Marker Multi QuadraticLocal Org AllOrder Function MeasureTheory Analysis Table Spec Extraction
open QuadraticLocal.Affinity QuadraticLocal.Earn QuadraticLocal.Mentor PhysicalNext.Repeat.Legato Next.UVStress StressFlux.Matching Cells
open WilsonCenteredPhysicalPanel WilsonCenteredCompactBooking WilsonReceivedCanonicalVersePortfolio
open scoped Classical BigOperators Topology
open WilsonPositionThermometerConnected
open WilsonMaxwellThermometerNominatedSecant (bill)
open WilsonOriginalObservedRoseMeshHeight (height)
open WilsonOriginalObservedRoseVanePurse (ages)
open WilsonReceivedChronologicalFixedRoseVariation (cells signed total)
open scoped Classical BigOperators
open RG16 RG16.Literal
open Extra.Histories
local notation "Faces" => Finset (Fin 3)
/-- The physical cells may carry any finite array. The three chosen arms use
the same marked coordinate map on all proper faces. -/
def mode {n:ℕ}(port:Fin 3↪Fin n)(s:Finset (Fin 3)):(Stock.census (Fin n)).Mode:=
  ⟨s.map port,mem_univ _⟩

variable {G:Gauge}(R:Run G){n:ℕ}(φ:Test n)(r:ℝ)(grid:ℕ×ℕ)
local notation "domain" => cells R φ r grid
local notation "mass₀" => WilsonCenteredCompactBooking.mass R φ r grid

theorem exact_read (p q:domain→Faces→ℂ):
    signed R φ r grid (fun z=>value (p z)-value (q z))=
      ∑z:domain,mass₀ z.val*∑s:Faces,bill (p z) (q z) s*(p z s-q z s):=by
  unfold WilsonReceivedChronologicalFixedRoseVariation.signed
  exact sum_congr rfl fun z _=>congrArg (mass₀ z.val*·)
    (WilsonMaxwellThermometerNominatedSecant.signed (p z) (q z))

theorem price (p q:domain→Faces→ℂ)(fee:domain→Faces→ℝ)(paid:∀z s,‖p z s-q z s‖≤fee z s):
    ‖signed R φ r grid (fun z=>value (p z)-value (q z))‖≤
      ∑z:domain,‖mass₀ z.val‖*∑s:Faces,‖bill (p z) (q z) s‖*fee z s:=by
  rw [exact_read]
  refine (norm_sum_le _ _).trans (sum_le_sum fun z _=>?_ )
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (sum_le_sum fun s _=>?_)) (norm_nonneg _)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (paid z s) (norm_nonneg _)

theorem graded (p q:domain→Faces→ℂ){k τ:ℝ}(rp:0≤r)(two:2≤k)(positive:0≤τ)(small:τ≤1)(A B:ℕ)
    (low:∀z (s:Faces),s.Nonempty → r^(height ages s)*‖q z s‖≤k^(B+A*height ages s))
    (delta:∀z (s:Faces),s.Nonempty → r^(height ages s)*‖p z s-q z s‖≤k^(B+A*height ages s)*τ):
    r^14*‖signed R φ r grid (fun z=>value (p z)-value (q z))‖≤
      (∫y,‖φ y‖)*(21*k^(3*(B+1)+A*14)*τ):=by
  let d:domain→ℂ:=fun z=>value (p z)-value (q z)
  have cap:=WilsonReceivedChronologicalFixedRoseVariation.original R φ r grid
    (fun z=>(r:ℂ)^14*d z) (21*k^(3*(B+1)+A*14)*τ) (by positivity)
    (fun z=>by
      rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg rp]
      exact WilsonReceivedChronologicalFixedRoseGradeReturn.original (p z) (q z) rp two positive small A B (low z) (delta z))
  have separate:signed R φ r grid (fun z=>(r:ℂ)^14*d z)=(r:ℂ)^14*signed R φ r grid d:=by
    unfold WilsonReceivedChronologicalFixedRoseVariation.signed
    rw [mul_sum]
    exact sum_congr rfl fun z _=>by ring
  rw [separate,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg rp] at cap
  exact cap

end YM.Integration.WilsonReceivedChronologicalFixedRoseTestProducts
end
