import YM.Integration.WilsonPhysicalMarkedDefectStoredInterior
import YM.Extra.MULTISOURCE_BOUNDS.Columns

/-! Charge the current dressed section of the *same* stored coefficient,
with the legal rooted angular directions on its native healthy footprint.
On failed configurations the finite physical section has a different,
explicit price in the measured coupling. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalMarkedDefect.InteriorSection
open Function Finset Lattice Wilson RG Source Labels Cells
open Extra.Histories Extra.Multi Pert.Asymptotics RG16.Literal Trace.Physical.GermGraph
open StoredInterior
open scoped Classical BigOperators

variable {G : Gauge} (C : Family G) (N p h b : ℕ)
local notation "F" => (C.labels.level h)
local notation "A" => (C.path.rep N p b)
local notation "S" => (C.localSection h)
local notation "X" => (SectionData.footprint (C.localSection h) (0 : Site (C.side b p)))
local notation "g" => regulatorRun C N p b

theorem chart (law : C.Makes) (ref : C.ref h ≤ b) (hb : b ≤ N)
    (Q : store C h p b) {fee : ℝ} (cost : (F).coeffSize Q.x ≤ fee) :
    (A).p.Regular X (fitted C N p h b Q) ∧
    (A).p.supBounds 0 X (fitted C N p h b Q) ((C.path.levels.params b).columns * fee) := by
  let c := (C.path.levels.params b).columns
  have pEq := (law.wilson.represents N p b hb).vac
  have prep : ∀ i : (F).Index, (A).p.Regular X ((S).places (Pi.single i 1) 0) ∧
      (A).p.supBounds 0 X ((S).places (Pi.single i 1) 0) (c * (A).p.threshold^((F).grades i).2) := by
    rw [pEq]
    exact law.priced h b p ref 0
  have data := BasisCost.analytic (S) (A).p ((F).core Q.x) 0 prep
  have field : (S).places ((F).scaled (A).p.threshold⁻¹ ((F).core Q.x)) 0 = fitted C N p h b Q :=
    funext (primary C N p h b law hb Q)
  rw [field] at data
  have pos : 0 ≤ c := (mul_nonneg_iff_of_pos_right (pow_pos (A).p.threshold_pos _)).1 (prep 0).2.1
  have le := mul_le_mul_of_nonneg_left ((StoredInterior.core_le C h Q.x).trans cost) pos
  exact ⟨data.1,data.2.1.trans le,fun U hu l hl hd => (data.2.2 U hu l hl hd).trans le⟩

/-- The actual (not fitted) physical coupling is below 2 everywhere in the
legal Wilson band; no size estimate depends on the two torus regulators. -/
theorem coupling (law : C.Makes) (hb : b ≤ N) : regulatorRun C N p b ≤ 2 := by
  have band := (law.wilson.represents N p b hb).band.1
  have delayed := C.path.levels.fits.delayed b
  have positive := RG02.Actual.coupling_pos law.wilson (N:=N) (p:=p) hb
  let β := C.path.β N p b
  have sq := Real.sq_sqrt positive.le
  have pos := Real.sqrt_pos.mpr positive
  have low : (1:ℝ)/2 ≤ Real.sqrt β := by
    change 1/2 ≤ Real.sqrt (C.path.β N p b)
    nlinarith [band,delayed,Real.sqrt_nonneg (C.path.β N p b)]
  change (Real.sqrt β)⁻¹ ≤ 2
  rw [← one_div,div_le_iff₀ pos]
  linarith

def roughFee (fee : ℝ) : ℝ := BasisCost.price (S) * (g/2)⁻¹^(BasisCost.slots (F))*fee

theorem rough (law : C.Makes) (hb : b ≤ N) (Q : store C h p b)
    {fee : ℝ} (cost : (F).coeffSize Q.x ≤ fee) (U : Config G (C.side b p)) :
    ‖fitted C N p h b Q U‖ ≤ roughFee C N p h b fee := by
  have hg := g_pos law (N:=N) (p:=p) hb
  have ht := WilsonMasterCoordinatePrice.threshold law (N:=N) (p:=p) hb
  have room : g/2 ≤ (A).p.threshold := by
    have h := (div_le_iff₀ (A).p.threshold_pos).1 ht
    linarith
  rw [← primary C N p h b law hb Q U]
  exact (BasisCost.full_scaled (S) ((F).core Q.x) 0 (by positivity : 0 < g/2) room
    (by linarith [coupling C N p b law hb]) U).trans
    (mul_le_mul_of_nonneg_left ((StoredInterior.core_le C h Q.x).trans cost)
      (mul_nonneg (zero_le_one.trans (BasisCost.price_pos (S))) (by positivity)))

theorem failed (law : C.Makes) (hb : b ≤ N) (Q : store C h p b)
    {fee : ℝ} (cost : (F).coeffSize Q.x ≤ fee) (U : Config G (C.side b p)) :
    ‖StoredInterior.failed C N p h b Q U‖ ≤ if Healthy (A).p.threshold X U then 0 else roughFee C N p h b fee := by
  by_cases ok : Healthy (A).p.threshold X U
  · simp [StoredInterior.failed,ok]
  · simpa [StoredInterior.failed,ok] using rough C N p h b law hb Q cost U

end YM.Integration.WilsonPhysicalMarkedDefect.InteriorSection
