import YM.Integration.WilsonFullFaceSignedCapture
import YM.Integration.WilsonFullFacePooledUnit

/-! A signed linear extraction of an entire actual three-source gallery. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonGeometricSignedCapture
open Finset Lattice RG Wilson Marker Multi QuadraticLocal Ac Source Labels Extra.Histories
open Push.Local Planned.GuardedAtom WilsonThermometerCenteredAlgebra
open WilsonCenteredFiledAtoms WilsonRootedKioskOccupiedSlip
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {d : ℕ} {F : Frame G d} {P : Rep G n}
local notation "J" => Stock.census (Fin 3)

def take (c : (J).Mode → ℂ) (M : Poly J) : ℂ := ∑ s, c s * M.part s
def weightBill (c : (J).Mode → ℂ) (w : Fin 3 → ℝ) : ℝ := ∑ s, ‖c s‖ / Poly.toll w s

theorem pooled (S : SectionData F) (Y : Hol G) (y : Site n) {κ σ C Λ δ v μ : ℝ}
    (div : 0 < κ) (law : P.Lawful σ C Λ δ v) (reader : Readable Y S P.p n μ)
    (c : (J).Mode → ℂ) (M L : Config G n → Poly J) (fee : (J).Mode → ℝ)
    (faces : ∀ s : (J).Mode, Store P S Y y κ (fee s) (fun U => (M U).part s - (P.eval U:ℂ)*(L U).part s)) :
    ∃ h : Coefficient F n, h.Format y Y P ∧ h.remBound y P κ (∑ s, ‖c s‖ * fee s) ∧
      (∀ U, h.density y S P U = take c (M U) - (P.eval U:ℂ)*take c (L U)) ∧
      ∀ a : Probe G d, a.2.val = 0 → runProbe F a h.x =
        (P.eval (1:Config G n):ℂ)⁻¹ * (take c (M 1) - (P.eval (1:Config G n):ℂ)*take c (L 1)) := by
  obtain ⟨h,fmt,bill,pub⟩ := WilsonFullFaceSignedHard.collect (univ : Finset (J).Mode) S Y y div law _ _
    (fun s _ => WilsonFullFaceSignedInterpolation.painted S Y y (c s) (faces s))
  have field U : h.density y S P U = take c (M U) - (P.eval U:ℂ)*take c (L U) := by
    rw [pub,take,take,mul_sum,←sum_sub_distrib]
    exact sum_congr rfl fun s _ => by ring
  exact ⟨h,fmt,bill,field,fun a flat => (WilsonCenteredDetectorUnit.flatProbe h fmt reader.sound a flat).trans
    (congrArg (fun t => (P.eval (1:Config G n):ℂ)⁻¹*t) (field 1))⟩

variable {X ι ν : Type} {o : Fin 3 → Site n}

theorem scalar (L : Lamps X ι G P.p o J) (B : Lamps X ν G P.p o J) (H : Hard X P.p P.activities.forced P.activities.K o J)
    (w : Fin 3 → ℝ) (hw : ∀ j, 0 < w j) {C e : ℝ} (ep : 0 < e) (low : e ≤ 1) (cpos : 0 ≤ C)
    (model : L.Paid w P.p.B (P.p.supportExponent+2) C) (debt : B.Paid w P.p.B (P.p.supportExponent+2) e)
    (x : X) (c : (J).Mode → ℂ) :
    let A : Gallery X (ι⊕ν) o P J := ⟨L.join B,H⟩
    let t : ℂ := (P.eval (1:Config G n):ℂ)
    ‖t⁻¹ * (take c (A.density x 1) - t*take c (Poly.pass (bare L x 1)))‖ ≤
      weightBill c w * (e * WilsonFullFaceSignedPower.inter * ((Fintype.card (parts (J)).Mode:ℝ)*(C+3)^3)) := by
  intro A t
  let d (s : (J).Mode) := t⁻¹ * ((A.density x 1).part s - t*(Poly.pass (bare L x 1)).part s)
  have field : t⁻¹ * (take c (A.density x 1) - t*take c (Poly.pass (bare L x 1))) = ∑ s, c s * d s := by
    rw [take,take,mul_sum,←sum_sub_distrib,mul_sum]
    exact sum_congr rfl fun s _ => by dsimp [d]; ring
  let K := e*WilsonFullFaceSignedPower.inter*((Fintype.card (parts (J)).Mode:ℝ)*(C+3)^3)
  have per (s : (J).Mode) : ‖d s‖ ≤ K / Poly.toll w s := (le_div_iff₀ (Poly.worth hw s)).mpr
    ((mul_comm ‖d s‖ (Poly.toll w s)).le.trans (WilsonFullFaceSignedUnit.priced L B H w hw ep low cpos model debt x s))
  rw [field]
  calc
    _ ≤ ∑ s, ‖c s * d s‖ := norm_sum_le ..
    _ ≤ ∑ s, (‖c s‖/Poly.toll w s)*K := sum_le_sum fun s _ => by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (per s) (norm_nonneg _)).trans_eq (by ring)
    _ = _ := (sum_mul ..).symm

end YM.Integration.WilsonGeometricSignedCapture
