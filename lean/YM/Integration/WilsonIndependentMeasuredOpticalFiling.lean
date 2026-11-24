import YM.Integration.WilsonIndependentMeasuredOpticalDose
import YM.Integration.WilsonIndependentMeasuredOpticalWindow

/-! All restored rows of a recorded original panel, on its own board and
through its original issued matrices at every physical cutoff. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentMeasuredOpticalFiling
open Filter Lattice RG Source Labels PhysicalNext.Repeat.Legato
open WilsonIndependentRawPhysicalFaces (weight)
open WilsonThermometerPositionTunedSlope (Columns)
open WilsonPhysicalOrientedStencilPin (coordinates)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonMeasuredPublicEntrancePanel (Panel)
open WilsonIndependentMeasuredOpticalWindow (Slot)
open WilsonIndependentMeasuredOpticalDose (fare)
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) (V:XSpace.Run)
def AllFaces (f K i seats power q:ℕ) (B:ℝ) : Prop :=
    ∀n:ℕ,n ≤ seats → ∀(d:Fin n→ℕ)(s:Finset (Fin n))(N per:ℕ)(fk:f ≤ K)(kn:K ≤ N)
      (file:Filed R d K)(request age:ℕ)(A:Panel R d N per f K fk kn request power age B),
      A.slot=file.station → A.axis=file.A N per →
      let δ := fun j:s=>d j
      let row:=coordinates R d (N:=N) (per:=per) file A.names A.turn
      (∑a:Columns R δ,‖weight R d row s a‖ ≤ fare R d s power B*(V.den i:ℝ)^(power*s.card)) ∧
      ∀(k:ℕ)(C:ℝ),0 ≤ C → ∀Y:Columns R δ→ℂ,
        (∀a,‖Y a‖ ≤ C*(1+Real.log ((V.step i).p.side.val:ℝ))^k*((V.step i).p.side.val:ℝ)^(-(1/4:ℝ))) →
        ‖∑a:Columns R δ,weight R d row s a*Y a‖ ≤ 
          (fare R d s power B*C*(1+8*((k:ℝ)+1))^k)*(R.family.S.a K/R.family.S.a f)^q

theorem original (simple:G.Simple) {f K i seats power q:ℕ} (entry:Slot R V f K i)
    (late:8*(power*seats+q) ≤ i) (B:ℝ) (positive:0 ≤ B):AllFaces R V f K i seats power q B := by
  intro n size d s N per fk kn file request age A station axes δ row
  have card : s.card ≤ n := s.card_le_univ.trans_eq (Fintype.card_fin n)
  have room := (Nat.mul_le_mul_left 8 (Nat.add_le_add_right (Nat.mul_le_mul_left power (card.trans size)) q)).trans late
  refine ⟨WilsonIndependentMeasuredOpticalDose.original R V d s file A station axes positive entry.restored,?_⟩
  intro k C cap Y paid
  rw [entry.spacing]
  exact WilsonIndependentMeasuredOpticalDose.signed R simple V d s file A station axes positive entry.restored room C cap Y paid

end YM.Integration.WilsonIndependentMeasuredOpticalFiling
