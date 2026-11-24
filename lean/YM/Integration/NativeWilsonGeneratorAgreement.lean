import YM.Comparison.RG02.Bulk.Fk
import YM.Integration.LocalFormalCoefficients

/-! Finite-order vacuum replacement in the original Wick prescription for arbitrary unchanged marks. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeWilsonGeneratorAgreement
open Function Filter Finset RG Precision Lattice Wilson Exterior Tree
open Comparison.RG02 Comparison.RG02.Bulk Comparison.RG02.Assembly
open Next.SectorChange PertExtension.Series Multi Marker Comparison.RG02.Order
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip} {P : PathData G}
    {O : ChartRatio G} {V : Type} [DecidableEq V] [Fintype V] {H : Census V}
    (K : Bulk.Kernel S p P O) (F : Forest S.ratio) (t : S.Choices)
    (W : Bulk.Colors H G f) (vac : ℝ → Config G f → ℝ)

def replaceVacuum (W : Bulk.Colors H G f) (vac : ℝ → Config G f → ℝ) : Bulk.Colors H G f :=
  { W with vac := vac }

local notation "W₁" => replaceVacuum W vac

/-- A vacuum generator of perturbative degree j has genuine derivative order j+2. -/
theorem raw (x : fieldDir G c 1) (r : ℕ)
    (hj : ∀ k, k ≤ r+2 → iteratedFDeriv ℝ k (Bulk.geometric K F t W) 0 =
      iteratedFDeriv ℝ k (Bulk.geometric K F t W₁) 0) :
    Bulk.Fk K F t W x r = Bulk.Fk K F t W₁ x r := by
  have gen (s : Hot (Board H r)) :
      Assembly.generator (Bulk.stage K F x) (Bulk.hinge F) W.power (Bulk.markFn S F W)
        (Bulk.geometric K F t W) r s =
      Assembly.generator (Bulk.stage K F x) (Bulk.hinge F) (W₁).power (Bulk.markFn S F W₁)
        (Bulk.geometric K F t W₁) r s := by
    have hk := Order.order_limit r (Join.right s.val)
    unfold Assembly.generator
    dsimp only
    by_cases he : (Join.left s.val).val.Nonempty
    · simp only [dif_pos he]
      rfl
    · simp only [dif_neg he,Assembly.naked,hj _ (Nat.add_le_add_right hk 2)]
  unfold Bulk.Fk Assembly.prescription
  rw [funext gen]

theorem of_grade (x : fieldDir G c 1) (r : ℕ) (hw : Bulk.Well W) (hv : Bulk.Well W₁)
    (h : GradeAt (r+3) (Bulk.projected (fun g U => W.vac g U - vac g U))) :
    Bulk.Fk K F t W x r = Bulk.Fk K F t W₁ x r := by
  apply raw K F t W vac x r
  have hrest := Bulk.joint_receipt S F h
  have hid : (fun z => Bulk.geometric K F t W z - Bulk.geometric K F t W₁ z) =
      Bulk.posed S F (fun g U => W.vac g U - vac g U) := by
    funext z
    dsimp [Bulk.geometric,Bulk.fee,Bulk.supplement,Bulk.posed,replaceVacuum]
    ring
  have h0 : GradeAt (r+3) (fun z => Bulk.geometric K F t W z - Bulk.geometric K F t W₁ z) :=
    hid.symm ▸ hrest
  intro k hk
  have hj := h0.vanish k (by omega)
  have ha : ContDiffAt ℝ k (Bulk.geometric K F t W) 0 :=
    ((Bulk.stone_smooth K F t).add (Bulk.fee_starts K F W hw).smooth).of_le le_top
  have hb : ContDiffAt ℝ k (Bulk.geometric K F t W₁) 0 :=
    ((Bulk.stone_smooth K F t).add (Bulk.fee_starts K F W₁ hv).smooth).of_le le_top
  change iteratedFDeriv ℝ k (Bulk.geometric K F t W - Bulk.geometric K F t W₁) 0 = 0 at hj
  rw [iteratedFDeriv_sub_apply ha hb] at hj
  exact sub_eq_zero.mp hj

end YM.Integration.NativeWilsonGeneratorAgreement
end
