import YM.Integration.WilsonFirstReceivedGalleryRegular
import YM.QuadraticLocal.Campaign.Reach
import YM.Comparison.RG02.Order.Pay

noncomputable section
namespace YM.Integration.WilsonFirstReceivedGalleryNodes

open Finset Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Tint
open Comparison.RG02 Order Extra.Trajectories Primitives.GCC.Anchor Multi
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {V T ι J : Type} [DecidableEq V] [Fintype V]
variable {P : Passport n V} {R : Census V} {U : RG.Rep G n}
variable (X : ι → Row P R G T) (Y : Tint.Incoming P U T J R) {w : V → ℝ}
variable {g a b : ℝ}

/-- On a clean real probe the exact physical report has only the enrolled old regular
discrepancy against its full analytic roster. The latter retains every marked constant. -/
theorem original (ha : 0 ≤ a) (hw : ∀v, 0<w v)
    (rent : Y.old.Paid w U.p.B a b) (t : T) (W : Config G n)
    (hW : flags U.p.threshold W = ∅)
    (issued : Summable fun i => (rendered X U.p g).frame i t W)
    (s : R.Mode) (v : V) (hv : v∈s.val) :
    let A := Patrol.report X Y g
    let report := Order.logTo (Fintype.card V) (((U.eval W:ℂ)⁻¹) • A.density t W)
    report = (rendered X U.p g).log t W + Y.old.log t W ∧
      Poly.toll w s * ‖(report-(rendered X U.p g).log t W).part s‖ ≤ b := by
  dsimp only
  let A := Patrol.report X Y g
  let L := rendered X U.p g
  have regular := rent.sums ha hw t W
  have both : Summable fun i=>A.E.frame i t W := issued.sum (f:=fun i=>A.E.frame i t W) regular
  have vacuum : (U.eval W:ℂ)=(Real.exp (U.exponent W):ℂ) := by
    simp [Rep.eval,U.activities.gas_one U.p hW]
  have normed : (((U.eval W:ℂ)⁻¹) • A.density t W) = Poly.pass (A.E.log t W) := by
    rw [Gallery.density,WilsonFirstReceivedGalleryRegular.clear A t W hW,mul_one,vacuum,
      smul_smul,inv_mul_cancel₀ (by exact_mod_cast (Real.exp_ne_zero (U.exponent W))),one_smul]
  have hnil := Lamps.quiet_of_hasSum t W both
  have filed : Order.logTo (Fintype.card V) (((U.eval W:ℂ)⁻¹) • A.density t W) =
      L.log t W + Y.old.log t W := by
    rw [normed,← Order.log_to _ (Poly.pass_part _ hnil) _ (fun s => card_le_univ _),
      connected_pass hnil]
    exact Lamps.joinLog t W issued regular
  refine ⟨filed,?_⟩
  change Poly.toll w s * ‖(Order.logTo _ (((U.eval W:ℂ)⁻¹) • A.density t W)-L.log t W).part s‖ ≤ b
  rw [filed,add_sub_cancel_left]
  exact WilsonFirstReceivedGalleryRegular.occupied Y.old rent ha hw t W s v hv

end YM.Integration.WilsonFirstReceivedGalleryNodes
end
