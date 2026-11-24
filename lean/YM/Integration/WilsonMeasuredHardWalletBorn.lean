import YM.Integration.WilsonMeasuredSingletonForce
import YM.Integration.WilsonPhysicalHistoryGroupedGas

/-! Absolute convergence at each original field follows from the elected hard wallet.
This issues the signed singleton coefficient on the given original gallery. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredHardWalletBorn
open Finset Lattice Wilson RG Source Labels Ac Marker Push GridApprox.Nil QuadraticLocal MergeProof MergeProof.Accent
open Extra.Histories Extra.Trajectories QuadraticLocal.Fusion.Attached WilsonPhysicalHistoryGroupedHard
open scoped BigOperators Classical
variable {G:Gauge} {n:Side} {V X:Type} [DecidableEq V] {J:Census V}
    {P:Rep G n} {o:V→Site n} (H:Hard X P.p P.activities.forced P.activities.K o J)
    (w:V→ℝ) (positive:∀ v,0<w v)

include positive

theorem summable {a cost:ℝ} (expo:0≤a) (wallet:H.Paid w P.p.B a cost)
    (x:X) (U:Config G n) : Summable (packet P.activities P.p (H.hard x) U) :=by
  have seen:=(stored P o H w positive univ expo wallet x).repair positive U
  have original:column P o H univ x=H.hard x :=by
    funext i W
    ext s
    change (if s∈(univ:Finset J.Mode) then _ else _)=_
    exact if_pos (mem_univ _)
  rw [original] at seen
  have summed:=summable_finsetProd_of_summable_nonneg (fun i=>Poly.nonnegative positive (H.hard x i U)) seen.1
  apply (Poly.budgeted positive summed ?_).1
  intro B
  unfold packet
  split
  · exact Poly.multiple positive _ _
  · simp only [Poly.zero_price]
    exact prod_nonneg fun _ _=>Poly.nonnegative positive _

theorem original {d:ℕ} {F:Frame G d} (S:SectionData F) (Y:Hol G) (x:X) (v:V)
    {κ M:ℝ} (hk:0<κ) (hn:0≤M) (wallet:H.Paid w P.p.B P.p.supportExponent (κ*M)) :
    let h:=WilsonMeasuredSingletonForce.row (F:=F) H x v
    h.Format (o v) Y P ∧ h.remBound (o v) P κ ((w v)⁻¹*M) ∧ h.x=0 ∧ h.regular=0 ∧
      (∀i U,h.forced i U=(H.hard x i U).part (J.fire v)) ∧
      ∀U,h.density (o v) S P U=(Real.exp (P.exponent U):ℂ)*(WilsonCenteredAbsoluteHard.gas H x U).part (J.fire v) := by
  exact ⟨WilsonMeasuredSingletonForce.format H x v Y,WilsonMeasuredSingletonForce.restored H x v w positive hk hn wallet,
    rfl,rfl,fun _ _=>rfl,fun U=>WilsonMeasuredSingletonForce.density H x v S U
      (summable H w positive P.p.exponent_pos.le wallet x U)⟩

end YM.Integration.WilsonMeasuredHardWalletBorn
