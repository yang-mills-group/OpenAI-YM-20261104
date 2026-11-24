import YM.Integration.WilsonEmittedRecordedField
import YM.Integration.WilsonEmittedRecordedJet

/-! Summability and the joint thermal/angular coefficient of the same emitted
group field, with the authentic Laurent shift on each proper subword. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionProgramEmittedPupil
open Finset Function Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise
open Comparison.RG02 Comparison.RG02.Bulk
open WilsonEmittedCutGrouping
open scoped BigOperators Classical
variable {G : Gauge} {n : Side} {V X ι : Type} [DecidableEq V]
variable {P : Passport n V} {Γ : Census V} (M : ι → Row P Γ G X)
    (x : X) (w : V→ℕ) {a : ℝ} {p : ℕ} (staff : Air.Staff M (fun i=>(M i).paint x) w a p)

include staff in
theorem paid (g : ℝ) (live : g≠0) (U : Config G n) : Summable (fun i => Spill.raw M g x i U) := by
  let q := fun i=>(M i).paint x
  let total := fun s : Γ.Mode => ∑' i, (Spill.raw M g x i U).part s
  refine ⟨Poly.inject total,Pi.hasSum.mpr (fun s=>?_)⟩
  change HasSum (fun i=>(Spill.raw M g x i U).part s) (∑' i,(Spill.raw M g x i U).part s)
  let d := Launch.index Γ w s+1
  let δ := ((g^d:ℝ):ℂ)⁻¹
  have ready := (Air.usable_all M q w staff U g (picked M s)).mul_left δ
  apply Summable.hasSum
  refine ready.congr (fun i=>?_)
  by_cases hit : picked M s i
  · let μ : ι→Prop := fun j=>i=j
    have same := WilsonEmittedRecordedField.value M x w staff s live μ (fun j h=>h ▸ hit) U
    have cover : (M i).nominal g x U = δ*ScatterR.familyAt M q i g U := by
      simpa [μ,Air.sums,δ,d,q] using same
    simpa only [if_pos hit,Spill.raw,Poly.part_send,if_pos (show s=(M i).mode from hit)] using cover.symm
  · simp only [if_neg hit,mul_zero,Spill.raw,Poly.part_send,if_neg (show s≠(M i).mode from hit)]

include staff in
theorem original (L : AllOrder.Floe.Layout G) (tape : Finset AllOrder.Floe.Age)
    (s : Multi.Hot Γ) (g : ℝ) (live : g≠0) :
    (∀ U, (Spill.Foundry.uncut M g x U).part s.val =
      ((g^(Launch.index Γ w s.val+1):ℝ):ℂ)⁻¹ *
        Air.sums M (fun i=>(M i).paint x) (picked M s.val) g U) ∧
    (∀ j A, Assembly.jet (WilsonEmittedRootCensus.field M (fun i=>(M i).paint x) (picked M s.val))
      (Launch.index Γ w s.val+1+j) (1,A) =
      (Air.discharge (Air.craft M (fun i=>(M i).paint x) w L tape) j
        (Stationary.arm G n 1 (WilsonCubicOriginalTorus.coordinates G n A))).part s.val) :=
  ⟨fun U=>WilsonEmittedRecordedField.uncut M x w staff s.val live U (paid M x w staff g live U),
    WilsonEmittedRecordedJet.original M x w staff L tape s⟩

end YM.Integration.WilsonPositionProgramEmittedPupil
