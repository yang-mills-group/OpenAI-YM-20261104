import YM.Integration.WilsonSeparatedPositionCameras
import YM.Spec.Closed

/-! Changing a Euclidean camera rotates the actual quotient fields and rearranges
them together with the positions in the same unselected physical table. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedPhysicalCameraChange
open Function Filter Set Extraction Spec Table WilsonSeparatedPositionCameras
open scoped Topology Classical
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) {n : ℕ} {d : Fin n → ℕ}

def field (g : Ortho) (σ : Equiv.Perm (Fin n)) (v : ∀ i,S.Field (d i)) (i : Fin n) : S.Field (d (σ i)) :=
  F.sector.turns.act (d (σ i)) g (v (σ i))

theorem at_point (g : Ortho) (σ : Equiv.Perm (Fin n)) (v : ∀ i,S.Field (d i))
    {x : Points n} (hx : x∈conf n) {r : ℝ} (hr : 0<r) :
    S.classMoment S (fun i=>d (σ i)) (r • view g σ x) (field F g σ v) = S.classMoment S d (r • x) v := by
  let w (i : Fin n) : S.Tag := ⟨d i,v i⟩
  have clear : r • x∈conf n := by
    intro i j eq
    have e : r • x i = r • x j := eq
    have back := congrArg (fun a : E4 => r⁻¹ • a) e
    apply hx
    simpa only [← mul_smul,inv_mul_cancel₀ hr.ne',one_smul] using back
  have rotated := F.phase.transport.motion n w _ clear g
  have swapped := S.class_perm S F.room.kernel.laws.toSymmetric σ (Points.move_in g clear)
    (F.sector.turns.label g ∘ w)
  have rescale : r • view g σ x = Points.rearrange σ (Points.move g (r • x)) := by
    apply PiLp.ext
    intro i
    exact ((Ortho.motion g).map_smul r (x (σ i))).symm
  rw [rescale]
  exact swapped.trans rotated

theorem along (g : Ortho) (σ : Equiv.Perm (Fin n)) (v : ∀ i,S.Field (d i))
    {x : Points n} (hx : x∈conf n) (u : Points n) {r : ℝ} (hr : 0<r) :
    (fun t : ℝ=>S.classMoment S d (r • (x+t • u)) v) =ᶠ[𝓝 0]
      fun t : ℝ=> S.classMoment S (fun i=>d (σ i)) (r • (view g σ x+t • view g σ u)) (field F g σ v) := by
  have c : Continuous (fun t : ℝ=>x+t • u) := by fun_prop
  have open_at : x+(0:ℝ) • u ∈ conf n := by simpa only [zero_smul,add_zero] using hx
  filter_upwards [c.continuousAt.eventually ((conf_open n).mem_nhds open_at)] with t ht
  rw [← WilsonSeparatedPositionCameras.line]
  exact (at_point F g σ v ht hr).symm

end YM.Integration.WilsonSeparatedPhysicalCameraChange
