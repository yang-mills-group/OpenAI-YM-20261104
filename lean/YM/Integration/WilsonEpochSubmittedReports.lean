import YM.Integration.WilsonEpochClosedSource
import YM.Integration.WilsonEpochMeshTransport

/-! Natural reports on the original physical mesh, directly assembled from
its ultraviolet open graph. Both the unposted array and the signed
one-source telescope are linear in the test and multilinear in all marks. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonEpochSubmittedReports
open Function Lattice XSpace XSpace.Structure1 XSpace.Normalize XSpace.Cirrus
open FVA2 FVA2.Register FVA2.Arrival FormalBulk08.Flat
open WilsonEpochPositionCoefficients WilsonEpochMeshTransport
open scoped Classical BigOperators
variable {G : Gauge}
abbrev Fields := List (Folio G) → PowerSeries ℝ

private def functional (m : Mesh) {n d : ℕ} (k : ℕ) (t : Fin n → Dframe.Toon G d)
    (b : Fields (G:=G)) : Test n →ₗ[ℂ] ℂ :=
  (m.spacing:ℂ)^(4*n) • ∑ x : Fin n → m.Sites,
    PowerSeries.coeff k (WilsonEpochMeshTransport.position m t (lift ∘ x) b) • m.smear (lift ∘ x)

private theorem evaluated (m : Mesh) {n d : ℕ} (k : ℕ) (t : Fin n → Dframe.Toon G d)
    (b : Fields (G:=G)) (a : Test n) :
    functional m k t b a = PowerSeries.coeff k (sweep m t a b) := by
  simp only [functional,sweep,LinearMap.smul_apply,LinearMap.sum_apply,map_smul,map_sum,smul_eq_mul]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

def report (m : Mesh) (d : ℕ) (b : Fields (G:=G)) : Reports G d :=
  fun k n => ∑ t : Fin n → Dframe.Toon G d, (functional m k t b).smulRight (Dframe.each t)

theorem pay (m : Mesh) (d : ℕ) (b : Fields (G:=G))
    (k n : ℕ) (a : Test n) (p : Tags G d n) :
    report m d b k n a p = readBatch m n d k a p b := by
  simp only [report,readBatch,LinearMap.sum_apply,LinearMap.smulRight_apply,
    _root_.sum_apply,_root_.smul_apply,smul_eq_mul,evaluated]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

variable (R : PhysicalNext.Repeat.Legato.Run G)
variable (L : ∀ i, Lodge ((R.family.path.levels.clock.op i 0).patch))
variable (α : G.ColorIndex)

def graph (Y : Initialize G) (N per D : ℕ) : Fields (G:=G) :=
  fun l => PowerSeries.mk fun k =>
    (PowerSeries.coeff k (WilsonEpochClosedSource.submitted R L α Y N per D l)).re

theorem actual_field (Y : Initialize G) (N per D : ℕ) :
    graph R L α Y N per D = actual R Y (R.family.side N per) := by
  funext l
  apply PowerSeries.ext
  intro k
  simp only [graph,PowerSeries.coeff_mk,WilsonEpochClosedSource.closed,
    FormalOPE.RG10.InversionTop.into_coeff,Complex.ofReal_re]

theorem all_orders (Y : Initialize G) (N per D d : ℕ) :
    let m := mesh R N per
    report m d (graph R L α Y N per D) =
      XSpace.Normalize.batch Y m d + report m d (residual R Y m.p.side) := by
  intro m
  rw [actual_field]
  funext k n
  apply LinearMap.ext
  intro a
  apply MultilinearMap.ext
  intro p
  change report m d (actual R Y m.p.side) k n a p = XSpace.Normalize.batch Y m d k n a p +
    report m d (residual R Y m.p.side) k n a p
  rw [pay,pay]
  exact (comparison R Y m n d k (fun _=>0) a p).2

def publish {d : ℕ} (ν : ℝ) (S : MS.Land.Prescription (Press.portDeck G))
    (m : Mesh) (f : Reports G d) : Reports G d :=
  realm (Dframe.D ν S m d) (MS.Book.Program.substitute (Dframe.reset ν S m) f)

private theorem publish_sum {d : ℕ} (ν : ℝ) (S : MS.Land.Prescription (Press.portDeck G))
    (m : Mesh) (f g : Reports G d) : publish ν S m (f+g) = publish ν S m f + publish ν S m g := by
  unfold publish
  rw [map_add]
  funext k n
  apply LinearMap.ext
  intro a
  apply MultilinearMap.ext
  intro p
  simp only [Pi.add_apply,LinearMap.add_apply,_root_.add_apply,really,Finset.sum_add_distrib]

/-- Every entry of the independently deposited D matrix and time
substitution acts on the *signed difference*, before norms. -/
theorem posted (Y : Initialize G) (S : MS.Land.Prescription (Press.portDeck G))
    (ν : ℝ) (N per D d : ℕ) :
    let m := mesh R N per
    publish ν S m (report m d (graph R L α Y N per D)) =
      Reg.Pivot.posted ν Y S d m + publish ν S m (report m d (residual R Y m.p.side)) := by
  intro m
  rw [all_orders,publish_sum]
  rfl

end YM.Integration.WilsonEpochSubmittedReports
end
