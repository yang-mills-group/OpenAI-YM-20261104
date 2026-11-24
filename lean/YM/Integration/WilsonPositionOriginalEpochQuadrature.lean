import YM.Integration.WilsonPositionRawEpoch

/-! Both field changes in the true independent raw epoch commute with its actual common-center
quadrature. Each child retains its own finite torus site and the measure of the original test. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalEpochQuadrature
open Filter Set Finset Function Maxwell XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open FVA2 FVA2.Register FVA2.Scale MS MS.Land PowerSeries Lattice
open WilsonPositionRawFiling WilsonPositionRawMesh WilsonPositionRawEpoch
open scoped BigOperators Classical Topology
variable {G : Gauge} {Z : WilsonPrescription G} {i B n : ℕ} (P : Handoff.Directory Z i B)
    (d : ℕ) (φ : Test n) (v : Fin n → Sec G d)
local notation "m" => Z.run.step i

def point (x : Fin n → Cover) (k : ℕ) : ℂ :=
  ∑ a∈tally k n,∑ t,Dframe.each t (pulseU a (matrix Z i d) v) * coeff (a none) (P.point_fk n d t x)

theorem row (k : ℕ) : WilsonPositionRawEpoch.row Z P d φ v k =
    ((m).spacing:ℂ)^(4*n)*∑ x : Fin n → (m).Sites,
      (m).smear (Lattice.lift ∘ x) φ*point P d v (Lattice.lift ∘ x) k := by
  unfold WilsonPositionRawEpoch.row point Handoff.Directory.sweep_fk
  simp only [_root_.map_smul,_root_.map_sum,smul_eq_mul,Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  calc
    _ = ∑ t,∑ x : Fin n → (m).Sites,∑ a∈tally k n,
        ((m).spacing:ℂ)^(4*n) * (((m).smear (Lattice.lift ∘ x) φ) *
        (Dframe.each t (pulseU a (matrix Z i d) v) * coeff (a none) (P.point_fk n d t (Lattice.lift ∘ x)))) := by
      apply sum_congr rfl; intro t _
      rw [Finset.sum_comm]
      apply sum_congr rfl; intro x _
      apply sum_congr rfl; intro a _
      ring
    _ = _ := by
      rw [Finset.sum_comm];apply sum_congr rfl;intro x _
      rw [Finset.sum_comm]

theorem whole (q : ℕ) (u : ℂ) :
    (∑ k∈range (q+1),WilsonPositionRawEpoch.row Z P d φ v k*u^k) =
    ((m).spacing:ℂ)^(4*n) * ∑ x : Fin n → (m).Sites,
      (m).smear (Lattice.lift ∘ x) φ *
      ∑ k∈range (q+1),point P d v (Lattice.lift ∘ x) k*u^k := by
  simp only [row P d φ v,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply sum_congr rfl; intro x _
  apply sum_congr rfl; intro k _
  ring

end YM.Integration.WilsonPositionOriginalEpochQuadrature
