import YM.Extra.FREE_DETECTOR_ALGEBRA.Filtrate
import YM.FiniteVolumeClosure.A0bCompat.FDColor

set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD
open Function Set Filter Tensor Analysis Maxwell Wick Labels
open scoped Topology ContDiff BigOperators RealInnerProductSpace

variable {G : Gauge} {j d : ℕ}

theorem past_sector (p : WickPol G) : p∈shellSector G d ↔ p∈through G d ∧ secret p := by
  classical
  let a (i : Labels.Key G) := Labels.generation i
  let b (i : Slot G) := costKey i
  constructor
  · rintro ⟨v,rfl⟩
    change reduceEq v.val∈_ ∧ _
    refine ⟨filterMove a b reduceEq (gradientReduce (·+2)) (show v.val∈byWeight a (Iic d) from v.property.1), fun u V => ?_⟩
    change probe (stain u V) (reduceEq v.val)=probe V (reduceEq v.val)
    rw [jet_value,jet_value,show (fun i => gaugeJet (G:=G) (stain u V i))=Labels.colored u (fun i => gaugeJet (V i)) from
      funext fun i => radial_color ..]; exact v.property.2 _ u
  rintro ⟨hp,hp'⟩
  have he : writeRaw p∈limited G d := filterMove b a writeRaw (gradientWrite (·+2)) (show p∈byWeight b _ from hp)
  have ht : writeRaw p∈invariantSpace G := by
    intro J u; rw [writeRaw_read,writeRaw_read,show reroute (colored u J)=stain u (reroute J) from funext fun i => send_color (j:=i) u (J i)]
    exact hp' u _
  exact ⟨⟨writeRaw p,he,ht⟩,writeRaw_after p⟩
end YM.Extra.FD
