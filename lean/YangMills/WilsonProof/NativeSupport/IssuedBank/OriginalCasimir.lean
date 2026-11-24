import YangMills.WilsonProof.NativeSupport.WilsonBridge
import YangMills.WilsonProof.NativeSupport.WilsonLatticeData

set_option autoImplicit false

namespace IssuedBank.OriginalCasimir

open YangMills YangMills.Wilson
open scoped InnerProductSpace
noncomputable section

variable {g : GaugeGroup} (B : Maxwell.Reference g)

def bracket (x y : Maxwell.Color B.m) := B.matrix x * B.matrix y - B.matrix y * B.matrix x

theorem trace (x y : Maxwell.Color B.m) :
    ∃ z : Maxwell.Color B.m, B.matrix z = bracket B x y ∧
    -((bracket B x y * bracket B x y).trace).re = ((g.n+1 : ℕ) : ℝ) * ‖z‖ ^ 2 := by
  have entered (c : Maxwell.Color B.m) : B.matrix c ∈ g.lieAlgebra := by
    rw [← B.colors]
    exact ⟨c, rfl⟩
  have closed : bracket B x y ∈ g.lieAlgebra :=
    (g.generates _).2 (g.core.bracket_mem ((g.generates _).1 (entered x)) ((g.generates _).1 (entered y)))
  rw [← B.colors] at closed
  obtain ⟨z, hz⟩ := closed
  refine ⟨z, hz, ?_⟩
  rw [← hz, B.traceForm, real_inner_self_eq_norm_sq]

theorem nonnegative (x y : Maxwell.Color B.m) :
    0 ≤ -((bracket B x y * bracket B x y).trace).re := by
  obtain ⟨z, _, e⟩ := trace B x y
  rw [e]
  positivity

theorem positiveOn (x y : Maxwell.Color B.m) (physical : bracket B x y ≠ 0) :
    0 < -((bracket B x y * bracket B x y).trace).re := by
  obtain ⟨z, hz, e⟩ := trace B x y
  have nz : z ≠ 0 := by
    intro h
    exact physical (hz.symm.trans (h ▸ map_zero B.matrix))
  rw [e]
  exact mul_pos (by positivity) (pow_pos (norm_pos_iff.mpr nz) 2)


end
end IssuedBank.OriginalCasimir
