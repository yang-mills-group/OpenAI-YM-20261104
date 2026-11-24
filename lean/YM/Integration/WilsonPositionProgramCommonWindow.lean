import YM.Integration.WilsonPositionProgramElection
import YM.FVA2.Register.Pressroom

/-! The common inversion grid for a finite copy of the original variable blocking sequence. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramCommonWindow
open Filter Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open Push.PriceCompiler
open scoped BigOperators Classical Topology
variable {G : Gauge} (C : Run G) {simple : G.Simple} {a : Axis} {ε : ℝ}

/-- The selected physical run's actual blocks inherit the pre-period choice. -/
theorem blocks (purchase : WilsonPositionProgramElection.course simple a ε C.kit) (d : ℕ)
    (hd : 0 < d) : ∀ᶠ m in atTop, ∃ u : ℕ, C.family.S.block m = ((3:Side)^d)^u := by
  have h := WilsonPositionProgramLengths.eventual purchase.2 hd
  have dates := C.alloy.B.a.fits.deep.comp (tendsto_add_atTop_nat 1)
  filter_upwards [dates.eventually h] with m hm
  obtain ⟨u,hu⟩ := hm
  exact ⟨u,(block_eq C.alloy.B.valid m).trans hu⟩

variable (D : XSpace.Run)
/-- At a sufficiently fine reporter each actual finer block has an integer exponent in the given fixed regulator. -/
theorem dates (purchase : WilsonPositionProgramElection.course simple a ε C.kit) {d : ℕ}
    (hd : 0 < d) (hr : D.ratio = 3^d) : ∀ᶠ m in atTop, ∃ w : ℕ → ℕ,
      ∀ j : ℕ, (C.family.S.block (m+j)).val = D.ratio ^ w j := by
  obtain ⟨m₀,all⟩ := eventually_atTop.1 (blocks C purchase d hd)
  filter_upwards [eventually_ge_atTop m₀] with m hm
  have each (j : ℕ) := all (m+j) (hm.trans (Nat.le_add_right m j))
  choose w hw using each
  refine ⟨w,fun j => ?_⟩
  rw [hw,hr,PNat.pow_coe,PNat.pow_coe]
  rfl

def elapsed (w : ℕ → ℕ) (j : ℕ) : ℕ := ∑ k ∈ Finset.range j, w k

/-- These are the successive original dates after the reporting site, expressed in the one fixed-block grid. -/
theorem spacing (m : ℕ) (w : ℕ → ℕ) (b : ∀ j, (C.family.S.block (m+j)).val = D.ratio^w j)
    (j : ℕ) : C.family.S.a (m+j) = C.family.S.a m / D.den (elapsed w j) := by
  induction j with
  | zero => simp [elapsed,XSpace.Run.den]
  | succ j ih =>
    rw [←Nat.add_assoc,C.family.S.a_step,ih,b,Nat.cast_pow]
    simp only [elapsed,Finset.sum_range_succ,XSpace.Run.den,pow_add,Nat.cast_mul,Nat.cast_pow]
    exact div_div ..

/-- At fixed top `j`, reproduce every actual physical block ratio on the auxiliary period. -/
def side (w : ℕ → ℕ) (j k : ℕ) : Side := D.finalSide.side *
  ⟨D.den (D.reserve*(elapsed w j)*(elapsed w j) + elapsed w k),D.den_pos _⟩

theorem edge (m : ℕ) (w : ℕ → ℕ) (b : ∀ k, (C.family.S.block (m+k)).val = D.ratio^w k)
    (j k : ℕ) : (side D w j (k+1)).val = (side D w j k).val * (C.family.S.block (m+k)).val := by
  rw [b]
  change D.finalSide.side.val * D.den (D.reserve*elapsed w j*elapsed w j+elapsed w (k+1)) =
    D.finalSide.side.val * D.den (D.reserve*elapsed w j*elapsed w j+elapsed w k)*D.ratio^w k
  rw [show elapsed w (k+1)=elapsed w k+w k from Finset.sum_range_succ ..,←Nat.add_assoc]
  simp only [XSpace.Run.den,pow_add,Nat.mul_assoc]

theorem fine (w : ℕ → ℕ) (j : ℕ) : side D w j j = (D.step (elapsed w j)).p.side := by
  apply Subtype.ext
  change D.finalSide.side.val * D.den (D.reserve*(elapsed w j)*(elapsed w j)+elapsed w j) =
    D.finalSide.side.val * D.den (elapsed w j+D.reserve*(elapsed w j)*(elapsed w j))
  rw [Nat.add_comm]

/-- Exactly the fixed regulator's deployed fine spacing, retaining both actual physical dates. -/
theorem fine_spacing (m : ℕ) (w : ℕ → ℕ) (b : ∀ k, (C.family.S.block (m+k)).val = D.ratio^w k)
    (j : ℕ) : C.family.S.a (m+j) / C.family.S.a m = (D.step (elapsed w j)).spacing := by
  rw [spacing C D m w b]
  change _ / _ / _ = ((D.den (elapsed w j):ℝ))⁻¹
  field_simp [(C.family.S.a_pos m).ne',(Nat.cast_pos.mpr (D.den_pos (elapsed w j)) : 0 < (D.den (elapsed w j):ℝ)).ne']

end YM.Integration.WilsonPositionProgramCommonWindow
end
