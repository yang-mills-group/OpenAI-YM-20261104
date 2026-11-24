import YM.Integration.WilsonPositionProgramVariableCircuit

/-! The common finite torus along the complete variable-block interval, including its final infrared read. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramInfraredCircuit
open Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open RegulatorIR RegulatorIR.Oracle RegulatorIR.Ledger RegulatorIR.FVAAlt2.Period.Field
open WilsonPositionProgramCommonWindow WilsonPositionProgramVariableCircuit
variable {G : Gauge} (C : Run G) (D : XSpace.Run) {X : Type} (m j : X → ℕ) (w : X → ℕ → ℕ)
    (blocks : ∀ x k, (C.family.S.block (m x+k)).val=D.ratio^(w x k))

def count (p : Page j) : Side := D.finalSide.side * ⟨D.den (elapsed (w p.bindW) (remaining j p)),D.den_pos _⟩

local notation "B" => WilsonPositionProgramVariableCircuit.circuit C D m j w blocks

/-- The fine spacing is the unit of length in `Rocket.soothe`. -/
def circuit : Circuit j (count D j w) where
  l p := ((count D j w (Page.opening j p.bindW)).val : ℝ)/(count D j w p).val
  P x := (count D j w (Page.opening j x)).val
  sizeL := (B).sizeL
  J := (B).J
  seats f := by
    apply Subtype.ext
    change D.finalSide.side.val * D.den (elapsed (w f.volW) (remaining j f.prev)) =
      D.finalSide.side.val * D.den (elapsed (w f.volW) (remaining j f.next)) * (C.family.S.block (m f.volW+remaining j f.next)).val
    have adj : remaining j f.prev=remaining j f.next+1 := by
      change j f.volW-f.offset=j f.volW-(f.offset+1)+1
      have := f.ok
      omega
    rw [adj,show elapsed (w f.volW) (remaining j f.next+1)=elapsed (w f.volW) (remaining j f.next)+w f.volW (remaining j f.next) from Finset.sum_range_succ ..,
        blocks f.volW (remaining j f.next)]
    simp only [XSpace.Run.den,pow_add,Nat.mul_assoc]
  odd := (B).odd
  holds := (B).holds
  stands p := D.finalSide.large.trans (Nat.le_mul_of_pos_right _ (D.den_pos _))
  dual p := even_iff_two_dvd.mpr (dvd_mul_of_dvd_left D.finalSide.even _)
  week := (B).week
  shakes := (B).shakes
  slow := (B).slow
  l_p p := div_pos (by exact_mod_cast (count D j w _).property) (by exact_mod_cast (count D j w p).property)
  comet p := div_mul_cancel₀ _ (by exact_mod_cast (count D j w p).property.ne')

def history : SeriesT (circuit C D m j w blocks) C.family.path.levels.clock.kernel C.family.path where
  vol := date m j
  links := (WilsonPositionProgramVariableCircuit.history C D m j w blocks).links
  pact := (WilsonPositionProgramVariableCircuit.history C D m j w blocks).pact
  creed _ _ := rfl

theorem fine (x : X) (i : ℕ) (reach : elapsed (w x) (j x)=D.reserve*i*i+i) :
    count D j w (Page.opening j x)=(D.step i).p.side := by
  apply Subtype.ext
  change D.finalSide.side.val * D.den (elapsed (w x) (j x-0))=D.finalSide.side.val * D.den (i+D.reserve*i*i)
  rw [Nat.sub_zero,reach,Nat.add_comm (D.reserve*i*i)]

theorem finalSide (x : X) : count D j w (Page.finallyW j x)=D.finalSide.side := by
  apply Subtype.ext
  change D.finalSide.side.val * D.ratio^(elapsed (w x) (j x-j x))=D.finalSide.side.val
  simp [elapsed]

theorem units : (∀ x, (circuit C D m j w blocks).l (Page.opening j x)=1) ∧
    ∃ v : ℕ, ∀ x, (count D j w (Page.finallyW j x)).val ≤ v := by
  refine ⟨fun x => ?_,D.finalSide.side.val,fun x => (congrArg Subtype.val (finalSide D j w x)).le⟩
  change ((count D j w (Page.opening j x)).val:ℝ)/(count D j w (Page.opening j x)).val=1
  exact div_self (by exact_mod_cast (count D j w (Page.opening j x)).property.ne')

end YM.Integration.WilsonPositionProgramInfraredCircuit
end
