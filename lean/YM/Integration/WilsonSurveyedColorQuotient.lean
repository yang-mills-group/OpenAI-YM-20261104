import YM.Integration.WilsonSurveyedColorTensor
import YangMills.WilsonProof.NativeSupport.YM.MS.Mach.Land

/-! Color change on the actual momentum-space MS rows and their regulated
linear BV exact part. Source representatives are selected in their own
physical deck after the change. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSurveyedColorQuotient
open Function MS MS.Plane MS.Koszul MS.Landau MS.Landau.Detect MS.Local.Physical
open WilsonSurveyedColorTensor
open scoped BigOperators Classical
variable {G : Gauge} {P D : Type} (U : G.Color ≃ₗᵢ[ℝ] G.Color)

def leg : Legs (Note G D P) → Score G D P →ₗ[ℂ] ℂ
  | [] => LinearMap.proj []
  | d::w => ∑ i : G.ColorIndex, entry U i d.1.2 •
      ((leg w).comp (Koszul.D (MS.Color.setLeg d i)))

def turn : Score G D P →ₗ[ℂ] Score G D P := LinearMap.pi (leg U)

theorem derivative (a : Note G D P) (F : Score G D P) :
    Koszul.D a (turn U F) =
      ∑ i : G.ColorIndex, entry U i a.1.2 • turn U (Koszul.D (MS.Color.setLeg a i) F) := by
  ext w
  change leg U (a::w) F = _
  simp [leg,turn]

variable [Fintype D] [DecidableEq D] (f : P → Momentum D)

private lemma at_color (i : Branch G D) (q : P) (F : Score G D P) :
    (send f).move.hook (i,q) (turn U F) =
      ∑ l : G.ColorIndex, entry U l i.2 •
        turn U ((send f).move.hook (MS.Color.setLeg (i,q) l) F) := by
  simp_rw [Charge.hook_rule (F:=turn U F), MS.Color.hook_send, derivative, Finset.smul_sum,
    MS.Color.setLeg, Charge.hook_rule .., MS.Color.hook_send, map_sum, map_smul, Finset.smul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => smul_comm ..

theorem charge (F : Score G D P) :
    turn U ((send f).raise F) = (send f).raise (turn U F) := by
  ext w
  induction w generalizing F with
  | nil => simp [turn, leg, Charge.raise]
  | cons a w ih =>
    obtain ⟨a,q⟩ := a
    rw [D_eval _ (turn U ((send f).raise F)), derivative, D_eval _ ((send f).raise (turn U F))]
    unfold Charge.raise at ih ⊢
    rw [Shift.deriving', at_color, derivative]
    simp_rw [Shift.deriving', map_add, map_sum, map_smul, smul_add, Finset.smul_sum,
      Finset.sum_add_distrib, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, ih]
    congr! 1
    exact Finset.sum_congr rfl fun i _ => smul_comm ..

/-- A counterterm with its native regulated differential transports with
the same momentum and color on *every* leg, including ghost slots. -/
theorem exactRow (F : Law G) : turn U (kills G F) = kills G (turn U F) :=
  charge U id F

/-- Select the transformed physical representative on the actual MS deck.
The paired residue below it is a genuine BV image. -/
theorem projected (B : Deck G) (h r : ℕ) (F : Law G)
    (allowed : turn U F ∈ Lease G h r 0) (closed : natQ F = 0) :
    ∃ (p : B.BIndex h r → ℝ) (K : Law G), K ∈ Lease G ((h:ℤ)-1) r (-1) ∧
      ∑ i, p i • B.raw h r i + natQ K = turn U F := by
  apply B.combine allowed
  exact (charge U id F).symm.trans (by rw [closed, map_zero])

end YM.Integration.WilsonSurveyedColorQuotient
end
