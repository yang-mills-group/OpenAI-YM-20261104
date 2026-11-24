import YM.Integration.WilsonMixedPassportArmada
import YM.QuadraticLocal.Fk.Window

/-! Unnormalized source entries for the two disjoint faces in one registered finite chart. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMixedFaceLog
open Finset Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn WilsonMixedPassportRows
open Comparison.RG02
open scoped Classical BigOperators

variable {G : Gauge} {n : Side} {V ι κ α β : Type} [DecidableEq V] [Fintype V] {C : Census V}
  {P Q : Passport n V} (M : ι → Row P C G α) (Y : κ → Row Q C G β)
  (old fresh : Finset V) (sep : Disjoint old fresh)

omit [Fintype V] in
private theorem onFace {g : ℝ} {x : α} {U : Config G n} (s : C.Mode) (Z : Poly C)
    (h : HasSum (fun i => Poly.send (M i).mode ((M i).nominal g x U)) Z) :
    HasSum (fun a : Face M old => (Poly.send (M a.val).mode ((M a.val).nominal g x U)).part s)
      (if s.val ⊆ old then Z.part s else 0) := by
  let f (i : ι) := (Poly.send (M i).mode ((M i).nominal g x U)).part s
  have total : HasSum f (Z.part s) := (Pi.hasSum.mp h) s
  by_cases hs : s.val ⊆ old
  · rw [if_pos hs]
    have active : Function.support f ⊆ {i | (M i).mode.val ⊆ old} := by
      intro i hfi
      have same : s = (M i).mode := by
        by_contra no
        exact hfi (by simp only [f, Poly.part_send, if_neg no])
      change (M i).mode.val ⊆ old
      rw [← same]
      exact hs
    exact (hasSum_subtype_iff_of_support_subset active).mpr total
  · rw [if_neg hs]
    apply hasSum_zero.congr_fun
    intro i
    have no : s ≠ (M i.val).mode := fun h => hs (h ▸ i.property)
    simp only [Poly.part_send, if_neg no]

variable {γ : Type} (leftTest : γ → α) (rightTest : γ → β)

def routed : Sum (Face M old) (Face Y fresh) → Row (passport (owner P Q old)) C G γ :=
  Sum.elim
    (WilsonMixedPassportArmada.roster M old (owner P Q old) (fun _ h => if_pos h) leftTest)
    (WilsonMixedPassportArmada.roster Y fresh (owner P Q old)
      (fun _ h => if_neg (fun h' => Finset.disjoint_left.mp sep h' h)) rightTest)

local notation "S" => routed M Y old fresh sep leftTest rightTest
omit [Fintype V] in
private theorem projected (point : BudgetPoint) (g : ℝ) (t : γ) (U : Config G n)
    (Z₀ Z₁ Z₂ : Poly C) (s : C.Mode)
    (h₀ : HasSum (fun i => Poly.send (M i).mode ((M i).nominal g (leftTest t) U)) Z₀)
    (h₁ : HasSum (fun i => Poly.send (Y i).mode ((Y i).nominal g (rightTest t) U)) Z₁)
    (h₂ : HasSum (fun i => Poly.send (S i).mode ((S i).nominal g t U)) Z₂) :
    Z₂.part s = (if s.val ⊆ old then Z₀.part s else 0) + (if s.val ⊆ fresh then Z₁.part s else 0) := by
  let left (a : Face M old) := (Poly.send (M a.val).mode ((M a.val).nominal g (leftTest t) U)).part s
  let right (a : Face Y fresh) := (Poly.send (Y a.val).mode ((Y a.val).nominal g (rightTest t) U)).part s
  have joinedSum := HasSum.sum (f := Sum.elim left right)
    (onFace M old s Z₀ h₀) (onFace Y fresh s Z₁ h₁)
  apply ((Pi.hasSum.mp h₂) s).unique (joinedSum.congr_fun _)
  rintro (j | j)
  · have h := WilsonMixedPassportRows.original (owner P Q old) (M j.val)
      (fun _ hv => if_pos (j.property hv)) leftTest point g t
    exact congrArg (fun y : ℂ => (Poly.send (M j.val).mode y).part s) (congr_fun h.2.2.2 U)
  · have h := WilsonMixedPassportRows.original (owner P Q old) (Y j.val)
      (fun _ hv => if_neg (fun h => Finset.disjoint_left.mp sep h (j.property hv)))
      rightTest point g t
    exact congrArg (fun y : ℂ => (Poly.send (Y j.val).mode y).part s) (congr_fun h.2.2.2 U)

variable (w₀ w₁ w : V → ℕ) (L : AllOrder.Floe.Layout G) (T : Finset AllOrder.Floe.Age)
  (t : γ)
local notation "X₀" => Air.craft M (fun i => (M i).paint (leftTest t)) w₀ L T
local notation "X₁" => Air.craft Y (fun i => (Y i).paint (rightTest t)) w₁ L T
local notation "X₂" => Air.craft S (fun i => (S i).paint t) w L T

omit [Fintype V] in
theorem original {a b c : ℝ} {d e f : ℕ}
    (h₀ : Air.Staff M (fun i => (M i).paint (leftTest t)) w₀ a d)
    (h₁ : Air.Staff Y (fun i => (Y i).paint (rightTest t)) w₁ b e)
    (h₂ : Air.Staff S (fun i => (S i).paint t) w c f)
    (point : BudgetPoint) (g : ℝ) (live : g ≠ 0) (U : Config G n) (s : C.Mode) :
    (Integral.markedLog g U X₂).part s =
      (if s.val ⊆ old then (Integral.markedLog g U X₀).part s else 0) +
      (if s.val ⊆ fresh then (Integral.markedLog g U X₁).part s else 0) := by
  letI : Fintype V := Fintype.ofInjective C.fire (fun a b h => (C.fire_inj a b).mp h)
  have hM := Air.liftPassport M _ w₀ h₀ L T g live U
  have hY := Air.liftPassport Y _ w₁ h₁ L T g live U
  have hS := Air.liftPassport S _ w h₂ L T g live U
  exact projected M Y old fresh sep leftTest rightTest point g t U _ _ _ s hM hY hS

end YM.Integration.WilsonMixedFaceLog
