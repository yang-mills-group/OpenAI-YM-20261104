import YM.Integration.WilsonMixedReceivedHard

/-! Re-enter the complete deposited signed regular and forced inventory on the next joint passport. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMixedReceivedInventory
open Finset Function Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Affinity
open Push Push.AbsoluteSums Next.Foundations
open WilsonMixedTestTableau WilsonMixedPassportRows
open private transport from YM.Integration.WilsonMixedTestTableau
open scoped BigOperators Classical

variable {G : Gauge} {n : Side} {V I : Type} [DecidableEq V] [Fintype V] {J : Census V}
  {P Q : Passport n V} {W : Rep G n} {E F : V → Type}
  [∀ v, AddCommGroup (E v)] [∀ v, AddCommGroup (F v)] [∀ v, Module ℝ (E v)] [∀ v, Module ℝ (F v)]
  (A : ∀ v, Set (E v)) (B : ∀ v, Set (F v))
  (K : ∀ v, Submodule ℝ (E v)) (L : ∀ v, Submodule ℝ (F v))
  (old : Finset V) (zeroA : ∀ v, 0 ∈ A v)
  (Y : Tint.Incoming P W (Wallet A) I J)
  (file : Taut P.support A K Y.old) (forced : Crown P.support A K Y.hard)

local notation "test" => left A B old zeroA
local notation "joined" => passport (owner P Q old)
abbrev Shelf := {i : I // (Y.old.mode i).val ⊆ old}

def regular : Lamps (Wallet (actors A B)) (Shelf A old Y) G W.p (joined).origin J where
  mode i := Y.old.mode i.val
  live i := Y.old.live i.val
  address i := Y.old.address i.val
  roots i v hv := by
    change (owner P Q old v).origin v ∈ _
    rw [show owner P Q old v = P from if_pos (i.property hv)]
    exact Y.old.roots i.val v hv
  nominal t i := Y.old.nominal (test t) i.val
  legal t i := Y.old.legal (test t) i.val
  clear i := Y.old.clear i.val
  pure t i := Y.old.pure (test t) i.val

def received : Tint.Incoming (joined) W (Wallet (actors A B)) (Shelf A old Y) J where
  old := regular (Q:=Q) A B old zeroA Y
  hard := WilsonMixedReceivedHard.posted (Q:=Q) A B K old zeroA Y.hard forced

local notation "intake" => received (Q:=Q) A B K old zeroA Y forced
local notation "rows" => regular (Q:=Q) A B old zeroA Y

include file
omit [Fintype V] in
theorem taut : Taut (joined).support (actors A B) (pieces K L) (rows) := by
  constructor
  · intro i v hv
    change (owner P Q old v).support v ⊆ _
    rw [show owner P Q old v = P from if_pos (i.property hv)]
    exact file.house i.val v hv
  · intro i U
    apply transport (file.adv i.val U) (leftAt A B old zeroA)
    · intro v hv x y z a b eq
      simp only [leftAt, if_pos (i.property hv)]
      exact congrArg Prod.fst eq
    · intro v hv t ht
      simp only [leftAt, if_pos (i.property hv)]
      exact ht.1

omit file [Fintype V] [∀ v, AddCommGroup (F v)] [∀ v, Module ℝ (F v)] in
theorem paid {w w' : V → ℝ} (positive : ∀ v, 0 < w v) (positive' : ∀ v, 0 < w' v)
    (fits : ∀ v ∈ old, w' v ≤ w v) {d : ℕ} {a c k : ℝ}
    (reg : Y.old.Paid w d a c) (hard : Y.hard.Paid w d a k) :
    (intake).old.Paid w' d a c ∧ (intake).hard.Paid w' d a k := by
  refine ⟨?_, WilsonMixedReceivedHard.paid (Q:=Q) A B K old zeroA Y.hard forced positive positive' fits hard⟩
  obtain ⟨f, pos, valid, hit⟩ := reg.budget
  refine ⟨fun i => f i.val, fun i => pos i.val, fun i t => valid i.val (test t), ?_⟩
  intro x
  apply budget_mono (budget_pull (Subtype.val : Shelf A old Y → I) Subtype.val_injective (hit x))
  · intro i
    change 0 ≤ if x ∈ Y.old.ground i.val then Poly.toll w' (Y.old.mode i.val)*f i.val*
      Real.exp (a*coverNumber d (Y.old.ground i.val)) else 0
    split
    · positivity [Poly.worth positive' (Y.old.mode i.val), pos i.val]
    · exact le_rfl
  · intro i
    change (if x ∈ Y.old.ground i.val then Poly.toll w' (Y.old.mode i.val)*f i.val*_
      else 0) ≤ (if x ∈ Y.old.ground i.val then Poly.toll w (Y.old.mode i.val)*f i.val*_ else 0)
    split
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (Finset.prod_le_prod (fun v _ => (positive' v).le)
          (fun v hv => fits v (i.property hv))) (pos i.val)) (Real.exp_pos _).le
    · exact le_rfl

omit [Fintype V] [∀ v, AddCommGroup (F v)] [∀ v, Module ℝ (F v)] in
/-- Every old coefficient survives on its projected test, including the mixed terms
already deposited. The physical forced array is the very same function at every owner. -/
theorem physical {w : V → ℝ} (positive : ∀ v, 0 < w v) {d : ℕ} {a c : ℝ}
    (nonnegative : 0 ≤ a) (reg : Y.old.Paid w d a c) (t : Wallet (actors A B)) (U : Config G n) :
    (intake).old.log t U = Y.old.log (test t) U ∧ (intake).hard.hard t = Y.hard.hard (test t) := by
  refine ⟨?_, rfl⟩
  let g := fun i => Y.old.frame i (test t) U
  have support : Function.support g ⊆ {i | (Y.old.mode i).val ⊆ old} := by
    intro i live v hv
    by_contra absent
    apply live
    have zero (W' : Config G n) : Y.old.nominal (test t) i W' = 0 := by
      apply (file.adv i W').idle v hv (test t)
      simp only [left, leftAt, if_neg absent, Submodule.zero_mem]
    have light : Y.old.light (test t) i U = 0 := by
      unfold Lamps.light
      split
      · exact zero U
      · by_cases good : Healthy W.p.threshold (Y.old.ground i) U
        · rw [masked_eq _ _ _ _ good, zero]
        · exact masked_ne _ _ _ _ good
    simp [g, Lamps.frame, light]
  have all : HasSum g (Y.old.log (test t) U) := (reg.sums nonnegative positive (test t) U).hasSum
  exact ((hasSum_subtype_iff_of_support_subset support).mpr all).tsum_eq

end YM.Integration.WilsonMixedReceivedInventory
