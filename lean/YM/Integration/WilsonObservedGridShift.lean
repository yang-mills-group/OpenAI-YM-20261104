import YM.Integration.WilsonReplicatedChildPurchase
import YM.Cells.Proximity

/-! Move an auxiliary replication grid and all of the original microscopic
cylinders in the same Wilson probability. The blocking schedule is fixed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonObservedGridShift
open Lattice Cells Wilson RG Labels Source MeasureTheory Function
open scoped Classical BigOperators Topology
variable {G : Gauge} {n : Side}

def grid (T : Tiling n) (q : Site n) := T.newly (T.base+q)

theorem translateBy (T : Tiling n) (q : Site n) (i : T.Cell) :
    (grid T q).translateBy i = T.translateBy i + q - (T.omega i).act q := by
  change T.base+q+T.units.root i - (T.omega i).act (T.base+q) + T.bias i =
    T.base+T.units.root i - (T.omega i).act T.base + T.bias i + q - (T.omega i).act q
  rw [Signed.act_add]; abel

theorem map (T : Tiling n) (q : Site n) (i : T.Cell) (x : Site n) :
    (grid T q).copyMap i (x+q) = T.copyMap i x + q := by
  change (T.omega i).act (x+q)+(grid T q).translateBy i = (T.omega i).act x+T.translateBy i+q
  rw [Signed.act_add,translateBy]; abel

theorem copy (T : Tiling n) (q : Site n) (i : T.Cell) (X : Config G n → ℂ) :
    (grid T q).copy i (X ∘ translate q) = T.copy i X ∘ translate q := by
  funext U
  have same : translate q (pull (T.omega i) ((grid T q).translateBy i) U) =
      pull (T.omega i) (T.translateBy i) (translate q U) := by
    simp only [← pull_one,pull_pull,mul_one,one_mul,affine,Signed.act_one,translateBy]
    congr 1; abel
  by_cases h : T.hand i
  · change (if T.hand i then star (X (translate q _)) else X (translate q _)) =
      (if T.hand i then star (X _) else X _)
    rw [if_pos h,if_pos h]; exact congrArg (fun W => star (X W)) same
  · change (if T.hand i then star (X (translate q _)) else X (translate q _)) =
      (if T.hand i then star (X _) else X _)
    rw [if_neg h,if_neg h]; exact congrArg X same

theorem root (T : Tiling n) (q : Site n) (β : ℝ) (X : Config G n → ℂ) (hX : Continuous X) :
    (grid T q).rootTest β (X ∘ translate q) = T.rootTest β X := by
  have exact : (fun U => ∏ i : (grid T q).Cell, (grid T q).copy i (X ∘ translate q) U) =
      T.fullAt (fun _ => X) ∘ translate q := by
    funext U; apply Finset.prod_congr rfl; intro i _; exact congrFun (copy T q i X) U
  have c : Continuous (T.fullAt (fun _ => X)) := by
    apply continuous_finsetProd; intro i _
    by_cases h : T.hand i
    · change Continuous (fun U => if T.hand i then star (X _) else X _)
      simp only [if_pos h]; exact continuous_star.comp (hX.comp (continuous_pull ..))
    · change Continuous (fun U => if T.hand i then star (X _) else X _)
      simp only [if_neg h]; exact hX.comp (continuous_pull ..)
  have m := moment_pull β 1 q (T.fullAt (fun _ => X))
    (c.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  have translated : pull (K:=G.El) 1 q = Lattice.translate q := funext (pull_one q)
  rw [translated] at m
  unfold Tiling.rootTest; rw [exact,m]; rfl

theorem physical (C : Family G) (N p : ℕ) (T : Tiling (C.side N p)) (q : Site (C.side N p))
    {I : Type*} [Fintype I] (d : I → ℕ) (x : ∀ i, C.label (d i)) (o : I → Site (C.side N p)) :
    (grid T q).rootTest (C.beta N p) (fun U => ∏ i, C.O N p (x i) (o i+q) U) =
      T.rootTest (C.beta N p) (fun U => ∏ i, C.O N p (x i) (o i) U) := by
  let X := fun U => ∏ i, C.O N p (x i) (o i) U
  have born : (fun U => ∏ i, C.O N p (x i) (o i+q) U) = X ∘ translate q := by
    funext U; simp only [X,Function.comp_apply,Family.O,TransferData.cylinder,initial,Pi.smul_apply,
      SectionData.places_trans]
  rw [born]; exact root T q _ X (continuous_finsetProd _ fun i _ => C.continuousO N p (d i) (x i) (o i))

end YM.Integration.WilsonObservedGridShift
