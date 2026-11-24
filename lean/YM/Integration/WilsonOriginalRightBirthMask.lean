import YM.Integration.WilsonOriginalRightBirthLamp

/-! Exact masked right-slot substitution on the original physical field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalRightBirthMask
open Function Finset Lattice Wilson RG Marker Ac Push Push.AbsoluteSums
open Corrected QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Affinity WilsonMixedPassportRows
open scoped Classical BigOperators
variable {G : Gauge} {V I : Type} [DecidableEq V] {n : Side} {C : Census V}
  {P Q : Passport n V} {E F : V → Type}
  [∀ i, AddCommGroup (E i)] [∀ i, AddCommGroup (F i)]
  [∀ i, Module ℝ (E i)] [∀ i, Module ℝ (F i)]
  (A : ∀ i, Set (E i)) (B : ∀ i, Set (F i))
  (K : ∀ i, Submodule ℝ (E i)) (L : ∀ i, Submodule ℝ (F i))
  (Y : I → Row Q C G (Wallet B))
  (P : Passport n V) (old fresh : Finset V) (apart : Disjoint old fresh) (zero : ∀ i, 0 ∈ B i)

local notation "X" => WilsonOriginalRightBirthLamp.rows A B Y P old fresh apart zero
local notation "right" => WilsonMixedTestTableau.right A B fresh zero

omit [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)] [∀ i, Module ℝ (F i)] in
theorem frame (point : BudgetPoint) (g : ℝ) (x : Wallet (WilsonMixedTestTableau.actors A B))
    (U : Config G n) (i : Face Y fresh) :
    (rendered X point g).frame i x U = (rendered Y point g).frame i.val (right x) U := by
  have same := WilsonMixedPassportRows.original (owner P Q old) (Y i.val)
    (fun _ hv => if_neg (fun ho => Finset.disjoint_left.mp apart ho (i.property hv)))
    right point g x
  change Poly.send (Y i.val).mode (if (Y i.val).clear then (X i).nominal g x U else
    masked point.threshold ((X i).ground point) ((X i).nominal g x) U) = _
  rw [show (X i).ground point = (Y i.val).ground point from same.2.2.1,
    show (X i).nominal g x = (Y i.val).nominal g (right x) from same.2.2.2]
  rfl

omit [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)] in
theorem logged (file : Tableau L B Y) [Fintype I] (point : BudgetPoint) (g : ℝ)
    (x : Wallet (WilsonMixedTestTableau.actors A B)) (U : Config G n) :
    (rendered X point g).log x U = (rendered Y point g).log (right x) U := by
  let f (i:I) := (rendered Y point g).frame i (right x) U
  have live : Function.support f ⊆ {i | (Y i).mode.val ⊆ fresh} := by
    intro i hi v hv
    by_contra absent
    have dead := (file.bill i).idle v hv (right x) (by
      change (WilsonMixedTestTableau.rightAt A B fresh zero v (x v)).val ∈ L v
      simp only [WilsonMixedTestTableau.rightAt,if_neg absent]
      exact (L v).zero_mem)
    have none : (Y i).nominal g (right x) U = 0 := by change (Y i).paint _ * _ = 0; rw [dead,zero_mul]
    apply hi
    change Poly.send (Y i).mode (if (Y i).clear then (Y i).nominal g (right x) U else masked point.threshold ((Y i).ground point) ((Y i).nominal g (right x)) U) = 0
    split
    · rw [none,Poly.send_zero]
    · by_cases pass : Healthy point.threshold ((Y i).ground point) U
      · rw [masked_eq _ _ _ _ pass,none,Poly.send_zero]
      · rw [masked_ne _ _ _ _ pass,Poly.send_zero]
  have total : HasSum (fun i : Face Y fresh => f i.val) (∑' i,f i) :=
    (hasSum_subtype_iff_of_support_subset live).mpr (by simpa only [tsum_fintype] using hasSum_fintype f)
  change (∑' i, (rendered X point g).frame i x U) = ∑' i, f i
  rw [← total.tsum_eq]
  exact tsum_congr (frame A B Y P old fresh apart zero point g x U)

end YM.Integration.WilsonOriginalRightBirthMask
