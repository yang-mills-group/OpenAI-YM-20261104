import YangMills.WilsonProof.NativeSupport.ActualNearBonds

/-! A spatial partition of one entire insertion layer. The position within a
terminal block is recorded using the actual `Ratio.splitSites` at every step. -/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.InletSusceptibility
open MeasureTheory Lattice Wilson RG RGComparison.Core16 YM.Pressure
open scoped BigOperators

def Digits {n : Side} : {c : Side} → Descent n c → Type
  | _, .nil => Unit
  | _, .push S _ d => Site S.ratio.count × Digits d

instance digitsFinite {n : Side} {c : Side} (d : Descent n c) : Fintype (Digits d) :=
  match d with
  | .nil => inferInstanceAs (Fintype Unit)
  | .push S _ d =>
    letI := digitsFinite d
    inferInstanceAs (Fintype (Site S.ratio.count × Digits d))

def coordinates {n : Side} : {c : Side} → (d : Descent n c) → Site n ≃ Site c × Digits d
  | _, .nil => (Equiv.prodUnique _ Unit).symm
  | _, .push S _ d => (coordinates d).trans <|
    (S.ratio.splitSites.prodCongr (Equiv.refl _)).trans (Equiv.prodAssoc _ _ _)

lemma coordinates_parent {n c : Side} (d : Descent n c) (x : Site n) :
    (coordinates d x).1 = home d x := by
  induction d with
  | nil => rfl
  | push S F d ih =>
    change S.ratio.parent ((coordinates d x).1) = S.ratio.parent (home d x)
    rw [ih]

abbrev Color {n c : Side} (d : Descent n c) := Digits d × Axis

def partition {n c : Side} (d : Descent n c) : Bond n ≃ Site c × Color d :=
  ((coordinates d).prodCongr (Equiv.refl Axis)).trans (Equiv.prodAssoc _ _ _)

lemma one_per_site {n c : Side} (d : Descent n c) (color : Color d) (x : Site c) :
    home d ((partition d).symm (x,color)).1 = x := by
  rw [← coordinates_parent]
  exact congrArg Prod.fst ((partition d).apply_symm_apply (x,color))

lemma color_count {n c : Side} (d : Descent n c) :
    c.val ^ 4 * Fintype.card (Color d) = n.val ^ 4 * 4 := by
  have h := Fintype.card_congr (partition d)
  simp only [Bond, Fintype.card_prod, site_card] at h
  simpa [Axis, Fintype.card_prod] using h.symm

theorem group_by_color {n c : Side} (d : Descent n c) (f : Bond n → ℝ) :
    ∑ b, f b = ∑ k : Color d, ∑ x : Site c, f ((partition d).symm (x,k)) := by
  classical
  let h : Site c × Color d → ℝ := fun p => f ((partition d).symm p)
  calc
    _ = ∑ p, h p := Fintype.sum_equiv (partition d) _ _ (fun b => by simp [h])
    _ = ∑ x : Site c, ∑ k : Color d, h (x,k) := Fintype.sum_prod_type h
    _ = _ := Finset.sum_comm

theorem traversal_home_comp {G : Gauge} {A : Levels G} {p : ℕ} (T : Slices A p)
    {a b N : ℕ} (ab : a ≤ b) (bN : b ≤ N) (x : Site (A.S.side N p)) :
    home (traversal T (ab.trans bN)) x =
      home (traversal T ab) (home (traversal T bN) x) := by
  induction ab using Nat.decreasingInduction with
  | self => rw [traversal_self]; rfl
  | of_succ j hj ih =>
    rw [traversal_push T (lt_of_lt_of_le hj bN), traversal_push T hj]
    exact congrArg (A.clock.op j p).ratio.parent ih

/-- The sites occupied by one color are distinct after *any* intermediate
projection of the actual traversal, even for the smallest period. -/
theorem all_cuts {G : Gauge} {A : Levels G} {p : ℕ} (T : Slices A p)
    {a b N : ℕ} (ab : a ≤ b) (bN : b ≤ N) (color : Color (traversal T (ab.trans bN))) :
    Function.Injective (fun x : Site (A.S.side a p) =>
      home (traversal T bN) (((partition (traversal T (ab.trans bN))).symm (x,color)).1)) := by
  intro x y h
  have h' := congrArg (home (traversal T ab)) h
  change home _ (home _ _) = home _ (home _ _) at h'
  simpa only [← traversal_home_comp T ab bN, one_per_site] using h'

end YM.Integration.InletSusceptibility
