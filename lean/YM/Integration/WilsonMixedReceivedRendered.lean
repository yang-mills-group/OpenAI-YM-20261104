import YM.Integration.WilsonMixedTestTableau

/-! Preserve each of the two real masks and the complete signed regular log of each enrolled cohort. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMixedReceivedRendered
open Function Finset Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Affinity
open WilsonMixedPassportRows WilsonMixedTestTableau
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {V ι κ : Type} [DecidableEq V] {J : Census V}
  {P Q : Passport n V} {E F : V → Type}
  [∀ v, AddCommGroup (E v)] [∀ v, Module ℝ (E v)]
  [∀ v, AddCommGroup (F v)] [∀ v, Module ℝ (F v)]
  (A : ∀ v, Set (E v)) (B : ∀ v, Set (F v))
  (K : ∀ v, Submodule ℝ (E v)) (L : ∀ v, Submodule ℝ (F v))
  (M : ι → Row P J G (Wallet A)) (N : κ → Row Q J G (Wallet B))
  (point : BudgetPoint) (g : ℝ)

private theorem full (old : Finset V) (t : Wallet A) (U : Config G n)
    (zero : ∀ v ∉ old, (t v).val ∈ K v) (file : Tableau K A M)
    (used : Summable (fun i => (rendered M point g).frame i t U)) :
    HasSum (fun i : Face M old => (rendered M point g).frame i.val t U) ((rendered M point g).log t U) := by
  let P₀ := rendered M point g
  have booked := file.line point g
  have supported : Function.support (fun i => P₀.frame i t U) ⊆ {i | (M i).mode.val ⊆ old} := by
    intro i active v hv
    by_contra absent
    have nil (Z : Config G n) : P₀.nominal t i Z = 0 := (booked.adv i Z).idle v hv t (zero v absent)
    have light : P₀.light t i U = 0 := by
      unfold Lamps.light
      split
      · exact nil U
      · by_cases good : Healthy point.threshold (P₀.ground i) U
        · rw [masked_eq _ _ _ _ good, nil]
        · exact masked_ne _ _ _ _ good
    exact active (by simp [Lamps.frame, light])
  exact (hasSum_subtype_iff_of_support_subset supported).mpr used.hasSum

private theorem placed {α β : Type} {P₀ : Passport n V}
    (p : V → Passport n V) (a : Row P₀ J G α) (home : ∀ v ∈ a.mode.val, p v = P₀)
    (test : β → α) (t : β) (U : Config G n) :
    (if a.clear then (place p a home test).nominal g t U else
      masked point.threshold ((place p a home test).ground point) ((place p a home test).nominal g t) U) =
    (if a.clear then a.nominal g (test t) U else masked point.threshold (a.ground point) (a.nominal g (test t)) U) := by
  have row := WilsonMixedPassportRows.original p a home test point g t
  rw [row.2.2.1, row.2.2.2]

theorem previous (old fresh : Finset V) (apart : Disjoint old fresh)
    (zA : ∀ v, 0 ∈ A v) (zB : ∀ v, 0 ∈ B v)
    (oldFile : Tableau K A M) (newFile : Tableau L B N)
    (t : Wallet (actors A B)) (U : Config G n)
    (first : Summable (fun i => (rendered M point g).frame i (left A B old zA t) U))
    (second : Summable (fun i => (rendered N point g).frame i (right A B fresh zB t) U)) :
    let S := WilsonMixedFaceLog.routed M N old fresh apart (left A B old zA) (right A B fresh zB)
    (rendered S point g).log t U = (rendered M point g).log (left A B old zA t) U +
      (rendered N point g).log (right A B fresh zB t) U := by
  intro S
  let l (i : Face M old) := (rendered M point g).frame i.val (left A B old zA t) U
  let r (i : Face N fresh) := (rendered N point g).frame i.val (right A B fresh zB t) U
  have hl := full A K M point g old (left A B old zA t) U
    (fun v absent => by simp [left, leftAt, absent]) oldFile first
  have hr := full B L N point g fresh (right A B fresh zB t) U
    (fun v absent => by simp [right, rightAt, absent]) newFile second
  have both := HasSum.sum (f:=Sum.elim l r) hl hr
  have same : HasSum (fun i => (rendered S point g).frame i t U) _ := both.congr_fun (by
    rintro (i | i)
    · apply congrArg (Poly.send (M i.val).mode)
      exact placed point g (owner P Q old) (M i.val) (fun _ h => if_pos (i.property h)) (left A B old zA) t U
    · apply congrArg (Poly.send (N i.val).mode)
      exact placed point g (owner P Q old) (N i.val) (fun _ h => if_neg (fun h' => Finset.disjoint_left.mp apart h' (i.property h))) (right A B fresh zB) t U)
  exact same.tsum_eq

end YM.Integration.WilsonMixedReceivedRendered
