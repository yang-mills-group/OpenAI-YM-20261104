import YM.Integration.FVA1Physical.Wilson.BoundaryPair

/-! A shared conditional expectation of arbitrarily many independent groups of
physical boundary insertions. Each group may contain several physical links. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Finset Function MeasureTheory Lattice RG YM.Wilson Tree Push.BetaTransport Pressure
open RGComparison.Core16 RGComparison.Core16.Descent
open scoped Classical BigOperators
variable {G : Gauge} {n c f : Side} {S : StepData c f} (F : Forest S.ratio) (p : Descent n f)
variable {ι : Type} [DecidableEq ι]

/-- A single simultaneous change of all covered links is exactly the product
of the separately supported insertions at the integrand level, with all
inner histories and tags kept fixed. -/
theorem gain_blocks (β : ℕ → ℝ) (A : Finset ι) (K : ι → Finset (Bond c))
    (disj : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → Disjoint (K i) (K j))
    (U V : Config G c) (t : (push S F p).Tags) (x : Fields G (push S F p)) :
    boundaryGain (push S F p) β U (varyBonds (A.biUnion K) U V) t x =
      ∏ i ∈ A, boundaryGain (push S F p) β U (varyBonds (K i) U V) t x := by
  induction A using Finset.induction_on with
  | empty =>
    have same : varyBonds ∅ U V = U := by funext e; simp [varyBonds]
    simp [boundaryGain,same]
  | @insert i A hi ih =>
    have split : Disjoint (K i) (A.biUnion K) := by
      apply Finset.disjoint_left.mpr
      intro e he hA
      obtain ⟨j,hj,hey⟩ := Finset.mem_biUnion.mp hA
      have hij : i ≠ j := fun h => hi (h ▸ hj)
      exact Finset.disjoint_left.mp (disj i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj) hij) he hey
    have rest : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → Disjoint (K i) (K j) :=
      fun i hi j hj h => disj i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) h
    rw [Finset.biUnion_insert,Finset.prod_insert hi,gain_disjoint F p β split,ih rest]

variable (d : Descent n c)

def blockRead (β : ℕ → ℝ) (A : Finset ι) (K : ι → Finset (Bond c)) (U V : Config G c) : ℝ :=
  (∑ t, ∫ x, d.integrand β t 1 U x * ∏ i ∈ A, boundaryGain d β U (varyBonds (K i) U V) t x ∂d.measure G) /
    massAt d β U

theorem block_read_eq (β : ℕ→ℝ) (A : Finset ι) (K : ι→Finset (Bond c))
    (disj : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → Disjoint (K i) (K j)) (U V : Config G c) :
    blockRead (push S F p) β A K U V = boundaryRead (push S F p) β U (varyBonds (A.biUnion K) U V) := by
  unfold blockRead boundaryRead
  simp_rw [gain_blocks F p β A K disj]

theorem block_read_cover (β : ℕ→ℝ) (A : Finset ι) (K : ι→Finset (Bond c))
    (disj : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → Disjoint (K i) (K j)) (cover : A.biUnion K = Finset.univ)
    (U V : Config G c) : blockRead (push S F p) β A K U V = boundaryRead (push S F p) β U V := by
  rw [block_read_eq F p β A K disj,cover]
  congr 1
  funext e
  simp [varyBonds]

end YM.Integration.FVA1Physical.Wilson
