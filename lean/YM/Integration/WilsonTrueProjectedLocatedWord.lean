import YM.Integration.WilsonTrueProjectedLocatedDebit

/-! The physically propagated cutoff field is compared on each torus before
normalizing any scalar. Its discrepancy is the signed sum of transported
defects on the original older kernels. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonTrueProjectedLocatedWord
open Filter MeasureTheory Lattice RG Wilson Extra.Histories Source Labels
open Extra.Histories.Relay Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open QuadraticLocal QuadraticLocal.Advent AllOrder AllOrder.Floe AllOrder.Transit WheelP WilsonOriginalNullCorridor
open scoped Classical Topology BigOperators
variable {G : Gauge} (R : Run G)
local notation "C₀" => R.family

theorem telescope (d N p b : ℕ) (F E : ∀ j,Config G ((C₀).side (b+j) p) → ℂ) :
    ∀ n : ℕ, (∀ j<n, Integrable (F j) (prior G _)) →
    (∀ j<n, Integrable (E j) (prior G _)) →
    (∀ j<n, transition (C:=C₀) d N p (b+j) (F (j+1))=F j+E j) →
    flow C₀ d N p b n (F n)=F 0+∑ j ∈ Finset.range n, flow C₀ d N p b j (E j) := by
  intro n
  induction n with
  | zero => simp [flow]
  | succ n ih =>
    intro before earn step
    change flow C₀ d N p b n (transition (C:=C₀) d N p (b+n) (F (n+1))) = _
    rw [step n (Nat.lt_succ_self n),flow_add C₀ d N p b n _ _ (before n (Nat.lt_succ_self n))
      (earn n (Nat.lt_succ_self n)),ih (fun _ h=>before _ (Nat.lt_succ_of_lt h))
      (fun _ h=>earn _ (Nat.lt_succ_of_lt h)) (fun _ h=>step _ (Nat.lt_succ_of_lt h)),
      Finset.sum_range_succ,add_assoc]

/-- Each dated original compact field includes its own full quiet density,
all eligible forced alternatives, and any already deposited ordinary words. -/
theorem original (d : ℕ) (simple : G.Simple) {ε : ℝ} (ep : 0 ≤ ε) :
    ∀ᶠ b : ℕ in atTop, ∀ m N p k n : ℕ, m ≤ b → b+n ≤ N →
    ∀ (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (W : ∀ j, Rep G ((C₀).side j p)),
    Concourse R.alloy R.kit R.T π Γ m N p k W →
    ∀ (o : ∀ j,Site ((C₀).side j p)),
    (∀ j<n, o (b+j)=((C₀).path.levels.clock.op (b+j) p).ratio.parent (o (b+j+1))) →
    (∀ j<n, WilsonOriginalNullPlacedParallel.Joined C₀ d N p (b+j) W (o (b+j+1)) ε) →
    (∀ j<n, ((C₀).path.levels.budget (b+j)).supportExponent ≤ 100) →
    ∀ (F : ∀ j, Config G ((C₀).side (b+j) p) → ℂ)
      (q : ∀ j, store C₀ d p (b+j)) (B : ℕ → ℝ),
    (∀ j<n, Integrable (F j) (prior G _)) →
    (∀ j<n, (q j).Format (o (b+j)) (C₀).params (W (b+j)) ∧
      (q j).remBound (o (b+j)) (W (b+j)) (safety C₀ (b+j)) (B j) ∧
      ((C₀).labels.level d).coeffSize (q j).x ≤ B j ∧
      transition (C:=C₀) d N p (b+j) (F (j+1))=
        F j+(q j).density (o (b+j)) ((C₀).localSection d) (W (b+j))) →
    let S := (C₀).localSection d
    let P := (C₀).path.rep N p b
    let Y := fun j (x : (C₀).label d) =>
      (calValues (C:=C₀) d N p (b+j) x) ∘ Lattice.translate (o (b+j))
    let wage := fun j => (2+4*stock C₀ (b+j))*B j
    ∃ (a : Fin n → (C₀).label d) (v w : Fin n → store C₀ d p b)
      (x : Fin n → ℕ → (C₀).label d) (u e : Fin n → ℝ),
    (∀ j, mCost C₀ d N p (b+j.val) (a j) ≤ 2*B j.val ∧
      (v j).Format (o b) (C₀).params (W b) ∧ (v j).remBound (o b) (W b) (safety C₀ b) (u j) ∧
      projection ((C₀).labels.level d) (C₀).params (W b).p.threshold (o b) (v j)=0 ∧
      (w j).Format (o b) (C₀).params P ∧ (w j).remBound (o b) P (safety C₀ b) (e j) ∧
      projection ((C₀).labels.level d) (C₀).params P.p.threshold (o b) (w j)=0 ∧
      u j+e j ≤ gain C₀ b (b+j.val)*wage j.val ∧
      ∀ i<j.val, mCost C₀ d N p (b+i) (x j i) ≤ ε*gain C₀ (b+i) (b+j.val)*wage j.val) ∧
    flow C₀ d N p b n (F n)=F 0+
      ∑ j : Fin n, ((v j).density (o b) S (W b)+(w j).density (o b) S P+
        (∑ i ∈ Finset.range j.val, flow C₀ d N p b i (Y i (x j i)))+
        flow C₀ d N p b j.val (Y j.val (a j))) := by
  classical
  filter_upwards [WilsonTrueProjectedLocatedDebit.original R d simple ep] with b single
  intro m N p k n mb top π Γ W course o route gate width F q B read paid
  dsimp only
  let S := (C₀).localSection d
  let E := fun j => (q j).density (o (b+j)) S (W (b+j))
  have iq (j : ℕ) (hj : j<n) : Integrable (E j) (prior G _) :=
    ((q j).envelope S (course.1.walk (b+j) (by omega) (by omega)).truep.valid
      (paid j hj).2.1 (paid j hj).1).integrableC _
  have compare := telescope R d N p b F E n read iq (fun j hj => (paid j hj).2.2.2)
  have split (j : Fin n) := single m N p k j.val mb (by have := j.isLt;omega) π Γ W course o
    (fun t ht => route t (ht.trans j.isLt)) (fun t ht => gate t (ht.trans j.isLt))
    (width j.val j.isLt) (q j.val) (B j.val) (paid j.val j.isLt).1 (paid j.val j.isLt).2.1 (paid j.val j.isLt).2.2.1
  choose a v w x u e rest using split
  refine ⟨a,v,w,x,u,e,fun j=> ⟨(rest j).1,(rest j).2.1,(rest j).2.2.1,(rest j).2.2.2.1,
    (rest j).2.2.2.2.1,(rest j).2.2.2.2.2.1,(rest j).2.2.2.2.2.2.1,
    (rest j).2.2.2.2.2.2.2.1,(rest j).2.2.2.2.2.2.2.2.1⟩,?_⟩
  rw [compare,←Fin.sum_univ_eq_sum_range]
  congr 1
  exact Finset.sum_congr rfl (fun j _ => (rest j).2.2.2.2.2.2.2.2.2)

end YM.Integration.WilsonTrueProjectedLocatedWord
