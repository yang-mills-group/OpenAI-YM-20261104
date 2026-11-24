import YM.Integration.WilsonTrueProjectedColumnStep

/-! Each independently transported column on the finite physical interval
is reset at its own actual germ. The upper null bill and each signed
one-block invoice occur with their original contracted gains. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonTrueProjectedColumnDescent
open Filter MeasureTheory Lattice Wilson RG Source Labels
open Trace.Physical Trace.Physical.GermGraph PhysicalNext.Repeat.Legato
open Extra.Histories Extra.Histories.Relay Bid MergeProof
open scoped Topology Matrix.Norms.Frobenius
variable {G : Gauge} {C : Family G} {d N p : ℕ}
local notation "σ" => (C.labels.level d).coeffSize
local notation "Q" => GermGraph.store C d p
local notation "V" => GermGraph.value (C:=C) d N p
local notation "Y" => GermGraph.calValues (C:=C) d N p
local notation "π" => GermGraph.page (C:=C) d p
local notation "X" => GermGraph.measuring C d N p
local notation "U" => GermGraph.transition (C:=C) d N p

abbrev decay (C : Family G) (i : ℕ) := (GermGraph.factor C i)^(-GermGraph.rate)

def wallet (C : Family G) (fee : ℕ → ℝ) (boundary : ℝ) : ℕ → ℕ → ℝ
  | 0, _ => boundary
  | n+1, i => decay C i * wallet C fee boundary n (i+1) + fee i

def retained (C : Family G) : ℕ → ℕ → ℝ
  | 0, _ => 1
  | n+1, i => decay C i * retained C n (i+1)

def invoice (e : ∀ j, Q j) (price : ℕ → ℝ) (i : ℕ) :=
  price i + (2*stock C i)*σ (π i (e i))

/-- The exact remaining top multiplier can be kept when the initial
representative has a cutoff-dependent invoice. -/
theorem bounded (C : Family G) {fee cap : ℕ → ℝ} (boundary ρ : ℝ) (floor stop : ℕ)
    (positive : ∀ i ≥ floor, i ≤ stop → 0 ≤ cap i)
    (decreasing : ∀ i ≥ floor, i < stop → cap (i+1) ≤ cap i)
    (contraction : ∀ i ≥ floor, i < stop → decay C i ≤ ρ)
    (funded : ∀ i ≥ floor, i < stop → fee i ≤ (1-ρ)*cap i) :
    ∀ i ≥ floor, ∀ n, i+n ≤ stop →
      wallet C fee boundary n i ≤ retained C n i * boundary + cap i := by
  intro i hi n
  induction n generalizing i with
  | zero =>
    intro top
    simpa [wallet,retained] using positive i hi (by omega)
  | succ n ih =>
    intro top
    have endpt : i < stop := by omega
    have h := ih (i+1) (by omega) (by omega)
    have loss : 0 ≤ decay C i := Real.rpow_nonneg (le_of_lt (zero_lt_one.trans (factor_positive C i))) _
    calc
      wallet C fee boundary (n+1) i ≤ decay C i * (retained C n (i+1)*boundary + cap (i+1)) +
          (1-ρ)*cap i := add_le_add (mul_le_mul_of_nonneg_left h loss) (funded i hi endpt)
      _ ≤ decay C i * (retained C n (i+1)*boundary) + ρ*cap i + (1-ρ)*cap i := by
        rw [mul_add]
        have hcap := (mul_le_mul_of_nonneg_left (decreasing i hi endpt) loss).trans
          (mul_le_mul_of_nonneg_right (contraction i hi endpt) (positive i hi endpt.le))
        exact add_le_add (add_le_add le_rfl hcap) le_rfl
      _ = retained C (n+1) i * boundary + cap i := by rw [retained]; ring

/-- All the `col j` are the actual submitted columns along one dated
program. Their measured numerical coordinates are recalculated on that
same original Wilson representation. No column salary occurs in the
homogeneous transfer. -/
theorem history (H : C.Makes) {floor stop : ℕ} (top : stop ≤ N)
    (col e : ∀ j, Q j) (v : ℕ → C.label d) {γ ε boundary : ℝ} (price : ℕ → ℝ)
    (opened : ∀ i ≥ floor, i < stop → Opened C d i p)
    (gate : ∀ i ≥ floor, i < stop → Gate C d N p i γ ε)
    (amount : ∀ i ≥ floor, i ≤ stop → X i (v i) = π i (col i))
    (admitted : ∀ i ≥ floor, i < stop → ∃ b, reads d N p i (col i) b)
    (funded : ∀ i ≥ floor, i < stop → reads d N p i (e i) (price i))
    (matched : ∀ i ≥ floor, i < stop → U i (V (i+1) (col (i+1))) = V i (col i) + V i (e i))
    (start : ∃ s : Q stop, reads d N p stop s boundary ∧ π stop s = 0 ∧
      V stop s = Y stop (v stop) - V stop (col stop)) :
    ∀ i ≥ floor, i ≤ stop →
      ∃ s : Q i, reads d N p i s (wallet C (invoice e price) boundary (stop-i) i) ∧
        π i s = 0 ∧ V i s = Y i (v i) - V i (col i) := by
  intro i mi ib
  induction ib using Nat.decreasingInduction with
  | self => simpa [wallet] using start
  | of_succ i ib ih =>
    obtain ⟨q,hq,qn,qv⟩ := ih (by omega)
    obtain ⟨a,showed⟩ := admitted i mi ib
    have hi := opened i mi ib
    obtain ⟨s,_,paid,zero,_,_,represented⟩ := WilsonTrueProjectedColumnStep.original H
      (ib.trans_le top) hi (gate i mi ib) (v (i+1)) (col (i+1)) q (col i) (e i) hq qn
      (by rw [qv]; abel) showed (funded i mi ib) (matched i mi ib)
    have dx : stop-i = (stop-(i+1))+1 := by omega
    refine ⟨s,?_,zero,?_⟩
    · rw [dx,wallet]
      exact paid
    · have a : (fitting d N p i H hi (ib.le.trans top)) (v i) = π i (col i) := amount i mi ib.le
      rw [←a,LinearEquiv.symm_apply_apply] at represented
      exact represented

end YM.Integration.WilsonTrueProjectedColumnDescent
