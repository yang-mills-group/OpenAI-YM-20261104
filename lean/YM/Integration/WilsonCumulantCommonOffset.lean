import YM.Integration.WilsonReportCashierConnected
import YM.Integration.WilsonObservedGridShift

/-! The reported finite connected displacement measures only relative
physical offsets. A common microscopic translate contributes exactly zero. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCumulantCommonOffset
open Function Finset MeasureTheory Lattice Wilson RG Source Marker Multi Extraction
open Push.GridApprox Extra.Trajectories WilsonReportMomentDifference WilsonReportCashierConnected
open scoped Classical BigOperators
variable {G : Gauge} {C : Family G} {n N p k : ℕ}

theorem moments (Γ : Census (Fin n)) (d : Fin n → ℕ) (v : (i:Fin n) → C.label (d i))
    (y : Fin n → Site (C.side N p)) (q : Site (C.side N p)) :
    microscopic Γ C (fun i => C.O N p (v i) (y i+q)) = microscopic Γ C (fun i => C.O N p (v i) (y i)) := by
  apply Marker.Poly.ext; intro s
  let X := fun U => ∏ i ∈ s.val, C.O N p (v i) (y i) U
  change moment (C.beta N p) (fun U => ∏ i ∈ s.val, C.O N p (v i) (y i+q) U) = moment (C.beta N p) X
  have equal : (fun U => ∏ i ∈ s.val, C.O N p (v i) (y i+q) U) = X ∘ translate q := by
    funext U; simp only [X,Function.comp_apply,Family.O,TransferData.cylinder,initial,Pi.smul_apply,
      SectionData.places_trans]
  have cont : Continuous X := continuous_finsetProd _ fun i _ => C.continuousO N p (d i) (v i) (y i)
  have h := moment_pull (C.beta N p) 1 q X (cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  rw [show pull (K:=G.El) 1 q = Lattice.translate q from funext (pull_one q)] at h
  rw [equal]; exact h

theorem observed_shift (Γ : Census (Fin n)) (d : Fin n → ℕ) (v : (i:Fin n) → C.label (d i))
    (y : Fin n → Site (C.side N p)) (q : Site (C.side N p)) (s : Γ.Mode) :
    observed Γ d v (fun i => y i+q) s = observed Γ d v y s := by
  unfold observed; rw [moments (C:=C) (N:=N) (p:=p) Γ d v y q]

def anchored (hk : k ≤ N) (y : Fin n → Site (C.side N p)) (i : Fin n) :=
  anchor C.S p hk ((C.S.toDepth hk p).parent (y i))

theorem relative (Γ : Census (Fin n)) (hk : k ≤ N) (d : Fin n → ℕ) (v : (i:Fin n) → C.label (d i))
    (y : Fin n → Site (C.side N p)) (q : Site (C.side N p)) (s : Γ.Mode) :
    displaced Γ hk d v y s = observed Γ d v (fun i => y i-q) s - observed Γ d v (anchored hk y) s := by
  let row (w : Fin n → Site (C.side N p)) := observed (C:=C) (N:=N) (p:=p) Γ d v w s
  let b := row (anchored (C:=C) (N:=N) (p:=p) hk y)
  change row y - b = row (fun i => y i-q) - b
  apply congrArg (fun a : ℂ => a-b)
  have moved : row (fun i => y i+(-q)) = row y := observed_shift (C:=C) (N:=N) (p:=p) Γ d v y (-q) s
  rw [show (fun i => y i-q) = (fun i => y i+(-q)) from funext fun i => sub_eq_add_neg ..]
  exact moved.symm

private theorem local_mode {V : Type} [Fintype V] [DecidableEq V] {Γ : Census V}
    (A B : Marker.Poly Γ) (s : Γ.Mode) (a₀ : A.part Γ.quiet=1) (b₀ : B.part Γ.quiet=1)
    (same : ∀ t : Γ.Mode, t.val ⊆ s.val → A.part t = B.part t) :
    (connected A).part s = (connected B).part s := by
  rw [Comparison.RG02.Cumulants.log_partition A a₀,Comparison.RG02.Cumulants.log_partition B b₀]
  apply sum_congr rfl; intro t ht; congr 1
  apply prod_congr rfl; intro z hz
  apply same
  have hh := (Finset.mem_filter.mp ht).2
  intro i hi; rw [← hh]; exact Finset.mem_biUnion.mpr ⟨z,hz,hi⟩

theorem uniform (Γ : Census (Fin n)) (hk : k ≤ N) (d : Fin n → ℕ) (v : (i:Fin n) → C.label (d i))
    (y : Fin n → Site (C.side N p)) (q : Site (C.side N p)) (s : Γ.Mode)
    (same : ∀ i ∈ s.val, y i-anchored hk y i = q) : displaced Γ hk d v y s = 0 := by
  rw [relative (C:=C) (N:=N) (p:=p) Γ hk d v y q]
  have single (i : Fin n) (h : i ∈ s.val) : y i-q = anchored hk y i := sub_eq_iff_eq_add.mpr (by
    have ir := sub_eq_iff_eq_add.mp (same i h); simpa only [add_comm] using ir)
  let a := fun i => y i-q
  let b := anchored hk y
  let A := microscopic Γ C (fun i => C.O N p (v i) (a i))
  let B := microscopic Γ C (fun i => C.O N p (v i) (b i))
  have ab (t : Γ.Mode) (ht : t.val ⊆ s.val) : A.part t = B.part t := by
    change moment (C.beta N p) (fun U => ∏ i∈t.val, C.O N p (v i) (a i) U) =
      moment (C.beta N p) (fun U => ∏ i∈t.val,C.O N p (v i) (b i) U)
    congr 1; funext U; exact prod_congr rfl fun i hi => congrArg (fun z => C.O N p (v i) z U) (single i (ht hi))
  change (connected A).part s - (connected B).part s = 0
  have start (Z : Fin n → Config G (C.side N p) → ℂ) : (microscopic Γ C Z).part Γ.quiet = 1 := by
    change moment _ (fun U => ∏ i ∈ (∅ : Finset (Fin n)), Z i U) = 1; simp [moment]
  exact sub_eq_zero.mpr (local_mode A B s (start _) (start _) ab)

end YM.Integration.WilsonCumulantCommonOffset
