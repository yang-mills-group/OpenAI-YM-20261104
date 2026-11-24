import YM.Integration.WilsonOriginalNullPlacedHistory
import YM.Integration.WilsonOriginalNullPlacedJointCenter

/-! Start the finite true null transport from one jointly vanishing signed
coordinate. Its individual heads need no bound at the earlier cutoff. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullPlacedJointHistory
open Function Filter MeasureTheory Lattice RG Wilson Extra.Histories Source Labels
open Extra.Histories.Relay Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato RG05Readout RG05Readout.Address
open WilsonOriginalNullCorridor
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G) (d N p b:ℕ) (W:∀ j,Rep G (R.family.side j p))
    (o:∀ j,Site (R.family.side j p)) {ε:ℝ}
local notation "C₀" => R.family
local notation "F₀" => (C₀).labels.level d
local notation "S₀" => (C₀).localSection d
local notation "P₀" j:max => (C₀).path.rep N p j
local notation "κ" j:max => safety C₀ j
local notation "Φ" j:max x:max => ((calValues (C:=C₀) d N p (b+j) x) ∘ Lattice.translate (o (b+j)))
local notation "ordinary" j:max v:max => Coefficient.density v (o (b+j)) S₀ (W (b+j))
local notation "physical" j:max v:max => Coefficient.density v (o (b+j)) S₀ (P₀ (b+j))

theorem finite (ep:0 ≤ ε) : ∀ n:ℕ, b+n ≤ N →
    (∀ j<n, o (b+j) = ((C₀).path.levels.clock.op (b+j) p).ratio.parent (o (b+j+1))) →
    (∀ j<n, ∃ a c f t s:ℝ,(W (b+j)).Lawful a c f t s) →
    (∀ j<n,Opened C₀ d (b+j) p) →
    (∀ j<n,WilsonOriginalNullPlacedParallel.Joined C₀ d N p (b+j) W (o (b+j+1)) ε) →
    (W (b+n)).p=(P₀ (b+n)).p →
    (∀ U,(W (b+n)).eval U=(P₀ (b+n)).eval U) →
    ∀ (h k:Coefficient F₀ ((C₀).side (b+n) p)) (B D:ℝ),
      h.Format (o (b+n)) (C₀).params (W (b+n)) → h.remBound (o (b+n)) (W (b+n)) (κ (b+n)) B →
      k.Format (o (b+n)) (C₀).params (P₀ (b+n)) → k.remBound (o (b+n)) (P₀ (b+n)) (κ (b+n)) D →
      projection F₀ (C₀).params (W (b+n)).p.threshold (o (b+n)) h+
        projection F₀ (C₀).params (P₀ (b+n)).p.threshold (o (b+n)) k=0 →
      ∃ (v w:Coefficient F₀ ((C₀).side b p)) (x:ℕ→(C₀).label d) (u e:ℝ),
        v.Format (o b) (C₀).params (W b) ∧ v.remBound (o b) (W b) (κ b) u ∧
        projection F₀ (C₀).params (W b).p.threshold (o b) v=0 ∧
        w.Format (o b) (C₀).params (P₀ b) ∧ w.remBound (o b) (P₀ b) (κ b) e ∧
        projection F₀ (C₀).params (P₀ b).p.threshold (o b) w=0 ∧
        u+e ≤ gain C₀ b (b+n)*(B+D) ∧
        (∀ j<n,mCost C₀ d N p (b+j) (x j) ≤ ε*gain C₀ (b+j) (b+n)*(B+D)) ∧
        flow C₀ d N p b n (ordinary n h+physical n k) =
          v.density (o b) S₀ (W b)+w.density (o b) S₀ (P₀ b) +
          ∑ j∈Finset.range n,flow C₀ d N p b j (Φ j (x j)) := by
  intro n live route laws home gates same quiet h k B D hf hp kf kp null
  obtain ⟨vf,vp,vn,wf,wp,wn,field⟩:=WilsonOriginalNullPlacedJointCenter.zero F₀ (C₀).params S₀
    (o (b+n)) (W (b+n)) (P₀ (b+n)) same quiet h k hf hp kf kp null
  rw [field]
  exact WilsonOriginalNullPlacedHistory.finite R d N p b W o ep n live route laws home gates _ _ B D vf vp vn wf wp wn

end YM.Integration.WilsonOriginalNullPlacedJointHistory
