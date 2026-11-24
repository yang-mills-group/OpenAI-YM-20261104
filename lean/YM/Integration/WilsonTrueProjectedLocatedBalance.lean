import YM.Integration.WilsonTrueProjectedLocatedMerge

/-! A genuine paid trajectory leaves one null account on each of its two
representations.  All earlier physical primary feeds still enter the same field. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonTrueProjectedLocatedBalance
open Filter MeasureTheory Lattice RG Wilson Extra.Histories Source Labels
open Extra.Histories.Relay Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open QuadraticLocal QuadraticLocal.Advent AllOrder AllOrder.Floe AllOrder.Transit WheelP WilsonOriginalNullCorridor
open scoped Classical Topology BigOperators

open FormalBulk08 City Pose RemainderComparison ConnectedActivityE6
open WilsonTrueProjectedPointProgram WilsonTrueProjectedPointInverse
open WilsonTrueProjectedLocatedBasis WilsonTrueProjectedLocatedHistory
open WilsonPinnedWidthTransport WilsonTrueProjectedNaturalFee WilsonTrueProjectedCourse
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G)
local notation "C₀" => R.family


open WilsonTrueProjectedLocatedFunded WilsonTrueProjectedLocatedMerge
theorem original {d N p b n : ℕ} {W : ∀ j,Rep G ((C₀).side j p)}
    {o : ∀ j,Site ((C₀).side j p)} {F : ∀ j,Config G ((C₀).side (b+j) p) → ℂ}
    {price : ℕ → ℝ} {ε total : ℝ} (H : Receipt R d N p b n W o F price ε)
    (paid : (∑ j : Fin n,(H.u j+H.e j)) ≤ total) (live : b≤N)
    (room : Opened C₀ d b p) {σ C Λ δ w : ℝ} (law : (W b).Lawful σ C Λ δ w)
    (dw : d≤(W b).p.order) (pw : d≤(W b).p.power) :
    let S := (C₀).localSection d
    let L := (C₀).labels.level d
    let P := (C₀).path.rep N p b
    ∃ h q : store C₀ d p b,
      h.Format (o b) (C₀).params (W b) ∧ q.Format (o b) (C₀).params P ∧
      h.remBound (o b) (W b) (safety C₀ b) (∑ j,H.u j) ∧ q.remBound (o b) P (safety C₀ b) (∑j,H.e j) ∧
      projection L (C₀).params (W b).p.threshold (o b) h=0 ∧ projection L (C₀).params P.p.threshold (o b) q=0 ∧
      L.coeffSize h.x≤tPrice L (C₀).params (W b)*(∑j,H.u j) ∧ L.coeffSize q.x≤tPrice L (C₀).params P*(∑j,H.e j) ∧
      (∑j,H.u j)+(∑j,H.e j)≤total ∧
      flow C₀ d N p b n (F n) = F 0+h.density (o b) S (W b)+q.density (o b) S P+
        (∑ j : Fin n,∑ i ∈ Finset.range j.val,flow C₀ d N p b i (placed R d N p b o i (H.feed j i)))+
        ∑ j : Fin n,flow C₀ d N p b j.val (placed R d N p b o j.val (H.primary j)) := by
  classical
  intro S L P
  have fee : 0<safety R.family b := Real.sqrt_pos.mpr (Real.exp_pos _)
  have dims:=dimensions d N p b R.makes room.post live
  obtain ⟨h,hf,hp,hz,he⟩:=collect L R.family.params (W b) (o b) S law fee dw pw H.active H.u
    Finset.univ (fun j _=>H.retained j)
  obtain ⟨q,qf,qp,qz,qe⟩:=collect L R.family.params P (o b) S (R.makes.wilson.represents N p b live).good fee
    dims.1 dims.2 H.canonical H.e Finset.univ (fun j _=>H.measured j)
  refine ⟨h,q,hf,qf,hp,qp,hz,qz,raw L R.family.params (W b) (o b) h hf hp dw pw hz,
    raw L R.family.params P (o b) q qf qp dims.1 dims.2 qz,?_,?_⟩
  · rwa [←Finset.sum_add_distrib]
  · rw [H.field,he,qe]
    simp only [Finset.sum_add_distrib]
    abel

end YM.Integration.WilsonTrueProjectedLocatedBalance
