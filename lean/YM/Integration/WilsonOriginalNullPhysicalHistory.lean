import YM.Integration.WilsonOriginalNullHistory
import YM.Integration.WilsonOriginalNullTransition

/-! The emitted raw sections are genuine canonical-P sources on the same
Wilson run. Only their vacuum and budget enter the raw primary density. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullPhysicalHistory
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Transit WheelP QuadraticLocal QuadraticLocal.Advent
open Function Filter MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext Repeat Legato Graces Roost Org Push.Local
open WilsonOriginalNullCorridor WilsonOriginalNullFiledStep
open scoped Classical BigOperators Topology Matrix.Norms.Frobenius

theorem reprint {G:Gauge} {n:Side} {d:ℕ} {F:Frame G d} (S:SectionData F) (P W:Rep G n)
    (point:W.p=P.p) (vac:W.eval=P.eval) (o:Site n) (α:F.Coeff) :
    (primary o α).density o S W=(primary o α).density o S P := by
  funext U
  rw [primary_density,primary_density,vac]
  congr 1
  change α 0+RG.masked W.p.threshold (S.footprint o) (S.places (F.scaled W.p.threshold⁻¹ (F.core α)) o) U=
    α 0+RG.masked P.p.threshold (S.footprint o) (S.places (F.scaled P.p.threshold⁻¹ (F.core α)) o) U
  rw [point]

variable {G:Gauge} (R:Run G) {m N per k:ℕ}
  (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (W:∀ j,Rep G (R.family.side j per))
  (book:Concourse R.alloy R.kit R.T π Γ m N per k W)
local notation "C₀" => R.family
local notation "P₀" j:max => R.family.path.rep N per j
local notation "F₀" d:max => R.family.labels.level d
local notation "S₀" d:max => R.family.localSection d
local notation "κ" j:max => LocalComparison.forcedDivisor R.family j

include book in
theorem paid_primary {i:ℕ} (entry:m ≤ i) (live:i ≤ N) (d:ℕ) (y:Site (R.family.side i per)) (α:(F₀ d).Coeff) :
    (primary y α).density y (S₀ d) (W i)=(primary y α).density y (S₀ d) (P₀ i) := by
  have step:=book.1.walk i entry live
  exact reprint (S₀ d) (P₀ i) (W i) (step.truep.point.trans (R.makes.wilson.represents N per i live).vac.symm)
    step.view y α

include book in
theorem original (d b n:ℕ) (ε:ℝ) (floor:m ≤ b) (live:b+n ≤ N)
    (o:∀ j,Site (R.family.side j per))
    (route:∀ j<n,o (b+j)=(R.family.path.levels.clock.op (b+j) per).ratio.parent (o (b+j+1)))
    (filed:∀ j<n,Filed C₀ d N per (b+j) W (o (b+j+1)) ε)
    (h:Coefficient (F₀ d) (R.family.side (b+n) per)) (B:ℝ) (form:h.Format (o (b+n)) R.family.params (W (b+n)))
    (paid:h.remBound (o (b+n)) (W (b+n)) (κ (b+n)) B)
    (null:projection (F₀ d) R.family.params (W (b+n)).p.threshold (o (b+n)) h=0) :
    ∃ (v:Coefficient (F₀ d) (R.family.side b per)) (α:ℕ→(F₀ d).Coeff),v.Format (o b) R.family.params (W b) ∧
      v.remBound (o b) (W b) (κ b) (gain C₀ b (b+n)*B) ∧ projection (F₀ d) R.family.params (W b).p.threshold (o b) v=0 ∧
      (∀ j<n,(F₀ d).coeffSize (α j) ≤ ε*gain C₀ (b+j) (b+n)*B) ∧
      flow C₀ d N per b n (h.density (o (b+n)) (S₀ d) (W (b+n)))=v.density (o b) (S₀ d) (W b)+
        ∑ j∈Finset.range n,flow C₀ d N per b j ((primary (o (b+j)) (α j)).density (o (b+j)) (S₀ d) (P₀ (b+j))) := by
  have laws (j:ℕ) (hj:j<n) := (book.1.walk (b+j) (by omega) (by omega)).truep.valid
  obtain ⟨v,α,shaped,priced,zero,fees,read⟩:=WilsonOriginalNullHistory.finite C₀ d N per b W o ε n
    route (fun j hj=>⟨_,_,_,_,_,laws j hj⟩) filed h B form paid null
  refine ⟨v,α,shaped,priced,zero,fees,read.trans ?_⟩
  congr 1
  apply Finset.sum_congr rfl;intro j hj
  have hj':=Finset.mem_range.mp hj
  rw [paid_primary R π Γ W book (i:=b+j) (by omega) (by omega) d]

end YM.Integration.WilsonOriginalNullPhysicalHistory
