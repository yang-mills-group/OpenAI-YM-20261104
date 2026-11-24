import YM.Integration.WilsonOriginalPublicNodalQuadraticSelf
import YM.Integration.WilsonMeasuredPublicEntranceSeparatedPins

/-! The compact bound on the unconditioned reflected pair with the original cutoff label repeated. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonOriginalPublicNodalQuadraticCutoffSelf
open Function Filter Finset Set Lattice Wilson RG Source Labels Cells OPE Extraction Spec
open Table Table.Pairing Extraction.Banks RG17 PhysicalNext.Repeat.Legato Climb GapsContact Next.Rank
open XSpace XSpace.Normalize XSpace.Rose MS MS.Menus MS.Land MS.Theater Local.Physical
open FVA2 FVA2.Register
open Trace.Pilot PhysMS Frame XSpace.Structure1 Maxwell Maxwell.Wick
open WilsonOriginalBlissMixedGram (columns grades)
open WilsonMeasuredPublicEntranceOrderedPins (physical)
open WilsonPositionHomogeneousFrame (homogeneous)
open WilsonThermometerUnitFilingFourSquare (Arm)
open WilsonOriginalPublicNodalQuadraticSelf (self)
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    (J:ℝ→tower S)(Z:WilsonPrescription G)(h:ℕ)(ax:Axis)(x:RG17.Free R.family h)
    {Y:(Bel R.family.book).Hierarchy}{l:Filter (ℕ×ℕ)}
local notation "C" => R.family
local notation "D" => grades h h
local notation "submitted" r:max => homogeneous F J Z r h x

theorem nodes (simple:G.Simple)(below:l≤f.fuse)(r:ℝ)(A:Arm (C) S l h (submitted r))
    {τ:Type}[Fintype τ](site:ℕ)(o:τ→Fin 2→ Cover)(pos:τ→Points 2)(μ:τ→ℂ)
    (placed:∀t,Order.grid (C) site (o t)=r • pos t)(safe:∀t,Order.grid (C) site (o t)∈conf 2):
    Tendsto (fun w:ℕ×ℕ=>∑t,μ t*physical D site (o t) w.1 w.2
        (columns R ax h h (A.source w) (A.source w))) l
      (𝓝 (∑t,μ t*self R F J Z h ax x r (pos t))):=by
  classical
  apply tendsto_finsetSum
  intro t _
  apply Tendsto.const_mul
  let y:=columns R ax h h A.label A.label
  have cv:∀k,Tendsto (fun w=>(columns R ax h h (A.source w) (A.source w)) k) l (𝓝 (y k)):=by
    intro k
    fin_cases k
    · change Tendsto (fun w=>((C).book.mirrorGroup h (Signed.mirror ax)) (star (A.source w))) _ _
      exact ((C).book.mirrorGroup h _).continuous_of_finiteDimensional.continuousAt.tendsto.comp A.approaches.star
    · exact A.approaches
  have read:=WilsonMeasuredPublicEntranceSeparatedPins.variation R F D site (o t) simple below _ y cv (safe t)
  have proj:(fun k=>S.project (D k) (y k))=Fin.cons (α:=fun k=>S.Field (D k))
      (S.adj F.room.kernel.spin h ax (submitted r)) (fun _=>submitted r):=by
    funext k
    fin_cases k
    · change S.project h ((C).book.adj h ax A.label)=_
      rw [←S.adj_project F.room.kernel.spin,A.represents]
      rfl
    · exact A.represents
  have same:=S.class_agrees S F.room.kernel.laws.toSymmetric (fun _:ℕ=>le_rfl) D (safe t) y
  change Tendsto _ _ (𝓝 (S.classMoment S _ (r • pos t) _))
  rw [←placed t,←proj,same]
  exact read

theorem original (simple:G.Simple)(lead:Leading F J)(earned:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d)
    (below:l≤f.fuse){K:Set (Points 2)}(compact:IsCompact K)(sep:K⊆conf 2):
    ∃B:ℝ,0≤B ∧ ∀ᶠr in trail,∀(A:Arm (C) S l h (submitted r)){τ:Type}[Fintype τ]
      (site:ℕ)(o:τ→Fin 2→ Cover)(pos:τ→Points 2)(μ:τ→ℂ),(∀t,pos t∈K) →
      (∀t,Order.grid (C) site (o t)=r • pos t) → (∀t,Order.grid (C) site (o t)∈conf 2) →
      ∀ε:ℝ,0<ε → ∀ᶠw:ℕ×ℕ in l,‖∑t,μ t*physical D site (o t) w.1 w.2
        (columns R ax h h (A.source w) (A.source w))‖≤(∑t,‖μ t‖)*B+ε:=by
  obtain ⟨B,positive,uniform⟩:=WilsonOriginalPublicNodalQuadraticSelf.bounded R F J Z h ax x simple lead earned compact sep
  refine ⟨B,positive,?_⟩
  filter_upwards [uniform] with r paid
  intro A τ finite site o pos μ hit placed safe ε ep
  have read:=nodes R F J Z h ax x simple below r A site o pos μ placed safe
  have bound:‖∑t,μ t*self R F J Z h ax x r (pos t)‖≤(∑t,‖μ t‖)*B:=by
    apply (norm_sum_le ..).trans
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun t _=>by rw [norm_mul];exact mul_le_mul_of_nonneg_left (paid _ (hit t)) (norm_nonneg _)
  filter_upwards [(Metric.tendsto_nhds.mp read) ε ep] with w close
  rw [dist_eq_norm] at close
  exact (norm_le_norm_sub_add _ _).trans ((add_le_add close.le bound).trans_eq (add_comm ..))

end YM.Integration.WilsonOriginalPublicNodalQuadraticCutoffSelf
