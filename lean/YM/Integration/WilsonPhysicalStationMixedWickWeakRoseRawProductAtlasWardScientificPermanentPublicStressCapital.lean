import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicStressDetector
import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicMeasuredStress
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicStressCapital
open Function Filter Set MeasureTheory Spec Extraction Table Maxwell Maxwell.Free
open Climb Lattice RG Filter Function Spec OPE Next.Extract PhysMS Trace.Target Trace.Pilot
open PhysicalNext.Repeat.Legato WilsonLimitConstruction Table
open PhysMS.Frame WilsonPhysicalWeakRisingStaff WilsonPhysicalWeakSundial
open scoped Topology BigOperators Classical
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true


open scoped Matrix


open WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicStressRows

variable {G:Gauge}{C:Family G}

theorem booked (C:Family G):∃(n:ℕ)(B:Module.Basis (Fin n) ℂ ((Bel C.book).Field 4))(P:Fin n→Survey C),
    (fun i j=>free (P i) (B j))=(1:Matrix (Fin n) (Fin n) ℂ):=by
  let V:=(Bel C.book).Field 4
  obtain ⟨D,inside,covered,indep⟩:=exists_linearIndependent ℂ (Set.range (free (C:=C)))
  have total:⊤≤Submodule.span ℂ (Set.range ((↑):D→Module.Dual ℂ V)):=by
    rw [Subtype.range_coe,covered,WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicStressDetector.original]
  let f:Module.Basis D ℂ (Module.Dual ℂ V):=Module.Basis.mk indep total
  letI:Fintype D:=FiniteDimensional.fintypeBasisIndex f
  let e:=Fintype.equivFin D
  let f':=f.reindex e
  let B:=f'.dualBasis.map (Module.evalEquiv ℂ V).symm
  have named (i:Fin (Fintype.card D)):∃P:Survey C,free P=f' i:=by
    have row:=inside (e.symm i).property
    simpa only [f',Module.Basis.reindex_apply,f,Module.Basis.mk_apply,Set.mem_range] using row
  choose P matchP using named
  refine ⟨_,B,P,?_⟩
  ext i j
  rw [matchP]
  change f' i ((Module.evalEquiv ℂ V).symm (f'.dualBasis j))=_
  rw [Module.apply_evalEquiv_symm_apply,Module.Basis.dualBasis_apply_self]
  simp [Matrix.one_apply]

theorem original (C:Family G):∃(n:ℕ)(B:Module.Basis (Fin n) ℂ ((Bel C.book).Field 4))(P:Fin n→Survey C),
    (fun i j=>free (P i) (B j))=(1:Matrix (Fin n) (Fin n) ℂ) ∧
    ∀{S:Table C.book}{f:Extraction.Order}(F:Final C f S)(X:Scaling S),Pert.FirstExtension F X→∀a b:Axis,
      Tendsto (fun k:ℕ=>fun j=>B.repr (born F X k a b) j) atTop
        (𝓝 (fun j=>B.repr (Pert.freeStress C.labels a b) j)) ∧
      ∃V:ℝ,0<V ∧ ∀ᶠ k in atTop,(∑j,‖B.repr (born F X k a b) j‖)≤V:=by
  obtain ⟨n,B,P,dual⟩:=booked C
  refine ⟨n,B,P,dual,?_⟩
  intro S f F X first a b
  exact WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicMeasuredStress.original B P (by rw [dual];simp) F X first a b

end YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicStressCapital
end
