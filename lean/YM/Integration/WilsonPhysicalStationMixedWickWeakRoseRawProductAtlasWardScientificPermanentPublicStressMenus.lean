import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicStressCapital
import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicJetSalary
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicStressMenus
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


variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
def height (t:(Bel C.book).Tag):Bool→ℕ
  | true=>4
  | false=>t.1
def width {D:ℕ}(t:(Bel C.book).Tag):Bool→ℕ
  | true=>D
  | false=>Module.finrank ℂ ((Bel C.book).Field t.1)
def basis {D:ℕ}(B:Module.Basis (Fin D) ℂ ((Bel C.book).Field 4))(t:(Bel C.book).Tag):
    ∀flag,Module.Basis (Fin (width (D:=D) t flag)) ℂ ((Bel C.book).Field (height t flag))
  | true=>B
  | false=>Module.finBasis ℂ ((Bel C.book).Field t.1)
def pupil (F:Final C f S)(X:Scaling S)(t:(Bel C.book).Tag)(ab:Axis×Axis)(k:ℕ):
    ∀flag,(Bel C.book).Field (height t flag)
  | true=>born F X k ab.1 ab.2
  | false=>t.2

theorem original (C:Family G):∃(D:ℕ)(B:Module.Basis (Fin D) ℂ ((Bel C.book).Field 4)),
    ∀{S:Table C.book}{f:Extraction.Order}(F:Final C f S)(X:Scaling S),Pert.FirstExtension F X→
      ∀{n:ℕ}(q:Fin n→(Bel C.book).Tag)(marks:Fin n→Bool)(ab:Fin n→Axis×Axis),∃V:ℝ,0<V ∧
        ∀ᶠ k in atTop,WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicJetSalary.salary (fun i=>basis B (q i) (marks i))
          (fun i=>pupil F X (q i) (ab i) k (marks i))≤V:=by
  obtain ⟨D,B,P,_,budget⟩:=WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicStressCapital.original C
  refine ⟨D,B,?_⟩
  intro S f F X earned n q marks ab
  have own (t:(Bel C.book).Tag)(a:Axis×Axis)(flag:Bool):∃v:ℝ,0<v ∧∀ᶠk:ℕ in atTop,
      (∑j,‖(basis B t flag).repr (pupil F X t a k flag) j‖)≤v:=by
    cases flag with
    | true=>exact (budget F X earned a.1 a.2).2
    | false=>
      let s:=∑j,‖(basis B t false).repr t.2 j‖
      have hn : 0 ≤ s :=Finset.sum_nonneg fun _ _=>norm_nonneg _
      refine ⟨s+1,by positivity,Filter.Eventually.of_forall fun _=>?_⟩
      change s ≤ s+1
      linarith
  choose v positive paid using fun i=>own (q i) (ab i) (marks i)
  refine ⟨∏i,v i,Finset.prod_pos fun i _=>positive i,?_⟩
  filter_upwards [Filter.eventually_all.mpr paid] with k budget
  exact Finset.prod_le_prod (fun i _=>Finset.sum_nonneg fun _ _=>norm_nonneg _) fun i _=>budget i

end YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicStressMenus
end
