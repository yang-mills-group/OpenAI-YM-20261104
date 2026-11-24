import YM.Integration.FVA1Physical.Round2.QuayLibrary

/-! The independent-bank comparison for mixed Quay proposals is attained
on a calibrated physical theory at any stipulated finite field horizon,
load and order. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Quay
open Function Finset Lattice RG YM.Wilson Tree Precision Source Labels Extra.Histories Marker
open LocalLTE.Sail PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Org RG.Supply
open MergeProof.Accent Bandage.Harmonics Next.Foundations FVA2.CityHistory UVNext.CouplingReset
open Comparison.RG02 RGComparison.Core16 RGComparison.Core16.Descent RGComparison.Core16.WilsonXLocal
open FormalOPE.RG10 FormalOPE.RG10.MultiGauge PertExtension PertExtension.Chart
open Integration.FVA1Physical.Wilson PertExtension.Series.Tested PhysicalNext.Repeat.Roost
open scoped Classical BigOperators


theorem realized_library (G : Gauge) (simple : G.Simple) (p d c order : ℕ) :
    ∃ (X : Metals G) (D : Rolls X.p) (A : Alloy X D) (P : Bolt A)
      (r₀ : ℕ→ℕ) (Y : ∀ d j t,TransferData ((Labels.frames G).level d) (Issue.trail P) j t),
      let C := YM.Family.mk (Issue.trail P) (Next.Foundations.hol G) (Labels.frames G)
        (Next.Foundations.localSection G) r₀ Y
      Spec.Calibrated C ∧ C.Makes ∧ (∀ i, order ≤ (A.B.a.budget i).order) ∧
      PricedLibrary P r₀ Y p d c := by
  obtain ⟨X,D,A,R,M,Ra,p₀,μ,σ,F,F',W,Z,P,T,der,_pen,_bar,_post,_views,_fame,_timed,
    r₀,Y,cal,ok,_bound,H,K,l,q,e,Γ,_port,_stately,a,_lower,_broad,hX,hQ,hr,_eld,
    AX,hM,orders,scales,z,hP,_survey,KX,Fx,hY,_scope,_repository,ι,_pack,_lane,lib⟩ :=
    PhysicalNext.Repeat.Legato.engineProducts simple p order d 1 1 c 1 0 0 0 (1/4)
      (κ:=1) zero_lt_one le_rfl le_rfl (by norm_num) 1
  exact ⟨X,D,A,P,r₀,Y,cal,ok,der,library_price P r₀ Y Γ hY hX hQ lib ok⟩
end YM.Integration.FVA1Physical.Round2.Quay
