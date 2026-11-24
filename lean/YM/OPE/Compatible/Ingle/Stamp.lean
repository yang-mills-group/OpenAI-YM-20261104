import YM.OPE.Compatible.Ingle.Type
import YM.Extra.FREE_DETECTOR_ALGEBRA.Rank
/-! # both real Hilbert morphisms finite -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent MeasureTheory RG Wilson Exterior Stationary Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open Module Silt.Float Drift Quit Quit.Jac
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open Source Labels Source.Drops WardBin Prairies
open Finset
variable {G:Gauge}{k i r n d m:ℕ}
lemma GrainΩ (G:Gauge)(d:ℕ) (F:Labels.Frame G d) : FiniteDimensional ℝ F.Coeff ∧ Nonempty (F.Coeff ≃ₗ[ℝ] Carton G d):=⟨by infer_instance,⟨ ((LinearEquiv.ofBijective (CacheM G d) ⟨ClanM G d,WholeM G d⟩).trans (F.coords.restrictScalars ℝ)).symm⟩⟩
noncomputable def PrismM (F:Frames G)(d:ℕ): Carton G d→ₗ[ℝ] (Maxwell.freeTable F).Field d:=(((Extra.FD.exactField F d).symm.toLinearMap ∘ₗ (Maxwell.observable G d).rangeRestrict).restrictScalars ℝ) ∘ₗ CacheM G d
lemma EquaR (F:Frames G)(p:Carton G d) : PrismM F d p=0 ↔ ∀ i,(p i).1∈ Ghost G d i.val ∧ (p i).2∈ Ghost G d i.val:=by
       rw [← Ghostly p]; let A:= Extra.FD.exactField F d; let W:=Maxwell.observable G d; change A.symm (W.rangeRestrict (CacheM G d p))=0 ↔ W (CacheM G d p)=0; rw [map_eq_zero_iff A.symm A.symm.injective]; exact ⟨fun h=>congr_arg Subtype.val h,fun h=>Subtype.ext h⟩
section
variable (A:(i:ℕ)→Submodule ℝ (Bead G d i)) (F:Frames G)(hA:∀ i:Fin (d+1), IsCompl (Ghost G d i.val) (A i.val))
noncomputable abbrev SealΩ := (j:Fin (d+1))→ ↥(A j.val) × ↥(A j.val)
noncomputable def Φs:SealΩ A →ₗ[ℝ] Carton G d:={ toFun p i:= ⟨((p i).1).val,((p i).2).val⟩,map_add' _ _:=rfl,map_smul' _ _:=rfl }
noncomputable abbrev πCut := PrismM F d ∘ₗ Φs A
private lemma complementaryZero {E : Type*} [AddCommGroup E] [Module ℝ E]
    {K A : Submodule ℝ E} (h : IsCompl K A) (x : A) (hx : x.val ∈ K) : x = 0 := by
  apply Subtype.ext
  have hv : x.val ∈ K ⊓ A := ⟨hx, x.property⟩
  rw [h.inf_eq_bot] at hv
  exact (Submodule.mem_bot ℝ).mp hv

private lemma complementaryRepresentative {E : Type*} [AddCommGroup E] [Module ℝ E]
    {K A : Submodule ℝ E} (h : IsCompl K A) (x : E) : ∃ v : A, x - v.val ∈ K := by
  have hx : x ∈ K ⊔ A := h.sup_eq_top ▸ Submodule.mem_top
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
  exact ⟨⟨w, hw⟩, by simpa using hu⟩

private lemma prismSurjective (F : Frames G) (d : ℕ) : Surjective (PrismM F d) := by
  exact (Extra.FD.exactField F d).symm.surjective.comp
    ((LinearMap.surjective_rangeRestrict (Maxwell.observable G d)).comp (WholeM G d))

private lemma bijectiveFromRepresentatives {X Y V : Type*} {f : X → V} {g : Y → V}
    (hg : Injective g) (hf : Surjective f) (h : ∀ x, ∃ y, f x = g y) : Bijective g := by
  refine ⟨hg, ?_⟩
  intro v
  obtain ⟨x, hx⟩ := hf v
  obtain ⟨y, hy⟩ := h x
  exact ⟨y, hy.symm.trans hx⟩

include hA

private lemma sealInjective : Injective (πCut A F) := by
  rw [← LinearMap.ker_eq_bot]
  apply LinearMap.ker_eq_bot'.2
  intro p hp
  have hx := (EquaR F (Φs A p)).1 hp
  funext i
  exact Prod.ext (complementaryZero (hA i) (p i).1 (hx i).1)
    (complementaryZero (hA i) (p i).2 (hx i).2)

private lemma sealRepresentative (y : Carton G d) : ∃ v : SealΩ A, PrismM F d y = πCut A F v := by
  choose q hq using fun i : Fin (d + 1) => complementaryRepresentative (hA i) (y i).1
  choose r hr using fun i : Fin (d + 1) => complementaryRepresentative (hA i) (y i).2
  let v : SealΩ A := fun i => (q i, r i)
  have hp : PrismM F d (y - Φs A v) = 0 := (EquaR F _).2 fun i => ⟨hq i, hr i⟩
  rw [map_sub] at hp
  exact ⟨v, sub_eq_zero.mp hp⟩

set_option maxHeartbeats 200000 in
lemma σrank : Bijective (πCut A F):=by
  exact bijectiveFromRepresentatives (f := PrismM F d) (g := πCut A F)
    (sealInjective A F hA) (prismSurjective F d) (sealRepresentative A F hA)
noncomputable def GradesSeal : SealΩ A≃ₗ[ℝ] (Maxwell.freeTable F).Field d:= LinearEquiv.ofBijective _ (σrank A F hA)
omit hA in lemma SupportQ {L:Register G}{S:Table L} {s:S.RealSpin}(A':(i:ℕ)→ Submodule ℝ (Bead G d i)) (hr:∀ i:Fin (d+1),IsCompl (Ghost G d i.val) (A' i.val)) (hp: Maxwell.Ranks S s): Nonempty (S.Field d ≃ₗ[ℝ] SealΩ A'):=by
       obtain ⟨h,H'⟩:= hp; obtain ⟨f,u,hF⟩:= H' d; exact ⟨(f.restrictScalars ℝ).trans ((GradesSeal A' _ hr).symm)⟩
end
end YM.OPE.Stroke
