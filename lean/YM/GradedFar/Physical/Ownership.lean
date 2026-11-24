import YM.GradedFar.Physical.Legs
import YM.GradedFar.Physical.Loom
import YM.GradedFar.Horizon.Scale

/-!
# G.2-type bound used for expanding & shrinking in the real filtered basis
(Preserving appointments.)
-/
namespace YM.FVA2.GradedFar.Physical
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open Moving Growth Pose Books
open Scale Dframe
open scoped Topology BigOperators Classical
variable {G : Gauge} {n m d h : ℕ} {I:Type} (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {simple : G.Simple}
    {A : MS.Land.Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
variable {R : Family G} {f : Extraction.Order} {P : Table R.book}
    (U : Spec.Final R f P) (Q : OPE.Orbits.Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
    (J K : FramesH P) (θ : ℝ→ℝ) (hq : Earned N M U J K θ) (he : oriented U K)
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G
local notation "F"=> familyPoint U J
local notation "F'"=> familyPoint U K
local notation "V"=> U.sector.derivatives
local notation "Ch"=> RowSpace G
open Horizon

/-- Full span isomorphism, same basis as throughout. -/
def mapK (r : ℝ)(d : ℕ): Ch d ≃L[ℂ] P.Field d := ((chair G d).symm.trans (K r d)).toContinuousLinearEquiv
lemma mapK_apply (r : ℝ)(d : ℕ)(u : Sec G d): mapK K r d (chair G d u)=K r d u:=by
    change K r d ((chair G d).symm _) = _; rw [LinearEquiv.symm_apply_apply]
lemma applied_symm (r : ℝ)(d : ℕ)(u : Sec G d): (mapK K r d).symm (K r d u)= chair G d u:= by
    rw [←mapK_apply K, ContinuousLinearEquiv.symm_apply_apply]
lemma action (d : ℕ) (r s:ℝ) (x:Ch d): mapK K r d (Moving.Zenith (next K d) r s x) = mapK K (resize r s) d x:= by
    obtain ⟨x,rfl⟩:= (chair G d).surjective x; rw [Moving.Zenith,appointed,mapK_apply, mapK_apply]; exact LinearEquiv.apply_symm_apply ..
lemma action' (d : ℕ) (r s : ℝ) (x:Ch d) : mapK K (resize r s) d (Moving.downward (next K d) r s x)=mapK K r d x:= by
    obtain ⟨x,rfl⟩:= (chair G d).surjective x; rw [Moving.downward,appointed,mapK_apply,mapK_apply]; exact LinearEquiv.apply_symm_apply ..

/-- Price on projection to each *actual* layer, using supplied Q. -/
def extracted (d j:ℕ) (r:ℝ) : Ch d→L[ℂ]P.Field j := LinearMap.toContinuousLinearMap
    (Q.cutTest j d ∘ₗ (mapK K r d).toLinearEquiv.toLinearMap)

include H hq he
lemma brought (d j:ℕ): ∃ k : ℕ,∃ C : ℝ,0 < C ∧ ∀ᶠ r in τ, ‖extracted U Q K d j r‖ ≤ C*r^j * (1+degrees r)^k := by
    refine pushed N M H θ (next K d) ((hq.short 1 d le_rfl).2) (extracted U Q K d j) ?_ j ?_
    · filter_upwards with r; intro s hs; ext1 x; apply congrArg (Q.cutTest j d); exact (action' K d r s x).symm
    refine eventually_all.mpr (fun b=> ?_)
    let q:= flash b
    let u:= O.Score.vertex q.item
    have h: u= u:=rfl
    let A := size_le b
    have he0: up A u=theory b:= rfl
    filter_upwards [he.raises _ _ A] with r hr hh
    change Q.cutTest j d (mapK K r d (chair G d _))=0
    rw [mapK_apply,←he0,hr,Q.cut_rise]
    exact Q.kills_lower j b.size hh _
set_option linter.unusedSectionVars false in
lemma inverse_books (d : ℕ) : ∃ k : ℕ,∃ C : ℝ,0 < C ∧ ∀ᶠ r in τ, ‖(mapK K r d).symm.toContinuousLinearMap‖ ≤ r⁻¹^d*C*(1+degrees r)^k := by
    refine fetched N M H θ (next K d) (hq.short 1 d le_rfl).2 _ ?_
    filter_upwards with r; intro s hs; ext1 x; apply (mapK K r d).injective; change mapK K r d ((mapK K r d).symm x)=mapK K r d (Moving.Zenith (next K d) r s _); rw [ContinuousLinearEquiv.apply_symm_apply,action]; exact (ContinuousLinearEquiv.apply_symm_apply (mapK K (resize r s) d) x).symm
end
end YM.FVA2.GradedFar.Physical
