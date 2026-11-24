import YM.FVA2.AnyNorm
/-!
# Every admissible normalized linear condition (based), and every spanning tree

No FP hypotheses or costly suppression estimates. For the inversion-regulator finite
formal prescription. Any rooted spanning tree in the quotient graph, include allowing
any root as far as *defining the tree*. Gauge parameter convention throughout is still
the *given* base/root. Even off a different tree `root` all equalities below use that
same actual convention (and no need to assume invariant under all constant gauges).
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.FVA2.TreeBasis.Repoint
open FormalOPE.RG10 FormalOPE.RG10.BlockGauge PertExtension PertExtension.Chart
open Function Filter Set LinearMap Finset SectionBasis
open scoped Topology Classical ContDiff BigOperators
variable {V E W : Type} {D : Loom V E}(G : Gauge)(v : V)(T:D.Truss)

def orbit (v : V)(D : Loom V E): Loom V E:= {D with origin:=v}

-- transport tangent root space (infinitesimal gauge parameters at 0)
variable (D)
def under (v:V)(a:Root D G)(w:Nonroot (orbit v D)): G.Color:= guarded G D a w.val-guarded G D a v
def transfer : Root D G→ₗ[ℝ] Root (orbit v D) G := LinearMap.pi fun i=> ((LinearMap.proj i.val: Sites V G→ₗ[ℝ] G.Color) - LinearMap.proj v) ∘ₗ guarded G D
lemma under_v (a:Root D G)(w:V): guarded G (orbit v D) (transfer D G v a) w= guarded G D a w-guarded G D a v:= by by_cases he:w=v; (subst w; exact (guard_zero G (orbit v D) _).trans (sub_self _).symm); exact guard_off G (orbit v D) _ (⟨ w,he⟩:Nonroot (orbit v D))
lemma d_of (a:Root D G): d G (orbit v D) (transfer D G v a)=d G D a:= by funext i; rw [diff,diff,under_v,under_v]; unfold orbit; dsimp only; abel
lemma under_one (a:Root D G)(w:Nonroot D): guarded G (orbit v D) (transfer D G v a) w.val - guarded G (orbit v D) (transfer D G v a) D.origin = a w:= by rw [under_v,under_v,guard_zero,guard_off]; abel

def vendor : Root (orbit v D) G→ₗ[ℝ] Root D G:= LinearMap.pi fun i=> ((LinearMap.proj i.val: Sites V G→ₗ[ℝ] G.Color)-LinearMap.proj D.origin) ∘ₗ guarded G (orbit v D)
lemma over_v (a:Root (orbit v D) G)(w:V): guarded G D (vendor D G v a) w= guarded G (orbit v D) a w-guarded G (orbit v D) a D.origin:= by by_cases he:w=D.origin; subst w; simp; exact guard_off G D _ (⟨w,he⟩:Nonroot D)
lemma commute (a:Root (orbit v D) G): transfer D G v (vendor D G v a)=a:= by ext1 i; change guarded G D (vendor D G v a) i.val-guarded G D (vendor D G v a) v=_; rw [over_v,over_v,guard_off, show guarded G (orbit v D) a v=0 from guard_zero G (orbit v D) a ]; abel -- replacing v everywhere?

def around : Root D G≃ₗ[ℝ] Root (orbit v D) G:= LinearEquiv.ofLinear (transfer D G v) (vendor D G v) (LinearMap.ext (commute D G v)) (LinearMap.ext (fun p=> funext (under_one D G v p)))
variable {D}
lemma turn_lift (t:FVA2.TreeBasis.Links E G): turn G (orbit v D) t=turn G D t:= rfl

section NormalQueue
variable [Fintype V][Fintype E]
variable [AddCommGroup W][Module ℝ W]

/-- General linear condition on log links around the trivial orbit. jacobian with respect
 to based gauge variables invertible (transverse gauge at 0). Constant sign convention normalized
 here. Converts any allowable condition `K` to `GaugeSlice`.
-/
def chart {G : Gauge} (K:Links E G→ₗ[ℝ] W)(h: Bijective (K ∘ₗ d G D)):= LinearEquiv.ofBijective _ h
abbrev judge {G:Gauge}(K:Links E G→ₗ[ℝ] W)(h:Bijective (K ∘ₗ d G D)): Links E G→ₗ[ℝ] Root D G:= (chart K h).symm.toLinearMap ∘ₗ K
omit [Fintype V] [Fintype E] in
lemma judge_of (K:Links E G→ₗ[ℝ] W)(h:Bijective (K ∘ₗ d G D))(p:Root D G): judge K h (d G D p)=p:= LinearEquiv.symm_apply_apply (chart K h) p

def issue (K:Links E G→ₗ[ℝ] W)(h:Bijective (K ∘ₗ d G D)): SectionBasis D T G where
    L := TreeBasis.enter G T-(d G D) ∘ₗ judge K h ∘ₗ TreeBasis.enter G T
    agreement x := by
       change whereL G T (TreeBasis.enter G T x - d G D ((judge K h) _))=x; rw [map_sub,d_where,sub_zero]; simpa using where_apply G T 0 x
lemma sent (K:Links E G→ₗ[ℝ] W)(h:Bijective (K ∘ₗ d G D))(x:Free T G): judge K h ((issue G T K h).L x)=0:= by change judge K h (TreeBasis.enter G T x- d G D (judge K h _))=_; rw [map_sub, judge_of, sub_self]
lemma reissue (K:Links E G→ₗ[ℝ] W)(h: Bijective (K ∘ₗ d G D)): (issue G T K h).projection=judge K h:= by
     apply LinearMap.ext; intro x; conv_rhs => rw [←(issue G T K h).resolves x]; rw [map_add,judge_of,sent,add_zero]
lemma licence (K:Links E G→ₗ[ℝ] W)(h:Bijective (K ∘ₗ d G D))(A:Links E G): K A=0 ↔ A∈ LinearMap.range (issue G T K h).L:= by
    let e:=issue G T K h; have he(A:Links E G) : (chart K h).symm (K A)=e.projection A:= (DFunLike.congr_fun (reissue G T K h) A).symm
    constructor
    · intro h; obtain hy:=e.resolves A; rw [← he, h, _root_.map_zero, _root_.map_zero,zero_add] at hy; exact ⟨_,hy ⟩
    rintro ⟨x,rfl⟩; apply (chart K h).symm.injective; rw [he, show e.projection ((issue G T K h).L x)=0 from e.in_slice x,map_zero]

end NormalQueue
section
variable (S:(orbit v D).Truss) [Fintype V][Fintype E]
lemma mark : Bijective (pick G S ∘ₗ d G D):= by rw [show ⇑(pick G S ∘ₗ d G D)= (⇑(treeIso G S) ∘ ⇑(around D G v)) from funext (fun x=> by change pick G S (d G D x)=_; rw [← d_of D G v x,picks]; rfl) ]; exact (treeIso G S).bijective.comp (around D G v).bijective
def orbitGauge : SectionBasis D T G := issue G T (pick G S) 
     (mark G v S)

local notation "Z" => orbitGauge G v T S
local notation "K" => pick G S
local notation "L" => (orbitGauge G v T S).L

lemma is_fixed (x: Free T G) : K (L x)=0:= (licence G T K (mark G v S) _).mpr ⟨x,rfl⟩
def priceBasis : Free T G→ₗ[ℝ] Free S G := TreeBasis.restrict G S ∘ₗ L
lemma pricing (x : Free T G) : enter G S (priceBasis G v T S x)=L x:= by apply TreeBasis.full G S; rw [entry,is_fixed]; rw [entry_back]; rfl
lemma reverse (x:Free S G): L (whereL G T (enter G S x))=enter G S x:= by
     obtain ⟨t,h⟩:= (licence G T K (mark G v S) _).mp (entry G S x); change L t=enter G S x at h; rw [←h,(Z).agreement]

def switch : Free T G≃L[ℝ] Free S G:=
    (LinearEquiv.ofLinear (priceBasis G v T S) ((whereL G T) ∘ₗ enter G S) (LinearMap.ext (fun x=> by change TreeBasis.restrict G S (L (whereL G T (enter G S x)))=x; rw [Repoint.reverse,entry_back])) (LinearMap.ext (fun x=> by change whereL G T (enter G S (priceBasis G v T S x))=x; rw [pricing,(Z).agreement]))).toContinuousLinearEquiv
lemma switch_entry (x:Free S G): L ((switch G v T S).symm x)=enter G S x:= Repoint.reverse G v T S x
lemma switch_origin : (switch G v T S).symm 0=0 := map_zero _

lemma tree_ghost (A: Free T G) : (Z).ghosts A=LinearMap.id:= by
    apply LinearMap.ext; intro p; unfold ghosts; change (issue G T K (mark G v S)).projection _=p; rw [reissue]; let H:=mark G v S
    suffices h:K (directed G D (L A) p)=K (d G D p) from Eq.trans (congr_arg (chart K H).symm h) (judge_of G K H p)
    apply funext; intro i; change turn G D (L A) _ i.val=d G D p i.val; rw [at_origin G D _ _ _ (congr_fun (is_fixed G v T S A) i), diff]
lemma tree_fpdet (A:Free T G): (Z).fpdet A=1:= by rw [fpdet, tree_ghost, det_id]
end
open Lattice PertExtension PertExtension.Series PertExtension.Series.Radial Precision
open MeasureTheory MeasureTheory.Measure PowerSeries Wilson GermLaplace Rates
section
variable {G : Gauge} {n:Side} (q:BlockGauge.Vertex n) -- namespace?
variable (Y:(orbit q (rim n)).Truss)(U:ChartRatio G)(H:LocalRatio U)
variable {O:Wilson.Observable G n} (hp:Physical O)(he: Honest O)(hn:_root_.Even n.val)
local notation "L" => orbitGauge G q (staple n) Y
local notation "θ"=> (switch G q (staple n) Y).symm
local notation "μ" => tangent G (staple n).Bulk
variable (G)
def cost (q: BlockGauge.Vertex n)(Y:(orbit q (rim n)).Truss) : Free Y G→ℝ := Wilson.pricing G n ∘ (enter G Y)
variable {G}
def material (q:BlockGauge.Vertex n)(Y:(orbit q (rim n)).Truss)(U: ChartRatio G)(O:Wilson.Observable G n): Free Y G→ℝ := fun x=> O (assemble G n (enter G Y x)) * density Y.Bulk U x
lemma cost_holds : cost G q Y= WilsonPull L ∘ θ:= funext fun x=> congr_arg (Wilson.pricing G n) (switch_entry ..).symm
lemma cost_hot : ContDiffAt ℝ ω (cost G q Y) 0:= by rw [cost_holds]; exact ((switch_origin G q _ Y).symm ▸ (pull_hot L)).comp 0 (θ).contDiff.contDiffAt
lemma cost_stat : Radial.Stationary (cost G q Y):= by rw [cost_holds]; exact rebase_stat θ (pull_stable L)
include hn in
lemma cost_gap : Gap (cost G q Y):= by rw [cost_holds]; exact rebase_gap θ ((pull_hot L).of_le le_top) (pull_gap L hn)
include H
lemma material_holds : material q Y U O= sliceK L U O ∘ θ:= by funext u; unfold material; rw [← tree_density U H (T:=Y),Function.comp_apply,sliceK, tree_fpdet,mul_one, switch_entry, slice,Function.comp_apply,switch_entry ]; rfl
include hp he in
lemma material_hot : ContDiffAt ℝ ω (material q Y U O) 0:= by rw [material_holds q Y U H]; exact ((switch_origin G q _ Y).symm ▸ (sliceK_hot L U H hp he)).comp 0 (θ).contDiff.contDiffAt
variable (ν:Measure (Free Y G))[IsAddHaarMeasure ν]
def treeMoment (O:Wilson.Observable G n): PowerSeries ℝ:= Rates.M ν (material q Y U O) (cost G q Y)
include hn
lemma tree_pos : 0 < constantCoeff (treeMoment q Y U ν 1):= by apply market ν (cost_gap q Y hn) (cost_stat q Y) ((material_hot q Y U H (Physical.one G n) one_honest).of_le le_top); rw [material]; simp_rw [Pi.one_apply,density_zero U H,one_mul]; exact zero_lt_one
include hp he
/-- Compare all observables (products and common vacuum) using any rooted tree slices.
 Distinct volume normalizations fine; Haar link chart ratio formal normalized J.
 Earlier Route kernels use separate trees and measure identities (not using this claim).
-/
theorem tree_value : PowerSeries.mk (Orb.diagonalWith U (Orb.restrictedO O))= treeMoment q Y U ν O * (treeMoment q Y U ν 1)⁻¹:= by
     rw [tree_identity L hn U H hp he]; unfold treeMoment; rw [material_holds q Y U H,material_holds q Y U H,cost_holds q Y]; exact (other_basis ν μ θ ((pull_hot L).of_le le_top) ((sliceK_hot L U H hp he).of_le le_top) ((sliceK_hot L U H (Physical.one G n) one_honest).of_le le_top) (one_core L hn U H)).symm
end
end YM.FVA2.TreeBasis.Repoint
