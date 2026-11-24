import YM.WilsonCoeffUV.Product.Report.Profiles
/-!
# Evaluated interactions before capture
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Soil
open Gauge Power PathCost Precision Embroider Fountain Cosmos Shard Realm
open PowerSeries
open scoped Topology BigOperators
variable {n c:Side}{U V α β:Type*}{r h D j e i l k:ℕ}{A B C s:ℝ}{G:Gauge}
open Embroider
open scoped ContDiff
-- θ-spun orientation not demanded after testing nonsymmetric profile; color/gauge preserved per root. exact.
variable {u:ℝ}
def drumB (h:ℕ)(t:ℝ):= t^4 * (t^h)⁻¹
lemma drumC (t:ℝ)(p:0≤t)(h:ℕ):0≤drumB h t:=by unfold drumB; positivity
def shoe (T: TowerS G D)(F:Rarity D)(t y:ℝ)(b:Cover): Era G Lounge:= shifted (tuftV (demonstrate (wheelC t y b F.ψ)) T) b
def pupil (k:ℕ)(T:TowerS G D)(F:Rarity D)(t y:ℝ): Era G Lounge:= ∑ b∈ canvasM F t y,drumB k t • shoe T F t y b
lemma placed (h:ℕ) {T:TowerS G D}(F:Rarity D)(v:On k T)(t y:ℝ): Auth k (pupil h T F t y):= Auth.sum fun i _=> (((Auth.tuft (On_auth v) _).shifted i).μ _)
lemma shoeNull (T:TowerS G D)(F:Rarity D)(x y:ℝ)(v:0<x)(o:Cover)(p:o ∉ canvasM F x y): shoe T F x y o=0:=by
   have he j: wheelC x y o F.ψ j=0:= not_ne_iff.mp (fun h=> p (contour F x y j o v h))
   refine Prod.ext (funext fun n=>funext fun i=>funext fun j=> funext fun w=>?_ ) (funext fun i=> funext fun j=>funext fun w=> ?_)
   · ext1 u; change T.1 n i j _ (wheelC x y o F.ψ u)=_; rw [he]; exact map_zero _
   ext1 u; change T.2 i j _ (wheelC x y o F.ψ u)=_; rw [he]; exact map_zero _

def heapZ (P:Patch)(x:Cover×Site P.L): Cover := P.L.val • x.1+ lift x.2
lemma heapZ_eq (P:Patch)(p:Cover): heapZ P (parentC P.L p,wrap P.L p)=p:= congr_arg Prod.fst (show panel P.L Unit (_,_ ,())=(p,()) from Eq.trans (congr_arg (panel P.L Unit) ((patchwork (L:=P.L) (p,())).symm)) (Equiv.apply_symm_apply ..))
lemma heapZ_inj (P:Patch): Injective (heapZ P):= by
   intro x y h; let f (x:Cover × Site P.L) := ((x.1,x.2,()) : Cloth (Co P.L Unit)); have hf: Injective f:= fun a b he=>Prod.ext (congr_arg (fun i:Cloth (Co P.L Unit)=>i.1) he) (congr_arg (fun i:Cloth (Co P.L Unit)=>i.2.1) he); apply hf; exact (panel P.L Unit).injective (Prod.ext h (Subsingleton.elim _ _))
lemma eyelet (P:Patch)(t y:ℝ)(d:Cover)(w:Site P.L)(F:Rarity D)(p:CellR) : wheelC t y (heapZ P (d,w)) F.ψ p=foldWord P w D (wheelC (t*P.L.val) y d F.ψ p):=by change page D _=foldWord _ _ _ (page D _); rw [observed,growingP]; rfl
lemma foreC (P:Patch)(T:TowerS G D)(F:Rarity D)(x y:ℝ)(d:Cover)(w:Site P.L)(p:0<x)(u: d∉ canvasM F (x*P.L.val) y) : shoe T F x y (heapZ P (d,w))=0:=by
   let t:=heapZ P (d,w); have he v:wheelC (x*P.L.val) y d F.ψ v=0:= not_ne_iff.mp (fun h=> u (contour _ _ _ v d (by positivity) h)); have ht v: wheelC x y t F.ψ v=0:=by rw [eyelet,he,map_zero]
   refine Prod.ext (funext fun n=>funext fun i=>funext fun j=> funext fun w=>?_ ) (funext fun i=> funext fun j=>funext fun w=> ?_)
   · ext1 z; change T.1 n i j _ (wheelC x y t F.ψ z)= _; rw [ht]; exact map_zero _
   ext1 z; change T.2 i j _ (wheelC x y t F.ψ z)= _; rw [ht]; exact map_zero _
lemma tiler (P:Patch)(F:Rarity D)(t y:ℝ)(p:0<t)(T: TowerS G D)(k:ℕ) : pupil k T F t y = ∑ j∈ canvasM F (t*P.L.val) y, ∑ i:Site P.L,drumB k t • shoe T F t y (heapZ P (j,i)):=by
    let X:=canvasM F t y; let U:=canvasM F (t*P.L.val) y; let f:=heapZ P; let S:= U.product (Finset.univ:Finset (Site P.L)); let Q:=S.image f; let V:=X∪Q; let s b:=drumB k t • shoe T F t y b; change ∑ i∈X,s i=∑ i∈U,∑ j,s (f (i,j))
    classical
    have h: ∑ i∈X,s i= ∑ i∈V,s i:=Finset.sum_subset (Finset.subset_union_left) fun i _ hi=> by unfold s; rw [shoeNull T F t y p _ hi,smul_zero]
    have hQ:∑ i∈Q,s i=∑ i∈V,s i:=by
       refine Finset.sum_subset Finset.subset_union_right fun i _ hi=>?_ ; let M:=(parentC P.L i,wrap P.L i); rw [←heapZ_eq P i]; unfold s; rw [foreC P T F t y _ _ p,smul_zero]; intro H; exact hi (Finset.mem_image.mpr ⟨M,Finset.mem_product.mpr ⟨H,Finset.mem_univ _⟩, heapZ_eq P i⟩)
    rw [h,←hQ, show Q=S.image f from rfl,Finset.sum_image (heapZ_inj P).injOn]; apply Finset.sum_product' (f:=fun i j=>s (f (i,j)))
-- coin law
lemma drum_law (P:Patch)(h k:ℕ)(t:ℝ)(p:0<t) : drumB h t= drumB h (t*P.L.val)*gradeH P h k*tiara P k:=by unfold drumB gradeH tiara; field_simp; ring

lemma seaWet (T:TowerS G D)(F:Rarity D)(x y:ℝ)(t:On k T):∀ b,Auth k (shoe T F x y b):=fun b=> ((On_auth t).tuft _).shifted b
end YM.WilsonCoeffUV.Mer
