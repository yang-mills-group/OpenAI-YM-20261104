import YM.WilsonCoeffUV.Product.Report.CostsFromSections
/-!
# Transmissions preserve path layout
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
-- warmth nearest.
def VisitsT (φ:Rarity D)(t y:ℝ)(o:CellR): Finset Cover:= by classical exact (canvasM φ t y).filter (fun i=> wheelC t y i φ.ψ o≠0)
lemma visiting {φ:Rarity D}{t y:ℝ}{o:CellR}{u:Cover}(v:0<t): u∈ VisitsT φ t y o ↔ wheelC t y u φ.ψ o≠0:=by
   classical
   unfold VisitsT; exact ⟨fun h=>(Finset.mem_filter.mp h).2,fun h=> Finset.mem_filter.mpr ⟨contour φ t y o u v h,h⟩⟩

def saddleP (L:Side)(S: Finset Cover): ProfileW:=fun x=> if h:S.Nonempty then S.inf' h fun i=> Bank.terrain.gap (parentC L i) x else 0
lemma launchS (L:Side){S: Finset Cover}{i:Cover}(p:i∈S)(j): saddleP L S j≤ Bank.terrain.gap (parentC L i) j:= by unfold saddleP; rw [dif_pos ⟨i,p⟩]; exact Finset.inf'_le _ p
lemma summitT (L:Side){S:Finset Cover}(p:S.Nonempty)(j):∃ i∈S,saddleP L S j=Bank.terrain.gap (parentC L i) j:=by unfold saddleP; rw [dif_pos p]; apply Finset.exists_mem_eq_inf'
lemma angleC (L:Side){S: Finset Cover}(p:S.Nonempty): AngleSea (saddleP L S):=by
    intro i j; obtain ⟨k,h,he⟩:=summitT L p j; rw [he]; exact (launchS L h i).trans (Bank.terrain.tri _ _ _)
lemma visita (P:Patch)(φ:Rarity D)(x y:ℝ)(o:CellR)(v:0<x)(b:Cover)(p:b∈VisitsT φ x y o): parentC P.L b∈VisitsT φ (x*P.L.val) y o:=by
    apply (visiting (show 0<x*P.L.val by positivity)).mpr; intro hx; apply (visiting v).mp p; nth_rw 1 [← heapZ_eq P b]; rw [eyelet,hx,map_zero]
-- sup norm
lemma reachFit (φ:Rarity D)(x y:ℝ)(o:CellR)(v:0<x)(i:Cover)(p:i∈VisitsT φ x y o): x*Bank.terrain.gap 0 i ≤ 4*radiusH φ x y:=by
   have he:= hall_fit φ x y o i ((visiting v).mp p); apply (mul_le_mul_of_nonneg_left (show (Bank.terrain.gap 0 i:ℝ)≤4*‖actualW i‖ from by rw [show Bank.terrain.gap 0 i=size i from by unfold Bank.terrain; simp]; exact actual_within i) v.le).trans; unfold radiusH; rw [abs_of_pos v] at he ⊢; linarith only [he]
lemma snowFit (P:Patch)(φ:Rarity D)(x y z:ℝ)(o:CellR)(v:0<x)(hx:x*P.L.val≤1)(hv: radiusH φ (x*P.L.val) y ≤ z) (p:(VisitsT φ x y o).Nonempty)(i):
    let η:= x*P.L.val; η* Bank.terrain.gap 0 i≤4*z+saddleP P.L (VisitsT φ x y o) i:=by
    intro η; obtain ⟨a,h,H⟩:= summitT P.L p i; rw [H]; have hη:0< η:=by unfold η; positivity
    let L:=parentC P.L a; have he : η*Bank.terrain.gap 0 L ≤ 4*z:= (reachFit φ η y o hη L (visita P φ x y o v a h)).trans (by linarith)
    apply (mul_le_mul_of_nonneg_left (show (Bank.terrain.gap 0 i:ℝ)≤ Bank.terrain.gap 0 L+(Bank.terrain.gap L i:ℝ) by exact_mod_cast Bank.terrain.tri 0 L i) hη.le).trans; rw [mul_add]; exact add_le_add he (mul_le_of_le_one_left (by positivity) hx)
-- D may differ fields
lemma orbital (x y:ℝ)(o:CellR)(a b: Cover)(p q:CellR)(u:0<x): dist (address x y o a p.val) (address x y o b q.val) ≤ x*(1+ Bank.terrain.gap a b):=by
   have he: dist p.val q.val≤1:=by rw [dist_eq_norm]; exact (norm_sub_le ..).trans ((add_le_add (c_norm p) (c_norm q)).trans (by norm_num))
   rw [dist_eq_norm] at he ⊢; unfold address position; rw [show x • actualW a-y • o.val+x • p.val-(x • actualW b-y • o.val+x • q.val)=x • ((actualW a-actualW b)+(p.val-q.val)) by rw [smul_add,smul_sub,smul_sub]; abel, norm_smul,Real.norm_eq_abs,abs_of_pos u]; apply mul_le_mul_of_nonneg_left _ u.le; rw [add_comm (1:ℝ)]; exact (norm_add_le ..).trans (add_le_add (by rw [← dist_eq_norm]; exact actual_dis ..) he)

def ClearDay (φ:Rarity D)(ψ:Rarity h)(x:ℝ): Prop:= ∀ a∈tsupport φ.ψ.val,∀ b∈tsupport ψ.ψ.val, x ≤ dist a b
lemma escape (P:Patch)(φ:Rarity D)(ψ:Rarity h)(x y t:ℝ)(o:CellR)(hp:0<x)(v:ClearDay φ ψ t)(a b)(p:a∈VisitsT φ x y o)(q:b∈VisitsT ψ x y o):
    let η:=x*P.L.val; t/η≤ 1+Bank.terrain.gap (parentC P.L a) (parentC P.L b):=by
    intro η; have hx:0<η:=by unfold η; positivity
    let L:=parentC P.L a; let M:=parentC P.L b
    obtain ⟨A,hA⟩:= featureV φ η y o L ((visiting hx).mp (visita P φ x y o hp _ p)); obtain ⟨B,hB⟩:=featureV ψ η y o M ((visiting hx).mp (visita P ψ x y o hp _ q)); apply (div_le_iff₀ hx).mpr; rw [mul_comm]; exact (v _ hA _ hB).trans (orbital η y o L M A B hx)
lemma disjointly (P:Patch)(φ:Rarity D)(ψ:Rarity h)(x y t z:ℝ)(o:CellR)(hp:0<x)(hv:x*P.L.val≤1)(v:ClearDay φ ψ t)(he:0<t)(hφ:radiusH φ (x*P.L.val) y≤z)(hψ:radiusH ψ (x*P.L.val) y≤ z) (p:(VisitsT φ x y o).Nonempty)(q:(VisitsT ψ x y o).Nonempty):
    let η:=x*P.L.val; SplitHill (saddleP P.L (VisitsT φ x y o)) (saddleP P.L (VisitsT ψ x y o)) η (4*z) (t/η):=by
    intro η; have hh:0<η:=by unfold η; positivity
    refine ⟨angleC _ p,angleC _ q,by have ht:= (fieldCap ..).trans hφ; linarith, div_pos he hh,hh.le,hv, snowFit P φ x y z o hp hv hφ p,snowFit P ψ x y z o hp hv hψ q,fun d e=>?_⟩
    obtain ⟨a,p,h⟩:=summitT _ p d; obtain ⟨b,v',f⟩:= summitT _ q e
    rw [h,f,Bank.terrain.swap (parentC P.L b) e]; apply (escape P φ ψ x y t o hp v a b p v').trans; simp only [add_assoc]; apply add_le_add_right; exact (by exact_mod_cast ((Bank.terrain.tri (parentC P.L a) d (parentC P.L b)).trans (Nat.add_le_add_left (Bank.terrain.tri d e (parentC P.L b)) _)))
end YM.WilsonCoeffUV.Mer
