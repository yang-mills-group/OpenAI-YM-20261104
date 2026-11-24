import YM.OPE.Compatible.Atrium.Stout
/-!
# Local patch frame pre-rotor. Lives in period-blind shelf. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Tree Exterior Stationary Woody Next.Foundations Planned.PrimaryIntegral295.Carrier
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{c f:Side}{S:StepData c f}
namespace Script
section
variable (G) (P:Patch)
def theatre : Finset (Cover × Tile G P.L) := (insert 0 ((playhouse P).image (cellar P.L))) ×ˢ univ
abbrev maskShelf:= shelf (theatre G P)
def chooseS (p:Cover)(v: Tile G P.L): maskShelf G P→L[ℝ] ℝ:= if h:(p,v)∈theatre G P then ContinuousLinearMap.proj ⟨(p,v),h⟩ else 0
abbrev vibe (a:Axis):maskShelf G P→L[ℝ] G.Color:= LinearMap.toContinuousLinearMap {
    toFun v:= toLp 2 fun j=> chooseS G P 0 (.inl (a,j)) v
    map_add' x y:=by ext j; exact map_add _ x y
    map_smul' x y:=by ext j; exact map_smul (chooseS G P 0 _) x y }
def song (i:Edge Cover): maskShelf G P→L[ℝ] G.Color:= if h:staffs P.L (wrap P.L i.1,i.2) then 0 else
   LinearMap.toContinuousLinearMap {
    toFun v:= toLp 2 fun j=>chooseS G P (cellar P.L i.1) (.inr (⟨_,h⟩,j)) v
    map_add' x y:=by ext j; exact map_add _ x y
    map_smul' x y:=by ext j; exact map_smul (chooseS G P _ _) x y }
def hornU (v:maskShelf G P): CoverConfig G:=fun i=> G.lieExp (song G P i v)
lemma horn_unit : hornU G P 0=1:=by funext i; simp [hornU]
lemma hornDiff : Army (hornU G P) 0:=fun i=> G.exp_jet.contDiffAt.comp (f:=song G P i) _ (song G P i).contDiff.contDiffAt
end
variable {P:Patch}{K:KernelChoices}
-- comparison exact shelf. any t. skeleton
lemma rootHalf (r:Ratio c f)(y : Site c)(p:Cover): r.parent (wrap f p+r.embed y)=y+wrap c (cellar r.count p)∧ r.residue (wrap f p+r.embed y)=wrap r.count p:=by
    rw [add_comm (wrap f p)]; rw [moves_parent,r.residue_embed,r.embed_parent,moves_residue,r.residue_embed]; refine ⟨rfl,?_⟩; simp [Work.F08.arrives]
variable (h:Odd S.ratio.count.val)
abbrev nick (p:Site c): vertP S.ratio h G→L[ℝ] maskShelf G S.patch:= lookS (theatre G S.patch) p ∘L (paintV S.ratio h G).toContinuousLinearMap
lemma chairV (p:Site c)(v:vertP S.ratio h G)(a:Axis): G.lieExp (vibe G S.patch a (nick h p v))=represent v.1 (p,a):=by
   change _= G.lieExp (v.1 (p,coord a)) * 1; rw [mul_one]; apply congr_arg; ext i; let P:= S.patch; let j:Tile G P.L:= Sum.inl (a,i); change chooseS G P 0 j (nick h p v)= v.1 (p,coord a) i; rw [chooseS, dif_pos (by simp [theatre])]; change spool G c v.1 (p+wrap c 0,a,i)=_; rw [map_zero,add_zero]; rfl
lemma chairU (p:Site c)(v:vertP S.ratio h G) (i:Edge Cover)(hp:i.1∈playhouse S.patch): expandAt (S.ratio.embed p) (Virgin.fieldF (forest S.ratio h) v.2) i=hornU G S.patch (nick h p v) i:=by
    let X:= S.ratio; let y:= wrap f i.1+ X.embed p; have ⟨hh, hx⟩:=rootHalf X p i.1; let F:=forest X h; let j:Edge (Site f):=(y,i.2); change F.drape _ j= G.lieExp (song _ _ _ _); have he : j∈ F.trunks ↔ staffs S.patch.L (wrap S.patch.L i.1,i.2):=by rw [staff_trunk]; change staffs X.count (X.residue (wrap f i.1+ X.embed p),i.2) ↔_; rw [hx]; rfl
    unfold song; split
    next hi=> rw [show F.drape _ j=1 from F.on_tree _ ⟨_,he.mpr hi⟩]; exact G.mat_lieExp_zero.symm
    next hi=> let t:F.Free:=⟨j,mt he.mp hi⟩; rw [show F.drape _ j=G.lieExp (v.2 t) from F.off_tree _ t]; apply congr_arg; ext u
              let z:=cellar X.count i.1; let e : Slip G S.patch.L:=(⟨_,hi⟩,u); change v.2 t u=chooseS G S.patch z (.inr e) (nick h p v); rw [chooseS,dif_pos]; swap; · apply mem_product.mpr; exact ⟨mem_insert_of_mem (mem_image_of_mem _ hp),mem_univ _⟩ -- mem_insert_of_mem signature
              let D:= paintV X h G v; change v.2 t u=D (starJ (p+wrap c z,e)); have ht: squad X h G (t,u)=(p+wrap c z,e):= Prod.ext hh (Prod.ext (Subtype.ext (Prod.ext hx rfl)) rfl); erw [← ht]; exact ((petalV X h v (t,u)).trans (rangers_fee (forest S.ratio h) ..)).symm
end Script
end YM.OPE.Flume
