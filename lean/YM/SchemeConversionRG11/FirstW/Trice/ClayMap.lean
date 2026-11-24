import YM.SchemeConversionRG11.FirstW.Trice.Clay
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW.Branch
open Function Filter Set MeasureTheory Metric Lattice Pert Align Position Topology Maxwell Pert.Triangle Tensor Analysis Deck SchemeConversionRG11.FirstMS Complex MvPolynomial Next.Rank.Normal
open SchemeConversionRG11.FirstMS.Triad hiding slide surface bar
open scoped Topology ContDiff BigOperators Classical Matrix
variable {T:Itinerary}{G:Gauge}{p:Nodes}{n:Side}{r:ℕ}
abbrev tallG (p:Points r) := (Wick.moment G p).compLinearMap (fun _:Fin r=> (reduceEq (G:=G)).toLinearMap ∘ₗ ((rename (R:=ℂ) (fun x:Who G 6=> x.val)).toLinearMap))
lemma tall_eq (o: Full.Grid n r)(t:ℝ): ∃ L: MultilinearMap ℂ (fun _:Fin r=>Deck.Part G 6) ℂ,∀ p,L p=ZeroR o t p:= by
 let W: Deck.Part G 6→ₗ[ℂ] Labels.Pol G:= (rename Subtype.val).toLinearMap; let M:= (PowerSeries.coeff (R:=ℂ) 0).compMultilinearMap ((Warp.recipe 6 t o).compLinearMap fun _=> W)
 exact ⟨M,fun p=>by simp only [M,W, LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply, PowerSeries.coeff_zero_eq_constantCoeff];rfl⟩
def amount (x:Points r)(v:Players G r 6):=tallG x v
lemma fortune {o:∀ i,Full.Grid (T.period i) r}{v:Points r}(d:Diorama T o v) (P:Players G r 6): Tendsto (fun i=> ZeroR (o i) (T.gap i) P) atTop (𝓝 (amount v P)) := Warp.poly_limit 6 T _ _ d.ht d.hs d.hdiv (fun i=>uncap_height (P i))
-- abstract Qu library Curried
abbrev Trio (G:Gauge):= Deck.Part G 6
abbrev StampC (G:Gauge):= Trio G→ₗ[ℂ] Trio G →ₗ[ℂ] Trio G →ₗ[ℂ] ℂ
lemma stamps (f:MultilinearMap ℂ (fun _:P=>Trio G) ℂ): ∃ L:StampC G,∀ a b c,L a b c=f (![a,b,c]) := by
 let g(a b c:Trio G):= f (![a,b,c]); let Z(a b:Trio G):=f.toLinearMap (![a,b,0]) 2
 have h (a b c:Trio G): Z a b c=g a b c:=by unfold g Z; rw [MultilinearMap.toLinearMap_apply]; congr; funext i; fin_cases i <;> rfl -- potential update classical
 have h0(a b c:Trio G): f.toLinearMap (![0,b,c]) 0 a=g a b c:= by unfold g; rw [MultilinearMap.toLinearMap_apply]; congr; funext i; fin_cases i <;> rfl
 have hv(a b c:Trio G): f.toLinearMap (![a,0,c]) 1 b=g a b c:= by unfold g; rw [MultilinearMap.toLinearMap_apply]; congr; funext i; fin_cases i <;> rfl -- before placeholders
 let L(a:Trio G): Trio G→ₗ[ℂ] Trio G →ₗ[ℂ] ℂ:={ toFun:=Z a,
                                                   map_add':=fun b c=>LinearMap.ext (fun d=>by simp only [LinearMap.add_apply,h,←hv]; exact map_add ..),
                                                   map_smul':=fun r b=>LinearMap.ext (fun c=>by simp only [LinearMap.smul_apply,h,←hv]; exact map_smul ..) }
 refine ⟨{toFun:=L, map_add' :=fun a b=>LinearMap.ext fun c=>LinearMap.ext fun d=> ?_, map_smul' :=fun k a=> LinearMap.ext fun c=>LinearMap.ext fun d=>?_},fun a b c=>h a b c⟩
 all_goals simp only [L,LinearMap.coe_mk,AddHom.coe_mk, LinearMap.add_apply, LinearMap.smul_apply, h,RingHom.id_apply];first|simp_rw [←h0]; rw [map_add]|simp_rw [←h0];rw [map_smul]
def copyK (G:Gauge)(p:P)(X:Trio G) := rename (Prod.mk p) (reduceEq (uncap X))
lemma glyphS (b:Bend G 3): copyK G b.j (Glyph b.B b.b)=dynasty b:=by unfold copyK dynasty; rw [proved,Triangle.reduced_fan]
lemma copy_mul (p:P)(x y: Trio G): copyK G p (x*y)=copyK G p x*copyK G p y:=by simp only [copyK,uncap,map_mul]
@[simp] lemma copy_one (p:P): copyK G p 1=1:=by simp [copyK,uncap]
variable (hp:p∈conf 3)
lemma reads_three (a b c: Trio G): amount p (![a,b,c])= blend (frameX hp) 0 (copyK G 0 a*copyK G 1 b*copyK G 2 c) := by
 change Wick.moment G p _=_; rw [Wick_reads (n:=3) hp,Fin.prod_univ_succ,Fin.prod_univ_succ,Fin.prod_univ_succ];simp only [Fin.prod_univ_zero,mul_one, mul_assoc];rfl
include hp
lemma ladder_c (b c: Badge G)(i j:P)(e:i≠j): lux p ⟨b,i,true⟩ ⟨c,j,false⟩= if b.2=c.2 then (mixed b.1 c.1 (p i-p j):ℂ) else 0:= by unfold lux; simp only [e,↓reduceIte,prob]; rw [mixed_probe b c (sub_ne_zero.mpr (hp.ne e))];split <;> simp
lemma lux_n (b c:Badge G)(i j:P): lux p ⟨b,i,false⟩ ⟨c,j,false⟩=0:=by
 unfold lux; by_cases e:i=j
 · simp [e]; -- etc
 rw [if_neg (show _ from e)]; change ↑(legKernel (Triangle.probe _ _ _) (Triangle.probe _ _ _) _)=(0:ℂ); rw [fan_kernel _ _ _ _ _ (sub_ne_zero.mpr (hp.ne e)),ofReal_zero]
end YM.RG11.FirstW.Branch
