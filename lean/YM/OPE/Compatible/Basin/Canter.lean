import YM.OPE.Compatible.Basin.Tulip
/-!
# Constructor and fork. Pilot. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Tree Exterior Stationary Woody
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J Q E:Type*} {G:Gauge}{n m l c f:Side}{S:StepData c f} {g:Ratio c f} {r:ℕ}
namespace Script
open Page Virgin Work.F05
def mus (G:Gauge): Shade G≃ PAC G 1:= Equiv.prodCongr axisEquiv (Equiv.refl _)
abbrev lent (G:Gauge)(n:Side): Tab (Shade G) n≃ Co n (PAC G 1):= laceC (mus G)
lemma altPaint (v:Bid.Dir G c): flatten v ∘ lent G c= spool G c v:=rfl
-- pull cross operations
abbrev topInk (B:Cross l (PAC G 1) I):Cross l (Shade G) I:= braidRow (lent G l) id B
lemma topInk_cash {P:Cross m (PAC G 1) I}(h: Whole P):Whole (topInk P):=braidP _ _ _ h
lemma topIncome (r:Ratio c f)(B:Cross r.count (PAC G 1) I): installed r (topInk B)=(installed r B).submatrix (lent G f) id := by
    ext i j; rfl
abbrev flue (G:Gauge)(l:Side): Cross l (Shade G) (Slip G l):=topInk (Woody.into G l)
lemma flue_basis {r:Ratio c f}(h:Odd r.count.val) (i:Active G (forest r h))(j:Tab (Shade G) f): installed r (flue G r.count) j (squad r h G i)= insertion (plant (forest r h)) (lent G f j) i:=by
     unfold flue; rw [topIncome,into_trunks]; rfl
def drip (G:Gauge)(l:Side): Cross l (Shade G) (Tile G l):= fun i j=> j.elim (fun _=>0) (fun j=> flue G l i j)
lemma drip_cash (G:Gauge)(l:Side):Whole (drip G l):=by
    refine ⟨1,1,one_pos,?_⟩; intro i j; rcases j with j|j
    · change Width 1 1 0; simp [Width,SumBudget]
    exact into_paid G l 1 _ _
lemma dripRead (r:Ratio c f)(v: Tab (Shade G) f)(i: Tab (Slip G r.count) c):installed r (drip G r.count) v (starJ i) = installed r (flue G r.count) v i:= by rfl
lemma dripThin (r:Ratio c f)(v: Tab (Shade G) f)(i:Tab (Shade G) c):installed r (drip G r.count) v (starI i)=0:=by
     rw [installed]; let p:= splitCo r (Shade G) v; change (∑' z:Cover, if i.1=p.1+ wrap c z then (0:ℝ) else 0)=0; simp
lemma paintDrip (D:StepData c f)(h:Odd D.ratio.count.val)(V:Bid.Dir G c × AxisChart G (forest D.ratio h)) : (installed D.ratio (drip G D.ratio.count))*ᵥ(paintV D.ratio h G V)= spool G f (arm G f 1 (Stationary.pad (forest D.ratio h) V.2)) :=by -- arm/pad gap StepData? yes F type implicit {S}
    ext1 i; rw [splitMargin]; let F := forest D.ratio h; let S := squad D.ratio h G; simp_rw [dripThin,zero_mul,sum_const_zero,zero_add]; rw [← S.sum_comp]; change (∑ a:Active G F,_)=_; unfold S; simp_rw [dripRead, flue_basis h]; -- change sum trivial, use chart_flow but S unknown. can point check against trees
    by_cases he:(i.1,i.2.1)∈ F.trunks
    · have hp (v:Active G F) : plant F v≠ lent G f i:= by
         intro d; apply v.1.property; rw [show v.1.val=(i.1,i.2.1) from Prod.ext (Prod.mk.inj d).1 (axisEquiv.injective (Prod.mk.inj (Prod.mk.inj d).2).1)]; exact he
      change (∑ j, (if plant F j=lent G f i then 1 else 0)*_ )=edgeColor (Stationary.pad F _) (i.1,i.2.1) i.2.2; simp_rw [if_neg (hp _),zero_mul,sum_const_zero]; rw [show edgeColor _ _= (0:G.Color) from Stationary.pad_trunk F V.2 ⟨_,he⟩]; rfl
    let T : Active G F:= (⟨_, he⟩,i.2.2)
    have hp (j: Active G F): plant F j =lent G f i ↔ j=T:=by change plant F j=plant F T ↔ j=T; exact (plant_inj F).eq_iff
    change (∑ j,(if plant F j=lent G f i then 1 else 0)*_)=edgeColor (Stationary.pad F _) T.1 T.2; simp_rw [hp,ite_mul,one_mul,zero_mul, Finset.sum_ite_eq',Finset.mem_univ,if_true]; rw [Stationary.pad_free]; exact (petalV D.ratio h V T).trans (rangers_fee F ..)
end Script
end YM.OPE.Flume
