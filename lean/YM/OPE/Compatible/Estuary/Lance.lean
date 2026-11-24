import YM.OPE.Compatible.Estuary.Torque
/-!
# Gauge transfer tape stencils -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Work.F05 Votive Tree
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I:Type*}{r n m d h:ℕ}{G:Gauge}{c f L:Side} {S:StepData c f}
namespace Script
open Page Virgin Planned.PrimaryIntegral295.Carrier
abbrev Blend (G:Gauge):= Shade G⊕ G.ColorIndex
abbrev hoods (G:Gauge)(A:Cross L (TypeFace 0) (TypeFace 1)):Cross L G.ColorIndex (Shade G):= braidRow (fun i=>(i.1,vac,i.2)) (mus G) (forestWalk G A)
lemma hoods_at (A:Cross S.ratio.count (TypeFace 0) (TypeFace 1))(x:Bid.Dir G c)(i:Tab G.ColorIndex f): (installed S.ratio (hoods G A) *ᵥ spool G c x) i=((installed S.ratio A)*ᵥ parts G 1 x i.2) (i.1,vac):=by
    let j: Co f (PAC G 0):= (i.1,vac,i.2); have he(p:Tab (Shade G) c): installed S.ratio (hoods G A) i p= installed S.ratio (forestWalk G A) j (lent G c p):= rfl
    calc
       _= (installed S.ratio (forestWalk G A) *ᵥ flatten x) j:=by unfold Matrix.mulVec dotProduct; dsimp only; rw [← (lent G c).sum_comp (fun p=> installed S.ratio (forestWalk G A) j p*flatten x p)]; exact sum_congr rfl fun i _=>rfl
       _=_:=by rw [forestWalk_read]; exact congr_fun (component_mul ..) (i.1,vac)
lemma hoodFund {A:Cross L (TypeFace 0) (TypeFace 1)}(h:Whole A): Whole (hoods G A):=by
    obtain ⟨s,D,h,H⟩:=h; exact braidP _ _ _ ⟨s,max D 0,h,forestWalk_pay (strip_mono H le_rfl (le_max_left ..)) (le_max_right ..)⟩
lemma chromeRead (g:Ratio c f)(A:Lines g.count)(x:Bid.Dir G c)(i:Tab (Shade G) f): (installed g (chrome G.ColorIndex A) *ᵥ spool G c x) i= (installed g A*ᵥ parts G 1 x i.2.2) (i.1,coord i.2.1):=by
    let j:= lent G f i; let W:= forestWalk G A; let B:= installed g A; calc
       _=(installed g W*ᵥ flatten x) j:=by unfold Matrix.mulVec dotProduct; dsimp only; rw [← (lent G c).sum_comp (fun p=> installed g W j p*flatten x p)]; exact sum_congr rfl fun i _=>rfl
       _=_:=by unfold W;rw [forestWalk_read];exact congr_fun (component_mul B (flatten x) i.2.2) (i.1,coord i.2.1)
-- combined
abbrev kite (G:Gauge)(P:Patch)(A:Lines P.L):Cross P.L (Blend G) (Shade G):= fun i j=> i.2.elim (fun k=> chrome G.ColorIndex A (i.1,k) j) (fun k=> hoods G (straighter P A) (i.1,k) j)
lemma kite_ne (P:Patch)(A:Lines P.L)(h:Whole A): Whole (kite G P A):=by
    obtain ⟨s,b,hs,H⟩:= chrome_sum (W:=G.ColorIndex) h; obtain ⟨t,v,ht,Q⟩:= hoodFund (G:=G) ((bow_price P).prod h); refine ⟨min s t,max b v,lt_min hs ht,?_⟩; rintro ⟨i,j|j⟩ k
    · exact strip_mono H (min_le_left ..) (le_max_left ..) (i,j) k
    exact strip_mono Q (min_le_right ..) (le_max_right ..) (i,j) k
variable (S)
lemma kiteX (A:Lines S.ratio.count)(x:deck (Shade G) c)(i:Tab (Shade G) f): (installed S.ratio (kite G S.patch A)*ᵥ x) (starI i)=(installed S.ratio (chrome G.ColorIndex A) *ᵥ x) i:=rfl
lemma kiteY (A:Lines S.ratio.count)(h:Whole A)(x:Bid.Dir G c)(i:Tab G.ColorIndex f):
    (installed S.ratio (kite G S.patch A)*ᵥ spool G c x) (starJ i)= (straighten S (forest S.ratio S.patch.odd_side) (installed S.ratio A) *ᵥ parts G 1 x i.2) (i.1,vac):=by
      erw [← straighten_acts S A h, ← hoods_at (S:=S) (straighter S.patch A) x];rfl
-- M relation from C.row
lemma spun (C:Boxes G S.patch S.kernel)(x:Bid.Dir G c) (p:Tab (Shade G) f) :
    (installed S.ratio (drip G S.ratio.count)*ᵥ(C.main.acts c *ᵥ spool G c x)) p=(installed S.ratio (C.C.highCross C.g)*ᵥ flatten x) (lent G f p):=by
     let K:= into G S.patch.L; let R:= S.ratio; let P:= C.C.rowNet C.g; let q:=lent G f p; let t := spool G c x
     erw [Medal.highCross, Whole.from_coarse S.ratio (into_good ..) (C.C.row_p C.g), ← Matrix.mulVec_mulVec,splitMargin (v:=C.main.acts c *ᵥ t)]
     erw [Finset.sum_eq_zero (s:=univ) (f:=fun i:Tab (Shade G) c=> _ ) (fun i _=>by erw [dripThin,zero_mul]),zero_add]; change ∑ j, (installed S.ratio (into G S.ratio.count) q j)*_= _; apply Finset.sum_congr rfl; intro i _; apply congr_arg _ (adjust C.C C.g x i) -- parent
end Script
end YM.OPE.Flume
