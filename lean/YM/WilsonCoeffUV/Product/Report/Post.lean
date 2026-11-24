import YM.WilsonCoeffUV.Product.Report.Pre
/-!
# Post costs in stage currencies
-/
set_option autoImplicit false
set_option maxHeartbeats 550000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Patrol
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Supply Ticket Polestar Next.Foundations Real Shard Plan
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n:Side}{U V:Type*}{r h D l e j k a N M m b i q z u:ℕ} {G:Gauge}{F:Labels.Frame G h}{H:Hol G}{A A':Levels G}
variable {p0:Sheet G}{Q:Rolls p0}{Ω:Protection Q}{F':ℕ→ℕ} {Y:Delays Ω}{o:Bar Y}{b':Supply.Wait o}{Ñ:ChartRatio G}
local notation "🜊" => Credit.leanC
-- stages coexist and any lists before capture at R
structure AwardsM (H:Hol G)(R:Master H)(F':ℕ→ℕ)(Q:Rolls p0)(Ñ: ChartRatio G){Ω:Protection Q}(Y: Delays Ω) : Prop where
    ink:floors G p0.kernel F'≤ p0.floorL
    rise:(fun i=>sharp H R p0.kernel Ñ i (F' i) (F' i))≤ p0.floorL
    carve:(fun i=>climbP H R Ñ p0.kernel i (F' i)) ≤ p0.floorL
    seam:(fun i=>preMark Ñ p0.kernel i (F' i)) ≤ p0.floorL
    fg:voucher Q F' Ñ ≤ Y.betaEntry
    hg:(fun j=>tickZ H R p0.kernel Ñ (Q.L j) (F' j) (F' j) j)≤ Y.betaEntry
    rg:(fun j=> utopia H R p0.kernel (F' j) (F' j) j)≤ Y.betaEntry
    page:(fun j=> guardRail H R Ñ p0.kernel j (F' j) (Q.L j)) ≤ Y.betaEntry
    tMark:(fun j=> postMark Ñ p0.kernel j (F' j) (Q.L j)) ≤ Y.betaEntry
variable {R:Master H}
lemma qualifiedBright (g:G.Simple)(hA:LocalRatio Ñ) {yD:ℕ→ℝ}(a:BasicBill Y A yD m)(f:AwardsM H R F' Q Ñ Y)(p:h<D)(v:Rails h k u e)(d':ℕ)(w:∀ j≥ m, let i:=A.clock.J (j+1); 5 ≤ i ∧ h+1≤ i-2 ∧ e+1≤ F' i ∧ D≤ F' i ∧ k+d'≤ F' i ∧ u≤ F' i) : ∃ W:ChorusLine H (R.T h) p e Credit.leanC Credit.leanC Credit.leanC,∃ Z:Torch H (R.T h) p v Credit.leanC Credit.leanC Credit.leanC,W.arch.V.draws=A∧ W.arch.V.paid=Ñ∧ W.arch.V.y=yD∧W.arch.V.anchor=m∧Weston W.arch Credit.leanC∧ (∀ i (v:W.arch.V.anchor≤ i), ∃ p:5≤A.clock.J (i+1),(W.arch.angle i v).lamp.exitS=crestM A i p) ∧ Z.L=W.arch ∧∀ k'≤ k,∀ d≤ d', Dormitory W.arch.V k' u Credit.leanC ∧ SpringD W.arch.V k' u (k'+d) Credit.leanC:=by
    obtain ⟨S,hS,vS,x,y,z,t⟩:= figures_cover H R g hA f.ink f.rise a f.fg f.hg f.rg p (e:=e) (m:=m) (fun j p=> let V:=w j p; ⟨V.1,V.2.1,V.2.2.1,V.2.2.2.1⟩)
    have hy i:A.S.block i=Q.L (A.clock.J (i+1)):=by rw [← A.fits.sameFactor,a.lengths]
    have hh j (v':S.arch.V.anchor≤j): CompassP H (R.T h) p v (S.arch.angle j v') (S.arch.V.cash Credit.leanC j):=by
       let i:=A.clock.J (j+1); have ht:=w j (y ▸ v'); obtain ⟨a',c,d,q,z⟩:= t j v'
       have hp : climbP H R Ñ p0.kernel i (F' i) ≤ (A.S.block j).val:= by rw [hy]; exact (f.carve i).trans (Q.large i).need
       have hQ: guardRail H R Ñ p0.kernel i (F' i) (A.S.block j) ≤ exp (exp (yD j-1)):= by rw [hy]; exact (f.page i).trans (a.pays j (y ▸ v'))
       rw [z,cash,x,Credit.lean_cost]; exact PackingCash H R Ñ p0.kernel _ (F' i) A j a.kernel rfl c d q a' hp p v ht.2.2.2.1 ((Nat.le_add_right k _).trans ht.2.2.2.2.1) ht.2.2.2.2.2 (e.le_succ.trans ht.2.2.1) hQ
    refine ⟨S,⟨S.arch,hh⟩,hS,vS,x,y,z,fun i u=>?lamp,rfl,fun k' p d l=>?_⟩
    case lamp => obtain ⟨i,v,q,b,h⟩:= t i u; rw [h]; exact ⟨v,rfl⟩
    have h j (v':S.arch.V.anchor ≤ j): let I:=(S.arch.V.mint j v').gear; DormP I k' e u (S.arch.V.cash Credit.leanC j) ∧ poreF G e k' u (k'+d) I ≤ S.arch.V.cash Credit.leanC j:=by
       obtain ⟨ap,v,q0,s,h⟩:= t j v'; let i:=A.clock.J (j+1)
       have ht : (S.arch.V.mint j v').gear=(quest A j Ñ v q0).gear := by rw [← (S.arch.effort j v').1,h]; rfl
       have hp:= w j (y ▸ v'); rw [ht]; dsimp only; rw [cash,x,Credit.lean_cost]
       have hx: preMark Ñ p0.kernel i (F' i)≤ (A.S.block j).val:=by rw [hy]; exact (f.seam _).trans (Q.large i).need
       have hP: postMark Ñ p0.kernel i (F' i) (A.S.block j) ≤ exp (exp (yD j-1)):=by rw [hy]; exact (f.tMark i).trans (a.pays j (y ▸ v'))
       exact handledCash Ñ p0.kernel i (F' i) k' u (k'+d) e A j a.kernel rfl v q0 (e.le_succ.trans hp.2.2.1) ((p.trans (Nat.le_add_right ..)).trans hp.2.2.2.2.1) hp.2.2.2.2.2 ((Nat.add_le_add p l).trans hp.2.2.2.2.1) hx hP
    exact ⟨fun j v'=>(h j v').1,⟨fun j v'=>(h j v').2⟩⟩
lemma qualifiedCash (g:G.Simple)(hA:LocalRatio Ñ) {yD:ℕ→ℝ}(a:BasicBill Y A yD m)(f:AwardsM H R F' Q Ñ Y)(p:h<D)(v:Rails h k u e)(d':ℕ)(w:∀ j≥ m, let i:=A.clock.J (j+1); 5 ≤ i ∧ h+1≤ i-2 ∧ e+1≤ F' i ∧ D≤ F' i ∧ k+d'≤ F' i ∧ u≤ F' i) : ∃ W:ChorusLine H (R.T h) p e Credit.leanC Credit.leanC Credit.leanC,∃ Z:Torch H (R.T h) p v Credit.leanC Credit.leanC Credit.leanC,W.arch.V.draws=A∧ W.arch.V.paid=Ñ∧ W.arch.V.y=yD∧W.arch.V.anchor=m∧Weston W.arch Credit.leanC∧ Z.L=W.arch ∧∀ k'≤ k,∀ d≤ d', Dormitory W.arch.V k' u Credit.leanC ∧ SpringD W.arch.V k' u (k'+d) Credit.leanC:=by
    obtain ⟨W,Z,x,a,b,c,d,_t,t,v⟩:= qualifiedBright g hA a f p v d' w; exact ⟨W,Z,x,a,b,c,d,t,v⟩
lemma qualified (g:G.Simple)(hA:LocalRatio Ñ) (a:Paid b' A)(f:AwardsM H R F' Q Ñ Y)(p:h<D)(v:Rails h k u e)(d':ℕ)(w:∀ j≥ m, let i:=A.clock.J (j+1); 5 ≤ i ∧ h+1≤ i-2 ∧ e+1≤ F' i ∧ D≤ F' i ∧ k+d'≤ F' i ∧ u≤ F' i) : ∃ W:ChorusLine H (R.T h) p e Credit.leanC Credit.leanC Credit.leanC,∃ Z:Torch H (R.T h) p v Credit.leanC Credit.leanC Credit.leanC,W.arch.V.draws=A∧ W.arch.V.paid=Ñ∧ W.arch.V.y=zz A∧W.arch.V.anchor=m∧Weston W.arch Credit.leanC∧ Z.L=W.arch ∧∀ k'≤ k,∀ d≤ d', Dormitory W.arch.V k' u Credit.leanC ∧ SpringD W.arch.V k' u (k'+d) Credit.leanC:=by
    exact qualifiedCash g hA (booked g a f.fg m) f p v d' w
lemma continuity (g:G.Simple)(hA:LocalRatio Ñ) (a:Paid b' A)(f:AwardsM H R F' Q Ñ Y)(l:Tendsto F' atTop atTop)(p:h<D)(v: Rails h k u e)(d:ℕ): ∀ᶠ m in atTop,∃ W:ChorusLine H (R.T h) p e Credit.leanC Credit.leanC Credit.leanC,∃ Z:Torch H (R.T h) p v Credit.leanC Credit.leanC Credit.leanC,W.arch.V.draws=A∧ W.arch.V.paid=Ñ∧ W.arch.V.y=zz A∧W.arch.V.anchor=m∧Weston W.arch Credit.leanC∧ Z.L=W.arch ∧∀ k'≤ k,∀ d'≤ d, Dormitory W.arch.V k' u Credit.leanC ∧ SpringD W.arch.V k' u (k'+d') Credit.leanC:=by
    have he: Tendsto (fun i=>A.clock.J (i+1)) atTop atTop:= A.fits.deep.comp (tendsto_add_atTop_nat 1)
    obtain ⟨t,h⟩:= eventually_atTop.mp ((he.eventually_ge_atTop (h+5)).and ((l.comp he).eventually_ge_atTop (e+1+D+k+d+u))); apply (eventually_ge_atTop t).mono; intro i g'
    exact qualified g hA a f p v d (m:=i) fun j hj=>by obtain ⟨x,h⟩:= h j (g'.trans hj); simp only [Function.comp_apply] at *; omega

def BayV (R:Master H)(h D:ℕ)(x:h<D): SealR G:=⟨h,R.F h,D,R.T h,x⟩
lemma ambassadors (g:G.Simple)(hA:LocalRatio Ñ)(a:Paid b' A)(f:AwardsM H R F' Q Ñ Y)(l:Tendsto F' atTop atTop)(e:ℕ)(P:Fin (z+1)→SealR G)(p:∀ i,BayV R (P i).h (P i).D (P i).path=P i) : ∀ᶠ i:ℕ in atTop,∀ S:Realm G (e+1) Credit.leanC,S.draws=A → S.paid=Ñ → S.y=zz A→ S.anchor=i → FramesR H S Credit.leanC Credit.leanC P Credit.leanC:=by
    have hx j:∀ᶠ m:ℕ in atTop,∀ S:Realm G (e+1) Credit.leanC,S.draws=A → S.paid=Ñ → S.y=zz A→ S.anchor=m → Nonempty (AheadT H S Credit.leanC Credit.leanC (P j) Credit.leanC):=by
       let T:= P j; obtain ⟨d,t,v⟩:= rail_noun T.h T.h e le_rfl 0; filter_upwards [continuity g hA a f l T.path v 0] with i hi; intro S p' u s k; obtain ⟨W,Z,hW,h,g,y,z,-⟩:=hi
       rw [← p]; exact ⟨⟨⟨W,hW.trans p'.symm,h.trans u.symm,g.trans s.symm,y.trans k.symm⟩,z⟩⟩
    filter_upwards [(eventually_all.mpr hx)] with i h; exact fun S p u y z i=> h i S p u y z

theorem PortsTogether (g:G.Simple)(hA:LocalRatio Ñ)(a:Paid b' A)(f:AwardsM H R F' Q Ñ Y)(l:Tendsto F' atTop atTop)(p:h<D)(v:Rails h k u e) (P:Fin (z+1)→SealR G)(q:∀ i,BayV R (P i).h (P i).D (P i).path=P i) (w: capP P≤k): ∀ᶠ m in atTop,∃ W:ChorusLine H (R.T h) p e Credit.leanC Credit.leanC Credit.leanC,∃ Z:Torch H (R.T h) p v Credit.leanC Credit.leanC Credit.leanC,W.arch.V.draws=A∧ W.arch.V.paid=Ñ∧ W.arch.V.y=zz A∧W.arch.V.anchor=m∧Weston W.arch Credit.leanC∧ W.arch=Z.L∧ Dormitory Z.L.V (capP P) u Credit.leanC ∧ SpringD Z.L.V (capP P) u (capP P+2) Credit.leanC ∧ FramesR H Z.L.V Credit.leanC Credit.leanC P Credit.leanC ∧ HorizonP H Z.L.V Credit.leanC Credit.leanC P:=by
    filter_upwards [continuity g hA a f l p v 2,ambassadors g hA a f l e P q] with m h ht; obtain ⟨W,Z,hW,h,x,y,z,o,s⟩:=h; obtain ⟨d,D'⟩:= s _ w 2 le_rfl; have hp:=ht W.arch.V hW h x y; refine ⟨W,Z,hW,h,x,y,z,o.symm,?_⟩; rw [o]; exact ⟨d,D',hp,fun j=> (hp j).map fun x=>x.p⟩
end YM.WilsonCoeffUV.Mer.Patrol
