import YM.Integration.WilsonIndependentEvenPassport

/-! A higher single-column moment and every lower pair moment are earned on one chosen unmarked gear. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 650000
noncomputable section
namespace YM.Integration.WilsonIndependentTwoMomentPassport
open WilsonCoeffUV
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Supply Ticket Polestar Next.Foundations Real Shard Plan
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n:Side}{U V:Type*}{r h D l e j k a N M m b i q z u:ℕ} {G:Gauge}{F:Labels.Frame G h}{H:Hol G}{A A':Levels G}
variable {p0:Sheet G}{Q:Rolls p0}{Ω:Protection Q}{F':ℕ→ℕ} {Y:Delays Ω}{o:Bar Y}{b':Supply.Wait o}{Ñ:ChartRatio G}
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.AuxPlates
variable {R:Master H}

theorem original (g:G.Simple)(hA:LocalRatio Ñ) {yD:ℕ→ℝ}(a:BasicBill Y A yD m)(f:AwardsM H R F' Q Ñ Y)(p:h<D)(v:Rails h k u e)(d':ℕ)(w:∀ j≥ m, let i:=A.clock.J (j+1); 5 ≤ i ∧ h+1≤ i-2 ∧ e+1≤ F' i ∧ D≤ F' i ∧ k+d'≤ F' i ∧ u≤ F' i) : ∃ W:ChorusLine H (R.T h) p e Credit.leanC Credit.leanC Credit.leanC,∃ Z:Torch H (R.T h) p v Credit.leanC Credit.leanC Credit.leanC,W.arch.V.draws=A∧ W.arch.V.paid=Ñ∧ W.arch.V.y=yD∧W.arch.V.anchor=m∧Weston W.arch Credit.leanC∧ (∀ i (v:W.arch.V.anchor≤ i), ∃ p:5≤A.clock.J (i+1),(W.arch.angle i v).lamp.exitS=crestM A i p) ∧ Z.L=W.arch ∧∀ u'≤u,∀ k'≤ k,∀ d≤ d', Dormitory W.arch.V k' u' Credit.leanC ∧ SpringD W.arch.V k' u' (k'+d) Credit.leanC:=by
    obtain ⟨S,hS,vS,x,y,z,t⟩:= figures_cover H R g hA f.ink f.rise a f.fg f.hg f.rg p (e:=e) (m:=m) (fun j p=> let V:=w j p; ⟨V.1,V.2.1,V.2.2.1,V.2.2.2.1⟩)
    have hy i:A.S.block i=Q.L (A.clock.J (i+1)):=by rw [← A.fits.sameFactor,a.lengths]
    have hh j (v':S.arch.V.anchor≤j): CompassP H (R.T h) p v (S.arch.angle j v') (S.arch.V.cash Credit.leanC j):=by
       let i:=A.clock.J (j+1); have ht:=w j (y ▸ v'); obtain ⟨a',c,d,q,z⟩:= t j v'
       have hp : climbP H R Ñ p0.kernel i (F' i) ≤ (A.S.block j).val:= by rw [hy]; exact (f.carve i).trans (Q.large i).need
       have hQ: guardRail H R Ñ p0.kernel i (F' i) (A.S.block j) ≤ exp (exp (yD j-1)):= by rw [hy]; exact (f.page i).trans (a.pays j (y ▸ v'))
       rw [z,cash,x,Credit.lean_cost]; exact PackingCash H R Ñ p0.kernel _ (F' i) A j a.kernel rfl c d q a' hp p v ht.2.2.2.1 ((Nat.le_add_right k _).trans ht.2.2.2.2.1) ht.2.2.2.2.2 (e.le_succ.trans ht.2.2.1) hQ
    refine ⟨S,⟨S.arch,hh⟩,hS,vS,x,y,z,fun i u=>?lamp,rfl,fun u' hu k' p d l=>?_⟩
    case lamp => obtain ⟨i,v,q,b,h⟩:= t i u; rw [h]; exact ⟨v,rfl⟩
    have h j (v':S.arch.V.anchor ≤ j): let I:=(S.arch.V.mint j v').gear; DormP I k' e u' (S.arch.V.cash Credit.leanC j) ∧ poreF G e k' u' (k'+d) I ≤ S.arch.V.cash Credit.leanC j:=by
       obtain ⟨ap,v,q0,s,h⟩:= t j v'; let i:=A.clock.J (j+1)
       have ht : (S.arch.V.mint j v').gear=(quest A j Ñ v q0).gear := by rw [← (S.arch.effort j v').1,h]; rfl
       have hp:= w j (y ▸ v'); rw [ht]; dsimp only; rw [cash,x,Credit.lean_cost]
       have hx: preMark Ñ p0.kernel i (F' i)≤ (A.S.block j).val:=by rw [hy]; exact (f.seam _).trans (Q.large i).need
       have hP: postMark Ñ p0.kernel i (F' i) (A.S.block j) ≤ exp (exp (yD j-1)):=by rw [hy]; exact (f.tMark i).trans (a.pays j (y ▸ v'))
       exact handledCash Ñ p0.kernel i (F' i) k' u' (k'+d) e A j a.kernel rfl v q0 (e.le_succ.trans hp.2.2.1) ((p.trans (Nat.le_add_right ..)).trans hp.2.2.2.2.1) (hu.trans hp.2.2.2.2.2) ((Nat.add_le_add p l).trans hp.2.2.2.2.1) hx hP
    exact ⟨fun j v'=>(h j v').1,⟨fun j v'=>(h j v').2⟩⟩
end YM.Integration.WilsonIndependentTwoMomentPassport

namespace YM.Integration.WilsonIndependentTwoMomentPassport
open WilsonCoeffUV
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Soil Power
open Embroider Precision Exterior Source Source.Drops Labels WardBin Cosmos Bulb Realm Fountain PathCost Supply Ticket Shard Plan Mer Patrol Polestar
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{h k u e n D j s a:ℕ}{H:Hol G} {R:Master H} {p:Sheet G} {Q: Rolls p}{Ω:Protection Q}{Y:Delays Ω}{F':ℕ→ℕ}{Ñ:ChartRatio G}{y:ℕ→ℝ} {A:Levels G}

open WilsonCoeffUV.AuxPlates

def Shared (R:Master H)(A:Levels G)(Ñ:ChartRatio G)(y:ℕ →ℝ)(e s kD kF:ℕ): Prop:= ∀ (h D k u d:ℕ)(p:h<D)(v:Rails h k u e), h≤ kD → D≤kF → k+d≤kF → u≤ kF →∃ W:ChorusLine H (R.T h) p e Credit.leanC Credit.leanC Credit.leanC,∃ Z:Torch H (R.T h) p v Credit.leanC Credit.leanC Credit.leanC,W.arch.V.draws=A∧ W.arch.V.paid=Ñ∧ W.arch.V.y=y∧ W.arch.V.anchor=s∧ Weston W.arch Credit.leanC∧ (∀ i (v:W.arch.V.anchor≤ i), ∃ p:5≤A.clock.J (i+1),(W.arch.angle i v).lamp.exitS=crestM A i p) ∧ Z.L=W.arch ∧∀ u'≤u,∀ k'≤ k,∀ d'≤ d, Dormitory W.arch.V k' u' Credit.leanC ∧ SpringD W.arch.V k' u' (k'+d') Credit.leanC
private theorem equipped (g:G.Simple)(hA:LocalRatio Ñ)(a:BasicBill Y A y s)(f:AwardsM H R F' Q Ñ Y) (h':∀ j≥ s, let v:=A.clock.J (j+1);5≤ v ∧ h+1 ≤ v-2 ∧ max k (e+1) ≤ F' v) : Shared R A Ñ y e s h k:=by
    intro i d m u w p v h k D u; apply original g hA a f p v; intro j z; obtain ⟨x,t,e⟩:= h' j z; omega
variable {K:KernelChoices}
theorem funded (g:G.Simple) (R: Master H)(Ñ:ChartRatio G)(hA:LocalRatio Ñ)(K:KernelChoices)(hk:∀ P:Patch,P.Branches K G) (e h k i:ℕ)(q:h+3≤ i)(v:5≤ i) : ∃ f:ℕ, ∀ L L':Side,f ≤ L.val → f≤ L'.val → Odd L.val → Odd L'.val → L.val ≤ L'.val →∃ C:ℝ,1≤C∧ ∀ n c:ℕ,c≤n→ ∃ A: Levels G, ∃ s:ℕ,A.clock.kernel=K ∧ A.clock.factor i=L ∧ A.clock.factor (i+1)=L' ∧ Walk A i c s n ∧ Shared R A Ñ (extendedY C A.S (s+n)) e s h k:=by
    obtain ⟨t⟩:= cap_st
    let X:=fun _ :ℕ=>max k (e+1); let p:Sheet G:= ⟨K,hk,fun _=>t,i,by omega,monotone_const,monotone_const,monotone_const,horiz H R Ñ X K⟩
    obtain ⟨f,F⟩:= any_two p g; refine ⟨f,fun L L' h p' v1 v2 t=>?_⟩; obtain ⟨W,hP,hQ⟩:= F L L' h p' v1 v2 t
    obtain ⟨Ω,ho⟩:= Protection.exists_margin W (fun _=>1) (fun _=>zero_lt_one); let Y:Delays Ω:= ⟨aperture H R Ñ X W,0,0,0⟩; obtain ⟨o,_⟩:= Bar.exists_above Y 1
    obtain ⟨C,hC,h⟩:= finite_plates g o; refine ⟨C,hC,fun n c p'=>?_⟩; obtain ⟨A,start,B,V,t,a⟩:= h n c p'
    have he:p.first=i:=rfl
    have hR: A.clock.factor i=L:= by rw [t.lengths,←he,hP]
    have hS:A.clock.factor (i+1)=L':=by rw [t.lengths,←he,hQ]
    refine ⟨A,start,a.kernel,hR,hS,V,equipped g hA a (reported H R (F':=X) (show _=_ from rfl).le (show _ ≤ Y.betaEntry from le_rfl)) (fun j hj=>?_)⟩; have hz:A.clock.J 0=i:=t.firstZero; have hg:= A.fits.mono (show 0≤j+1 by omega); exact ⟨by omega,by omega,le_rfl⟩

-- Turns full inputs. explicit enrollment no waiting for arbitrary constructor.

theorem admitted (maxH maxF:ℕ)(share:Shared R A Ñ y e s maxH maxF) : Ally R A Ñ y e s maxH maxF :=by
  intro h D k u d p rails hh hd hk hu
  obtain ⟨W,Z,a,b,c,v,w,t,l,fees⟩:=share h D k u d p rails hh hd hk hu
  exact ⟨W,Z,a,b,c,v,w,t,l,fees u le_rfl⟩

end YM.Integration.WilsonIndependentTwoMomentPassport
