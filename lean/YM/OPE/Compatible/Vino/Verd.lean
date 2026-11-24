import YM.OPE.Compatible.Vino.Huts
/-!
# T0 equality via probes. Finite H not needed
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Silt.Float
open Cascade Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Paver Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp
variable {n c f:Side}{I J:Type}{G:Gauge}{r i j d m l:ℕ} {K:KernelChoices}
variable (P:Flight i j) (h:4 ≤ j)

include h in
lemma fluxFee (v:stave m r (Shade G)):∃ u:ℝ, soot m (opal G.ColorIndex P K.penalty (seed m _ _ v)) u:=by
     obtain ⟨a,B,ha,H⟩:= chrome_sum (W:=G.ColorIndex) (stored P _ K.penalty_pos h); exact ⟨_,counterflow H ha _ _ (humor v)⟩ -- implications
noncomputable def pipeQ (P:Flight i j)(h:4 ≤ j)(K:KernelChoices)(G:Gauge)(r m:ℕ)(v:stave m r (Shade G)): stave m r (Shade G):= Silt.Float.plant m (opal G.ColorIndex P K.penalty (seed m _ _ v)) _ ((fluxFee (K:=K) P h (m:=m) v).choose_spec)
noncomputable def wagon (P:Flight i j)(h:4 ≤ j)(K:KernelChoices)(G:Gauge)(d m:ℕ)(p:Seat d m (Shade G)): Seat d m (Shade G):= fun u=> pipeQ P h K G u.val m (p u)
lemma stool (K:KernelChoices)(p:Seat d m (Shade G)) (r:ℕ): lilies m d (Shade G) (wagon P h K G d m p) r= opal G.ColorIndex P K.penalty (lilies m d _ p r):=by
     by_cases hr:r≤d
     · rw [soup,soup,moduleAt,dif_pos hr]; let f:Fin (d+1):=⟨r,by omega⟩; let s:=wagon P h K G d m p f; change seed m _ _ s= _; unfold s wagon pipeQ; rw [botany]; rfl
     rw [(sproutV m _ p).1 _ (by omega),(sproutV m _ _).1 r (by omega)]; ext1 i; simp [opal,countermove]
lemma bedW (C:KernelChoices)(p:Seat d m (Shade G)) (hp:p∈bed G d m) (hx:P.patch.Branches C G): wagon P h C G d m p∈bed G d m:=fun i=> show _ from by
     rw [stool]; exact (pipeX C G P hx h (⟨lilies m d _ p i,hp i⟩: cope G i m)).property
-- finite ordinary lens
lemma pipeSpace (P:Flight i j)(h:4≤j) (C:KernelChoices)(ha:f.val=c.val * P.L.val) {r:ℕ}(p: Fin r→Vec G c 1)(q:Script (Shade G) r)(hp:Summable q)(hx:q.abides)(z:Site c):
     let S:=P.visit (c:=c) (f:=f) C ha
     let M:= Master (G:=G) S P.odd (P.duo C.penalty).A0
     scribe z (opal G.ColorIndex P C.penalty q) (deckW G c ∘ p)=scribe (S.ratio.embed z) q (deckW G f∘ fun i=> M*ᵥ p i):=by
          intro S M; let T:=forest S.ratio P.odd; obtain H:= chrome_sum (W:=G.ColorIndex) (stored P C.penalty C.penalty_pos h); unfold opal; erw [bridge_torque (g:=S.ratio) H _ 0 q hp]; rw [map_zero,add_zero]
          let X:= (P.duo C.penalty).A0; let a:= S.ratio.embed z; let t(i):= tensor G (installed S.ratio X)*ᵥ p i; let x(i):=deckW G f (t i); let s (i):= M *ᵥ p i; let y(i):= deckW G f (s i)
          have he(i:Fin r): ∃ w:deck G.ColorIndex f, y i=x i+cliff w:=by have hp:s i = _ := planes (F:=T) (S:=S) (p i) X; unfold y; rw [hp,map_add,slopeCliff]; exact ⟨_,rfl⟩ -- F syntax
          have hv(t:ℕ):0≤t:=Nat.zero_le _
          choose l hl using he; have hh(i:Fin r):installed S.ratio (chrome G.ColorIndex (linesOf P C.penalty)) *ᵥ ((deckW G c∘ p) i) =x i :=by rw [stage_mul (S:=S)]; unfold Function.comp; rw [LinearEquiv.symm_apply_apply]; rfl
          erw [show (fun i:Fin r=>_) =x from funext hh]; change scribe _ _ _= scribe _ q y
          have hq: ∀ i:Fin r,∀ (u:Fin r→deck _ f)(w:deck G.ColorIndex f), scribe a q (Function.update u i (cliff w))=0:=by
               intro i u p; let w (d:Type)(t:deck d f):deck d f:=fun j=>t (a+j.1,j.2); let V:=u; rw [show _= _ from (show scribe a q (update u i (cliff p))=scribe 0 q (fun j=>w _ (update u i (cliff p) j)) from tsum_congr (fun k=> congr_arg (q k*·) (Finset.prod_congr rfl fun j _=>by change _= Function.update u i _ j (a+(0+wrap f _),_); rw [zero_add])))]; rw [show (fun j: Fin r=>w _ _) = update (fun j=> w _ (u j)) i (cliff (w _ p)) from ?_]; exact hx ..
               funext j; by_cases ht:j=i
               · subst j; rw [Function.update_self,Function.update_self]; funext k; change cliff p _=p (a+(k.1+step _),_) - p (a+_,_); unfold cliff; rw [add_assoc]
               simp [ht]
          symm; let k:= orchestra q a; have ht(i: Fin r→deck (Shade G) f): scribe a q i=k i:= (instruments q hp ..).tsum_eq; let Y (s :Finset (Fin r))(i):= if i∈s then y i else x i
          have hy (p:Finset (Fin r)): k (Y p)=k x:=by
               induction p using Finset.induction_on with
               | empty=> simp [Y]
               | insert i p hi ih=>
                    rw [show Y (insert i p)=Function.update (Y p) i (x i+cliff (l i)) from ?_]; swap
                    · ext1 j; by_cases ht:j=i<;> simp [Y,ht,hl]
                    rw [k.map_update_add,← ht (Function.update _ _ (cliff _)),hq, add_zero, ←(show Y p i=x i from if_neg hi),Function.update_eq_self]; exact ih
          have hz:=hy Finset.univ; rw [show Y Finset.univ=y from funext fun i=>if_pos (Finset.mem_univ _)] at hz; rw [ht,ht,hz]
end YM.OPE.Silt.Float
