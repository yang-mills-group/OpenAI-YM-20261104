import YM.WilsonCoeffUV.Product.Connected.JoinCover
/-!
# Contour cumulants at first join
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Soil
open Gauge Power PathCost Precision Embroider Fountain Cosmos Shard Realm
open PowerSeries
open scoped Topology BigOperators
variable {n c:Side}{U V α β:Type*}{r h D j e i l k:ℕ}{A B C s:ℝ}{G:Gauge}
def agateV [NormedRing V][NormedAlgebra ℝ V](X Y:Era G V): Era G V:= ((fun n=>woad (X.1 n) (Y.1 n)),woad X.2 Y.2)
lemma AuthCertSpan [NormedRing V][NormedAlgebra ℝ V]{X Y:Parcelized V G n}(p:shellK i X)(q:shellK j Y)(x:Cert X)(y:Cert Y)(u:U→ V→ₐ[ℝ]ℝ)(h:∀ x y:V,(∀ i,u i x=u i y)→x=y): Cert (woad X Y):=by
    apply certify (fun i=>(u i).toLinearMap) h _ (woad_shell X Y p q)
    intro i Z I z A A' H; let L:=u i; rw [woad_ply X Y (u i), woadap _ _ (finite_shell (ply_shell (u i).toLinearMap p)) (finite_shell (ply_shell (u i).toLinearMap q)),map_mul,map_mul]; exact congr_arg₂ (·*·) (x L.toLinearMap H) (y L.toLinearMap H)
lemma Auth.woadB [NormedRing V][NormedAlgebra ℝ V]{X Y:Era G V}(x:Auth i X)(y:Auth j Y)(u:U→ V→ₐ[ℝ]ℝ)(p:∀ x y:V,(∀ i,u i x=u i y)→x=y): Auth (i+j) (agateV X Y):=by
    refine ⟨?_,?_,?_,?_⟩
    · exact Bends_woad (V:=V) (U:=Hooks G) (P:=X.1) (Q:=Y.1) (S:=X.2) (T:=Y.2) x.wing y.wing
    · exact fun n=> woad_shell (X.1 n) (Y.1 n) (x.span n) (y.span n)
    · exact fun n=> woad_pure (X.1 n) (Y.1 n)
    exact fun n=> AuthCertSpan (x.span n) (y.span n) (x.token n) (y.token n) u p
lemma Auth.manor {X Y : Era G ℝ}(p:Auth i X)(q:Auth j Y): Auth (i+j) (agateV X Y):= p.woadB q (fun _:Unit=>AlgHom.id ℝ ℝ) (fun _ _ h=> h ())
lemma blend_woad (T S:Pal ℝ U)(A:Cost): Blue.mix A (T-S)=Blue.mix A T-Blue.mix A S:=by funext i j; unfold Blue.mix; simp only [Pi.sub_apply, Finset.sum_sub_distrib,smul_sub]

section
open Wilson Tree AnalyticNext.QuarticMatch.Sheets Exterior
variable {m N:ℕ}
def JoinGap (A:Levels G)(Ñ:ChartRatio G)(m N k h:ℕ)(P Q:Era G ℝ):Era G ℝ:= verseI A Ñ m N (k+h) (agateV P Q) - agateV (verseI A Ñ m N k P) (verseI A Ñ m N h Q)
abbrev joinC (I:Gear G)(X:Stand I)(k:ℕ)(V W:Bookend ℝ G): Bookend ℝ G:= Blue.mix X.moving (hotC I.patch I.kernel I.angle X.R X.Q X.page k V W)
lemma heatMiss (A: Levels G){Ñ:ChartRatio G}{X Y:Era G ℝ}(p:Auth i X)(q: Auth j Y)(g:G.Simple)(f:LocalRatio Ñ)(t:m<N):
    (JoinGap A Ñ m N i j X Y).2=Blue.mix (ratioHigh A Ñ N m) (hotC (ll A m) A.clock.kernel Ñ (shuttleM (conditional A N m)) (shuttleM (feedA A N m)) (actionW A Ñ N (m+1)) (i+j) X.2 Y.2):=by
   have e:= old A Ñ g f N (m+1) t; let P:= ll A m; let K:=A.clock.kernel; let R:= roam A N m; let u (n:Side):=n*P.L; let H:=freeForms A N (m+1); let Z (n:Side):=(story A Ñ N (m+1)).1 (n*P.L)
   let S n:= stepAt P K n; let O n:=xree P K n; let W n:=boiling (S n) (O n) H (R n) Ñ (Z n) (X.1 (u n)) (Y.1 (u n)); let D (n:Side) (e):= Blue.fade plug (finallyA (i+j) (W n) e); let Q:= ratioHigh A Ñ N m; let T:=JoinGap A Ñ m N i j X Y
   have he n:T.1 n=Blue.mix Q (D n):=by
      let U:= X.1 (u n); let V:=Y.1 (u n); let s h:=reed (R:=ℝ) (S n) (O n) H (R n) Ñ (Z n) h
      let F:= s i U; let L:= s j V; have hp:= e.basis (u n); change Blue.mix Q (s (i+j) (woad U V))-woad (Blue.mix Q F) (Blue.mix Q L)=_
      rw [← mix_wreath F L Q (reed_band _ _ _ _ _ hp.lamp f (p.span _)) (reed_band _ _ _ _ _ hp.lamp f (q.span _)),← blend_woad]; exact congr_arg (Blue.mix Q) (reed_miss (S n) (O n) H (R n) Ñ (Z n) U V (p.span _) (q.span _) hp.lamp f)
   let V':= hotC P K Ñ (shuttleM (conditional A N m)) (shuttleM (feedA A N m)) (actionW A Ñ N (m+1)) (i+j) X.2 Y.2
   funext i r; have h: Auth _ T:=(Auth.verse A t g f (p.manor q)).sub ((Auth.verse A t g f p).manor (Auth.verse A t g f q)); apply Soil.Bends.exten (h.wing i r)
   apply (bend_mixX (P:=D) (Q:=V') ?h Q i r).congr (Eventually.of_forall fun n=>congr_fun (congr_fun (he n).symm _) _)
   case h=>
    intro a b; unfold V' hotC sluice finallyA
    let F (n:Side) k:=bend (weaveH (ratioN P.L n) G) (W n k a)
    refine Bends.congr (Soil.Bends.scooped (leaderT (P:=F) (F:=fun k=> boilC P K Ñ (shuttleM (conditional A N m)) (shuttleM (feedA A N m)) (actionW A Ñ N (m+1)) X.2 Y.2 k a) (s:=Finset.range _) (fun i _=>gorgeThermo P K Ñ (A.blocks m 0).branches f (resin A N m t) e.basis e.patch X Y p q i _ _))) (Eventually.of_forall fun n=>?_)
    dsimp only [F,D]; rw [into_shade (ratioN P.L n)]; unfold sluice finallyA; rw [bend_sum]
end
end YM.WilsonCoeffUV.Mer
