import YM.WilsonCoeffUV.Product.Report.OneH
/-!
# Prices from section enrollment
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
variable {m N:ℕ}{L:Side}
open Wilson Tree PathCost AnalyticNext.QuarticMatch.Sheets
lemma rollCup [AddCommGroup U][NormedAddCommGroup V] (P:Ten V (U×α) r)(x y:U) : revolve (x+y) P = revolve x (revolve y P):=by
    funext v; unfold revolve; congr 1; funext i; simp [jog, Equiv.prodCongr_apply,add_assoc]; rfl

lemma patronRay (T: TowerS G D)(F:Rarity D)(x y:ℝ)(A:Levels G){Ñ: ChartRatio G}(g:G.Simple)(f:LocalRatio Ñ)(p:m<N)(u:On k T) (b:Cover)(h:ℕ)(v:0<x):
    let P:=ll A m; ∑ i:Site P.L, drumB h x • verseI A Ñ m N k (shoe T F x y (heapZ P (b,i))) = drumB h (x*P.L.val) • shoe (Spout A Ñ N m h k T) F (x*P.L.val) y b :=by
    intro P
    let M (w:Site P.L):= heapZ P (b,w); let Qw (w:Site P.L):= shoe T F x y (M w); let R:= Spout A Ñ N m h k T; let t:= x*P.L.val
    have hp: Auth k (shoe R F (x*P.L.val) y b):=seaWet _ _ _ _ (ShedG A Ñ p g f u le_rfl) b
    apply Auth.ext (Auth.sum (S:=Finset.univ) (fun i _=>(Auth.verse A p g f (seaWet T F x y u (M i))).μ (drumB h x))) (hp.μ _)
    funext n; let t0:= n*P.L; let K:=A.clock.kernel; let G':=freeForms A N (m+1); let Y:=freeForms A N m; let W:= roam A N m; let s:=stepAt P K n; let O:=xree P K n; let X:=(story A Ñ N (m+1)).1 t0; let V:=T.1 t0; let C:= gradeH P h k; let B:=ratioHigh A Ñ N m; let Z:= (s.ratio.embed (wrap n b)); let F'(j:Site P.L):= gatherT P j (wrap t0 (lift j)) V; let U j:= reed s O G' (W n) Ñ X k (F' j); let f0:= demonstrate (wheelC t y b F.ψ)
    have he w: (Qw w).1 t0= skewV Z (ply f0.toLinearMap (F' w)):= by
       let a:= wrap t0 (lift w); let Y':= tuftV (demonstrate (wheelC x y (M w) F.ψ)) T; change skewV (wrap t0 (M w)) (Y'.1 t0)= _; have ht: wrap t0 (M w)= Z + a:=by unfold a M heapZ; rw [map_add]; exact congr_arg (·+a) (Eq.symm (s.ratio.embed_wrap _))
       rw [ht]; funext i j z; unfold skewV; rw [rollCup]; ext1 v; change T.1 t0 i j (jog _ ∘ (jog _ ∘ z)) (wheelC x y (heapZ _ _) F.ψ v)= T.1 t0 i j _ (foldWord P w D (wheelC (x*P.L.val) y b F.ψ v)); rw [eyelet]
    -- linkWood on inner anchor F' w projected requires auth. use rotation and Wreath. show Cert before.
    have H w: Cert (F' w):=by
        let L:= shifted (tuftV (soprano P w D) T) (lift w)
        exact ((On_auth u).tuft (soprano P w D) |>.shifted (lift w)).token t0
    let V' w:=ply f0.toLinearMap (F' w)
    have hi:= (old A Ñ g f N (m+1) p).basis t0
    have hf w: (verseI A Ñ m N k (Qw w)).1 n= skewV (wrap n b) (ply f0.toLinearMap (Blue.mix B (U w))):=by
       have hq : Cert (V' w):=fun t {_} _ _ _ _ ha=> H w (t.comp f0.toLinearMap) ha
       have hg:1 ≤ (loose A m).L.val:=(loose A m).L.property
       change Blue.mix B (reed s O G' (W n) Ñ X k ((Qw w).1 t0))= _; rw [he]; rw [linkWood s O Ñ f G' Y (W n) (A.blocks m 0).branches ((cond_laws A m N).1 n (n*P.L) rfl) (horizon_step A m N p n _ rfl) (age_sym ..) X hi (ply_shell _ (gather_mark P V w _ (u.launch _))) (fun i=>ply_pure _ (gather_pure P V w _ (u.evenS _ i))) hq (wrap n b),mixed_shift (G:=G) (V:=Lounge)]; apply congr_arg (skewV (wrap n b)); rw [ply_mixX]; exact congr_arg (Blue.mix B) (Eq.symm (reed_maps s O _ _ _ f0.toLinearMap (w:=F' w)))
    rw [Prod.fst_sum,Finset.sum_apply]; simp only [Prod.smul_fst,Pi.smul_apply]; change ∑ i:Site P.L, drumB h x • ((verseI A Ñ m N k (Qw i)).1 n)=drumB h t • skewV (wrap n b) (ply f0.toLinearMap (C • Blue.mix B (tiara P k • ∑ w,U w)))
    have Hz : C • Blue.mix B (tiara P k • (∑ w,U w))=∑ w:Site P.L,(C*tiara P k) • Blue.mix B (U w):= by
       funext i j; simp only [Pi.smul_apply,Finset.sum_apply,Blue.mix]; simp_rw [Finset.smul_sum]; rw [Finset.sum_comm]; exact Finset.sum_congr rfl (fun i _=> Finset.sum_congr rfl fun v _=> by rw [← smul_smul C,smul_comm (tiara P k) _ (U i v j)];
         )
    simp_rw [hf,Hz,map_sum,map_smul]; funext i j z; simp only [Pi.smul_apply,skewV,revolve,Finset.sum_apply,Finset.smul_sum]; apply Finset.sum_congr rfl; intro a _; rw [drum_law P h k x v]; unfold t; rw [mul_assoc]; exact (smul_smul ..).symm

lemma journey (F:Rarity D)(T:TowerS G D)(A:Levels G){Ñ:ChartRatio G}(g:G.Simple)(f:LocalRatio Ñ)(h:On k T)(y:ℝ){x:ℝ}(p:0<x)(t:m<N)(i:ℕ):
    verseI A Ñ m N k (pupil i T F x y)= pupil i (Spout A Ñ N m i k T) F (x*(A.S.block m).val) y:=by
   let P:=ll A m; let v:= x*P.L.val; let Q b (w:Site P.L):= shoe T F x y (heapZ P (b,w)); let R:= verseI A Ñ m N k (V:=Lounge); let S:=(canvasM F v y).product (Finset.univ:Finset (Site P.L))
   rw [tiler P F x y p T i,←Finset.sum_product']; change verseI A Ñ m N k (∑ i' ∈ S, drumB i x • Q i'.1 i'.2)=_; rw [verse_sum A g t f (P:=fun v=> Q v.1 v.2) (S:=S) (fun i _=> seaWet T F x y h _)]; unfold S; rw [show (canvasM F v y).product Finset.univ=(canvasM F v y) ×ˢ (Finset.univ:Finset (Site P.L)) from rfl,Finset.sum_product' (f:=fun b w=>drumB i x • verseI A Ñ m N k (Q b w))]; exact Finset.sum_congr rfl fun i' _=>patronRay T F x y A g f t h i' i p
end YM.WilsonCoeffUV.Mer
