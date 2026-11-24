import YM.OPE.Screens.Deck
/-! # Probe budget after pricing

Finite polynomial in any signed rows across masks can be observed on any
far test word/correlation, if the complete comparison was paid on regulator.
Keep axes clear *among points in each row*, and stagger the guest words as before.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log.Trunk.Shuttle
open Function Filter Finset MeasureTheory Lattice RG Wilson Next.UVStress Spec Cards
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J Z : Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J] {G:Gauge}
    {k b n m l q u j p N W :ℕ} {C:Family G} {c A:ℝ}
    {F:Extraction.Order} {S:Table C.book}(U:Final C F S)
    {f:Filter (ℕ×ℕ)}[f.NeBot] (h:f≤ F.fuse)
    {x:I→ Cover} {z:J→ Cover} {v:I→ C.book.Token} {V:ReadLabel C v}
    {w:J→ C.book.Token} {y:J→ E4} {α:J→ℝ}
local notation "T!"=> C.S.gridPoint
namespace Probe
variable (p':Spark C f k) (D:Org.Grill C F)
abbrev point (p': Spark C f k) := T! k ∘ p'.x
def view (w:J→ C.book.Token)(y:J→ E4) := viewing U (beside (point p') y) (beside p'.v w)
def read (A:Table C.book)(w:J→ C.book.Token)(y:J→ E4) := observe A (beside (point p') y) (beside p'.v w)
def joint (w:J→ C.book.Token)(z:J→ Cover)(e:k ≤ j)(hc:Screen (beside (point p') (T! j ∘ z))) : Spark C f j where
    Index := p'.Index⊕ J
    x := beside (zoom C.S e ∘ p'.x) z
    v := beside p'.v w
    q := combine p'.q (frozen C w)
    limit i:= by cases i ; exact p'.limit _; exact tendsto_const_nhds
    frames := by rw [beside_commutes,show T! j ∘ zoom C.S e ∘ p'.x=point p' from funext fun i=> zoom_grid e _]; exact hc
lemma coupled (e:k ≤ j)(hc:Screen (beside (point p') (T! j ∘ z))) (w:J→ C.book.Token) : (joint p' w z e hc).glance U=view U p' w (T! j ∘ z):= by
    unfold Spark.glance; dsimp only [joint]; rw [beside_commutes,show T! j ∘ zoom C.S e ∘ p'.x=point p' from funext fun i=> zoom_grid e _]; rfl
lemma entered (e:k ≤ j)(hc:Screen (beside (point p') (T! j ∘ z))) (w:J→ C.book.Token)(h:j ≤ N): (joint p' w z e hc).cuts N p = p'.cuts N p * register C j z (germ (frozen C w)) N p:=by
    unfold Spark.cuts; change register C j (beside (zoom C.S e ∘ p'.x) z) (germ (combine p'.q (frozen C w))) N p=_; rw [works p'.q (frozen C w) j N p]; congr 1; funext u; simp_rw [germ_here]; dsimp only [comp_apply]; simp_rw [zoom_local _ e _ _ h]
-- expect <> throws & extend to any entire sum. Stamp.Work.Entrance.Price.P.*
variable {X': Cylinder C}
local notation "μ"=> C.S.a
variable (a:Fin n→ℂ)(L:Fin n→ Spark C f k)
    (he:Hall C.S b l q u W 1 (Fintype.card J))
    (hf:Prepared (C:=C) w F W α)
    (hp: ∀ᶠ i:ℕ×ℕ in f, PaidAt C.S i.1 i.2 q (C.beta i.1 i.2) c (X' i.1 i.2))
    (hE: ∀ᶠ i:ℕ×ℕ in f,(fun U:Config G (C.side i.1 i.2)=> ∑ j:Fin n, a j*(L j).cuts i.1 i.2 U)=X' i.1 i.2)
include U h he hf hp hE D
local notation "Z!"=> (fun _ : Unit=> (0:E4))
lemma customs (e:k≤ j)(hb:b≤j)(hx: ∀ i,Screen (beside (point (L i)) (C.S.gridPoint j ∘ z))) (hδ:Gap C.S j z (2*C.S.a l)) (hw: ApartFrom (2*C.S.a b) (Z!) (C.S.gridPoint j ∘ z)) : ‖∑ i:Fin n,a i • view U (L i) w (C.S.gridPoint j ∘ z)‖ ≤ c*∏ i,α i:=by
    let Y i:= joint (L i) w z e (hx i); let M i:=view U (L i) w (T! j ∘ z); let u (_:Unit):= (0:Cover); have ht:GapTo C.S j u z (2* C.S.a b):=fun i j'=> (by unfold u; rw [grid_zero]; exact hw i j')
    let Z :=germ (frozen C w)
    have he': TileDoc U j f (∑ i,a i • M i) (fun N p V=> ∑ i,a i* (Y i).cuts N p V):=by
       rw [show M=(fun i=> (Y i).glance U) from funext fun i=>(coupled ..).symm]; exact TileDoc.sparks ..
    apply le_trans (TileDoc.global U he' (B:= fun _ :Unit=>c) (w:=Z) D hb h (show Gap C.S j u (2* μ b) from fun i j h=>(h (Subsingleton.elim ..)).elim) hδ ht he (z:=fun _=> X') (fun i=> hp) (fun i=> (hf.here i).filter_mono h) ?_) (by simp only [prod_const,card_univ,Fintype.card_unique,pow_one,le_refl]); filter_upwards [(largeMesh F|>.mono_left h).eventually_ge_atTop j,hE] with i hi he; funext V; rw [just_one X']; have hp:∑ j:Fin n,a j*(L j).cuts i.1 i.2 V=X' i.1 i.2 V:=congr_fun he V; simp_rw [Y,entered _ e _ _ (show j ≤ i.1 from hi),Pi.mul_apply,←mul_assoc]; rw [← hp,sum_mul]

lemma border (e:b≤ k) (hx: ∀ i, Injective (beside (point (L i)) y)) (hδ:Apart (2*C.S.a l) y) (hw: ApartFrom (2*C.S.a b) (Z!) y) : ‖∑ i:Fin n,a i • view U (L i) w y‖ ≤ c*∏ j,α j:=by
    let W:= univ.biUnion (fun i=> univ.image (point (L i))); let V i:= Cloud.unitGrid C.S i W y; let z i:= Cloud.grid W (C.S.a i) y (fun _ _=>0); have hV:= Cloud.gridded W y C.S; have hS(i):Screen (V i):=Cloud.screened W _ (C.S.a_pos i) _ _
    apply (glance_contract U (mul_nonneg hp.exists.choose_spec.cost hf.cost)).mpr; intro v
    let M:= read (J:=J) (f:=f) (C:=C) (k:=k); let f' (y:J→ E4):= ∑ i:Fin n,a i*M (L i) (spectator U v) w y; have hm(y) (hx:∀ i,Injective (beside (point (L i)) y)): (glance U v) (∑ i,a i • view U (L i) w y) = f' y:=by
        rw [map_sum]; unfold f'; refine sum_congr rfl fun i hi=> ?_; rw [map_smul,view,glance_sees U v _ _ (hx i)]; rfl
    rw [hm y hx]; refine le_of_tendsto (show Tendsto (fun i:ℕ=> ‖f' (V i)‖) atTop (𝓝 ‖f' y‖) from (tendsto_finsetSum univ (fun i _=> ((smooth_observe (spectator U v) (spectate U v).smooth (beside (L i).v w) (hx i)).tendsto.comp (Cloud.beside_tends (z:=fun _:ℕ=> point (L i)) tendsto_const_nhds hV)).const_mul (a i))).norm) ?_
    filter_upwards [cross_limit (show Tendsto (fun _:ℕ=> (Z!)) atTop (𝓝 (Z!)) from tendsto_const_nhds) hV hw, apart_limit hV hδ,eventually_ge_atTop k] with i hh hδ ht; have hY(j): Screen (beside (point (L j)) (V i)):= by
       apply Screen.reserve.mpr; refine ⟨(L j).frames,hS i,fun x y a=> ?_⟩; exact (Cloud.clears (I:=J) W _ (C.S.a_pos i) _ _ a (fun _ _=>0) (point (L j) x) (mem_biUnion.mpr ⟨j,mem_univ _,mem_image_of_mem _ (mem_univ _)⟩)).symm
    rw [← hm (V i) (fun j=> (hY j).coin)]; exact le_trans (glance_bound ..) (customs (j:=i) (z:=z i) U h D a L he hf hp hE ht (e.trans ht) hY hδ hh)
end Probe
end YM.OPE.Log.Trunk.Shuttle
