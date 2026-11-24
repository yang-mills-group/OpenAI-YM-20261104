import YM.OPE.Compatible.Copper.Cumulus
/-!
# Three-component signed balance through tests. uniform exterior layout on fixed clearance. quantities needed on the root registration only. (All grade estimates are separate.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open MeasureTheory Function Filter Set Lattice Cells Wilson Extraction Word
open Cards Bid Spec
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{F: Extraction.Order}{S:Table C.book} (U: Final C F S) (h: Org.Grill C F)
variable {I J Z : Type}[Fintype I][Fintype J][Fintype Z] {N p k f b l n q: ℕ}
   {d:ℕ}{t:ℝ}
variable {x:I→ Cover}{z:Z→ Cover}{v:I→ C.book.Token}{u:Z→ C.book.Token}{w:J→ C.book.Token}{y:J→ E4}
    {φ:Filter (ℕ×ℕ)}[φ.NeBot]{B:J→ℝ} {D:ReadLabel C v}{L:ReadLabel C u}{Q:C.label d}{g:ℕ×ℕ→ C.label d}
set_option quotPrecheck false
local notation "Ω"=>C.S.gridPoint k
local notation "z0"=> (fun _ : Unit=> (0:E4))
local notation "V!"=> (fun _:Unit=> (⟨d,Q⟩: C.book.Token))
include U h
lemma testThird (hk:b ≤ k)(hx:Screen (C.S.gridPoint k ∘ x))(hz:Screen (C.S.gridPoint k ∘ z)) (hp: Apart (2*C.S.a l) y)(hd: ApartFrom (2*C.S.a b) z0 y) (hf:Injective (beside (Ω ∘ x) y))(ht:Injective (beside (Ω ∘ z) y))
    (he:Hall C.S b l q f n 1 (Fintype.card J)) (hr:φ≤ F.fuse) (hU:∀ i,Tendsto (D i) φ (𝓝 (v i).2))(hL:∀ i,Tendsto (L i) φ (𝓝 (u i).2))(hg:Tendsto g φ (𝓝 Q))
    (hB : ∀ᶠ i:ℕ×ℕ in φ, PaidAt C.S i.1 i.2 q (C.beta i.1 i.2) t ((register C k x (germ D) i.1 i.2-register C k z (germ L) i.1 i.2)-C.O i.1 i.2 (g i) 0))
    (hD: Prepared (C:=C) w F n B) (a:Viewers U):
    ‖(observe (spectator U a) (beside (Ω ∘ x) y) (beside v w)- observe (spectator U a) (beside (Ω ∘ z) y) (beside u w))-observe (spectator U a) (beside z0 y) (beside V! w)‖≤ t*∏ i,B i:=by
    let p':= spectator U a; let A:= Ω ∘ x; let A':= Ω ∘ z; let W:= insert (0:E4) (Finset.univ.image A ∪ Finset.univ.image A'); let Y i:=Cloud.unitGrid C.S i W y; let u' i:=Cloud.grid W (C.S.a i) y (fun _ _=>0); have hY:Tendsto Y atTop (𝓝 y):=Cloud.gridded W _ _
    have hS(i): Screen (Y i):= Cloud.screened _ _ (C.S.a_pos _) _ _; have hκ(k' i):∀ a,∀ y∈W,Y k' i a≠y a:=fun a=> Cloud.clears _ _ (C.S.a_pos k') _ i a (fun _ _=>0)
    have hu:Injective (beside z0 y):= hd.together (mul_nonneg zero_le_two (C.S.a_pos _|>.le)) (injective_of_subsingleton _) (hp.coin (mul_nonneg zero_le_two (C.S.a_pos _|>.le)))
    have hv{I : Type}[Fintype I](A:I→E4)(D:I ⊕ J → C.book.Token)(hi:Injective (beside A y)): Tendsto (fun i=> observe p' (beside A (Y i)) D) atTop (𝓝 (observe p' (beside A y) D)):= (smooth_observe _ (spectate U a).smooth D hi).tendsto.comp (Cloud.beside_tends (show Tendsto (fun t:ℕ=> A) atTop _ from tendsto_const_nhds) hY)
    refine le_of_tendsto ((((hv _ (beside v w) hf).sub (hv _ (beside u w) ht)).sub (hv _ (beside V! w) hu)).norm) ?_
    filter_upwards [apart_limit hY hp,cross_limit (show Tendsto (fun t:ℕ=> z0) atTop _ from tendsto_const_nhds) hY hd,eventually_ge_atTop k] with i hψ ht hi
    have he'{U':Type}[Fintype U'](x:U'→ E4)(hx:Screen x)(hy:∀ j,x j∈W) : Screen (beside x (Y i)):=Screen.reserve.mpr ⟨hx,hS _,fun a b s h=> hκ _ _ _ _ (hy _) h.symm⟩
    have hS₁: Screen (beside (Ω ∘ x) (Y i)):= he' _ hx (fun a=>Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem A (Finset.mem_univ _))))
    have hS₂: Screen (beside (Ω ∘z) (Y i)):=he' _ hz (fun a=>Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem A' (Finset.mem_univ _))))
    have hS₃: Screen (beside z0 (Y i)):= he' _ (fun _=> injective_of_subsingleton _) (fun _=>Finset.mem_insert_self ..)
    change ‖observe _ (beside _ (Y i)) (beside v w)-observe _ (beside _ (Y i)) (beside u w)-observe _ (beside _ (Y i)) (beside V! w)‖ ≤ _
    rw [← glance_sees U a _ _ hS₁.coin,← glance_sees U a _ _ hS₂.coin,← glance_sees U a _ _ hS₃.coin,← map_sub,← map_sub]; apply le_trans (glance_bound ..)
    let T:= C.S.gridPoint i; have hc:T ∘ sole (0:Cover)=z0:=funext fun _=> grid_zero ..; have hK:T ∘ zoom C.S hi ∘ x=Ω ∘ x:= funext fun _=> zoom_grid hi _; have hK':T ∘ zoom C.S hi ∘ z=Ω ∘ z:=funext fun _=> zoom_grid hi _
    have hh':GapTo C.S i (sole (0:Cover)) (u' i) (2*C.S.a b):=by change ApartFrom _ (T ∘ sole _) (Y i); rw [hc]; exact ht
    rw [← hc, ← hK, ← hK']; refine mirrorThird U h (x:=zoom C.S hi ∘ x) (z:=zoom C.S hi ∘ z) (y:=u' i) (hk.trans hi) hψ hh' (hK.symm ▸ hS₁) (hK'.symm ▸ hS₂) (hc.symm ▸ hS₃) he hr hU hL hg ?_ hD
    filter_upwards [hB,((Cards.largeMesh F).eventually_ge_atTop i).filter_mono hr] with s h L; change i ≤ s.1 at L; unfold register; simp only [comp_apply,zoom_local _ hi _ _ L]; exact h
-- exterior public
lemma billedThird (w:J→ C.book.Token){c:ℝ}(hc:0<c) : ∀ᶠ j:ℕ in atTop,∃ A:ℝ,0 ≤ A∧ ∀ (W:ℕ), j ≤ W → ∀ {I Z:Type}[Fintype I][Fintype Z]{v:I→ C.book.Token}{p:Z→ C.book.Token}{t:ℝ} {d:ℕ}{φ:Filter (ℕ×ℕ)}[φ.NeBot](x:I→ Cover)(z:Z→ Cover){D:ReadLabel C v}{L:ReadLabel C p}{Q:C.label d}{g:ℕ×ℕ→ C.label d}, Screen (C.S.gridPoint W ∘ x)→Screen (C.S.gridPoint W ∘ z)→ φ≤ F.fuse→ (∀ i,Tendsto (D i) φ (𝓝 (v i).2))→(∀ i,Tendsto (L i) φ (𝓝 (p i).2))→ Tendsto g φ (𝓝 Q)→(∀ᶠ i:ℕ×ℕ in φ, PaidAt C.S i.1 i.2 j (C.beta i.1 i.2) t ((register C W x (germ D) i.1 i.2-register C W z (germ L) i.1 i.2)-C.O i.1 i.2 (g i) 0)) → ∀ y:J→ E4, ClearOf 0 y c → Injective (beside (C.S.gridPoint W ∘ x) y)→ Injective (beside (C.S.gridPoint W ∘ z) y)→∀ a:Viewers U, ‖(observe (spectator U a) (beside (C.S.gridPoint W ∘ x) y) (beside v w)- observe (spectator U a) (beside (C.S.gridPoint W ∘ z) y) (beside p w))-observe (spectator U a) (beside z0 y) (beside (fun _: Unit=> (⟨d,Q⟩: C.book.Token)) w)‖≤ t*A:=by
   have hw:=C.S.shrinks; obtain ⟨b,hb⟩:= ((hw.const_mul 2).eventually (by rw [mul_zero]; exact gt_mem_nhds hc)).exists; have hh:(Tendsto (fun i=> (1:ℝ)*(2*(5*C.S.a i))) atTop (𝓝 0)):=by simpa only [mul_zero] using (((hw.const_mul 5).const_mul 2).const_mul 1)
   obtain ⟨i,he,hi⟩:= ((hh.eventually (gt_mem_nhds (C.S.a_pos b))).and (eventually_ge_atTop b)).exists; have hx:Tendsto (fun k=> (↑(Fintype.card J):ℝ)*(2*(3*C.S.a k))) atTop (𝓝 0):=by simpa only [mul_zero] using (((hw.const_mul 3).const_mul 2).const_mul (↑(Fintype.card J):ℝ))
   obtain ⟨l,hj,hn,Y,hY⟩:= ((hx.eventually (gt_mem_nhds (C.S.a_pos i))).and ((eventually_ge_atTop i).and (prepared_some U w))).exists
   filter_upwards [eventually_ge_atTop i] with k hk
   refine ⟨∏ u,Y u,hY.cost, fun W hW I Z _ _ v p t d φ _ x z D L Q g he' hy hr hX hZ hg hD y hh hx hv a=>?_⟩
   have hS:Hall C.S b i k i l 1 (Fintype.card J):=⟨hi,le_rfl,hk,hn,by simpa only [Nat.cast_one] using he,hj⟩; have hP:= hh.steered hb hi; exact testThird U h (hi.trans (hk.trans hW)) he' hy hP.1 hP.2 hx hv hS hr hX hZ hg hD hY a
end YM.OPE
