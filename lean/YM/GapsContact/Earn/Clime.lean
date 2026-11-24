import YM.GapsContact.Earn.Reef
import YM.Frontier6.Multi.Diff.Steer
/-!
# Variant of Swept cost in YM.OPE.Log.Spill.

Also for independently (same Wall) paid ext readings. Ext may have fully
varying token costs in the actual `Vane`. Require convergence in labels
at each chosen length. also with variable representatives in a configuration at cutoff
-/
set_option autoImplicit false
noncomputable section
namespace YM.GapsContact.Seams
open MeasureTheory Function Filter Set Lattice Cells Wilson Extraction Word
open OPE OPE.Log OPE.Cards Bid Spec
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{F : Extraction.Order}{S:Table C.book} (U: Final C F S)(h:Org.Grill C F)
variable {I J : Type}[Fintype I][Fintype J] {N p k f b l n q : ℕ}
variable {𝓕 : Filter (ℕ×ℕ)}
variable {B:I→ℝ}{D:J→ℝ} {x:I→ Cover}{v:I→ C.book.Token}{y:J→ Cover}{w:J→ C.book.Token}
    (Z:ReadLabel C v)(Y:ReadLabel C w)

variable {t:ℕ}{P: ℕ×ℕ→ C.label t}{a:C.label t}(o:ℝ)
local notation "Z0"=> (fun _ : Unit=> (0:Cover))
local notation "T'" => C.S.gridPoint k
include h
lemma unionCoast {X:ReadLabel C v}(hX:∀ i,Tendsto (X i) 𝓕 (𝓝 (v i).2))(hk:b ≤ k)(hp:Gap C.S k y (2*C.S.a l))(hd:GapTo C.S k (Z0) y (2*C.S.a b))
    (hf:Screen (beside ((T') ∘ x) ((T') ∘ y)))
    (hx:Screen (beside ((T') ∘ Z0) ((T') ∘ y)))
    (he:Hall C.S b l q f n 1 (Fintype.card J)) [𝓕.NeBot] (hr:𝓕≤ F.fuse)(hz:Tendsto P 𝓕 (𝓝 a))
    (hB : ∀ᶠ i:ℕ×ℕ in 𝓕, PaidAt C.S i.1 i.2 q (C.beta i.1 i.2) o (register C k x (germ X) i.1 i.2 - C.O i.1 i.2 (P i) 0))
    (hD:∀ j, ∀ᶠ i:ℕ×ℕ in 𝓕,PaidAt C.S i.1 i.2 n (C.beta i.1 i.2) (D j) (C.O i.1 i.2 (d:=(w j).1) (Y j i) 0))(hY:∀ j,Tendsto (Y j) 𝓕 (𝓝 (w j).2)) :
    ‖viewing U (beside ((T') ∘ x) ((T') ∘ y)) (beside v w) - viewing U (beside ((T') ∘ Z0) ((T') ∘ y)) (beside (fun _ : Unit=>⟨t,a⟩) w)‖ ≤ o * ∏ i,D i:=by
    let G := X; let Y' := Y; let V (_ : Unit):C.book.Token:= ⟨t,a⟩; let W:ReadLabel C V:= fun _=>P; rw [← beside_commutes] at hf hx; rw [← beside_commutes,← beside_commutes]
    let S:Cylinder C:=fun N p=> register C k x (germ G) N p - C.O N p (P (N,p)) 0; have hv(j): Tendsto (combine G Y' j) 𝓕 (𝓝 ((beside v w j).2)):=by cases j ; exact hX _; exact hY _
    have hu(j):Tendsto (combine W Y' j) 𝓕 (𝓝 ((beside V w j).2)):=by cases j; exact hz; exact hY _
    have hl: Gap C.S k Z0 (2*C.S.a b):=fun i j h=> (h (Subsingleton.elim ..)).elim
    have hQ: TileDoc U k 𝓕 (viewing U ((T') ∘ beside x y) (beside v w) - viewing U ((T') ∘ beside Z0 y) (beside V w))
        (register C k (beside x y) (germ (combine G Y')) - register C k (beside Z0 y) (germ (combine W Y'))):= TileDoc.diff U hf hx hv hu
    apply le_trans (TileDoc.global U hQ (B:=fun _ : Unit=>o) h hk hr hl hp hd he (z:=fun _=> S) (w:=germ Y') (fun _=> hB) hD ?_) (by simp)
    filter_upwards with i; let R:Cylinder C:= fun N p=> C.O N p (P (N,p)) 0; simp only [Pi.sub_apply]
    rw [works,works, just_one S, show germ W =(fun _=>R) from rfl, just_one R]; unfold S; rw [sub_mul]
variable {Z' Z'': J→ E4} {A:ℝ}
local notation "z0"=> (fun _ : Unit=> (0:E4))
omit h
include h in
lemma stylus_clime {Y₀: ReadLabel C v} (h0:∀ i,Tendsto (Y₀ i) 𝓕 (𝓝 (v i).2))(hk:b ≤ k)(hh: Screen (T' ∘ x))(hp: Apart (2*C.S.a l) Z')(hd:ApartFrom (2*C.S.a b) z0 Z') (hT:Injective (beside ((T') ∘ x) Z'))
    (he:Cards.Hall C.S b l q f n 1 (Fintype.card J)) [𝓕.NeBot] (hr:𝓕 ≤ F.fuse)(hz:Tendsto P 𝓕 (𝓝 a))
    (hB: Stylus Y₀ 𝓕 k q t x P A)(hD:∀ j, ∀ᶠ i:ℕ×ℕ in 𝓕,PaidAt C.S i.1 i.2 n (C.beta i.1 i.2) (D j) (C.O i.1 i.2 (d:=(w j).1) (Y j i) 0))(hH:∀ j,Tendsto (Y j) 𝓕 (𝓝 (w j).2)) :
    ‖viewing U (beside (T' ∘ x) Z') (beside v w) - viewing U (beside z0 Z') (beside (fun _ : Unit=>⟨t,a⟩) w)‖ ≤ A * ∏ i,D i:=by
    classical
    let W:= insert (0:E4) (Finset.univ.image fun i=> (T') (x i)); let z i:= Cloud.unitGrid C.S i W Z'; let y(i:ℕ):= Cloud.grid W (C.S.a i) Z' (fun _ _=>0); let V (_ : Unit):C.book.Token:= ⟨t,a⟩
    have hZ:Tendsto z atTop (𝓝 Z'):= Cloud.gridded W _ _; have hS(i): Screen (z i):= Cloud.screened _ _ (C.S.a_pos _) _ _
    have hx(k' i):∀ a,∀ y∈W,z k' i a≠y a:= fun a=> Cloud.clears _ _ (C.S.a_pos k') _ i a (fun _ _=>0)
    have hY: Injective (fun _:Unit=> (0:E4)):= injective_of_subsingleton _ -- remove i
    have hA(k): 0≤ 2*C.S.a k:=mul_nonneg zero_le_two (C.S.a_pos _|>.le)
    have hu:= hd.together (hA _) hY (hp.coin (hA _)); apply (glance_contract U (mul_nonneg hB.receipt.exists.choose_spec.cost (Finset.prod_nonneg (fun i _=> (hD i).exists.choose_spec.cost)))).mpr; intro u
    rw [map_sub,glance_sees _ _ _ _ hT,glance_sees _ _ _ _ hu]
    let S':= spectator U u; have hv:=(spectate U u).smooth
    refine le_of_tendsto (((Tendsto.sub ((smooth_observe S' hv (beside v w) hT).tendsto.comp (Cloud.beside_tends (show Tendsto (fun t:ℕ=> (T') ∘ x) atTop _ from tendsto_const_nhds) hZ)) ((smooth_observe S' hv (beside V w) hu).tendsto.comp (Cloud.beside_tends (show Tendsto (fun t:ℕ=> z0) atTop _ from tendsto_const_nhds) hZ)))).norm) ?_
    filter_upwards [apart_limit hZ hp,cross_limit (show Tendsto (fun t:ℕ=> z0) atTop _ from tendsto_const_nhds) hZ hd,eventually_ge_atTop k] with i hψ hκ hi
    have hG:Screen (beside ((T') ∘ x) (z i)):= Screen.reserve.mpr ⟨hh,hS i,fun a b s h=> hx _ _ _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ a))) h.symm⟩; have hQ:Screen (beside z0 (z i)):= Screen.reserve.mpr ⟨(fun _=> injective_of_subsingleton _), hS i,fun a b s h=>hx _ _ _ _ (Finset.mem_insert_self ..) h.symm⟩
    change ‖observe _ (beside _ (z i)) _ - observe _ (beside _ (z i)) _‖ ≤ _
    rw [← glance_sees U u _ _ hG.coin, ← glance_sees U u _ _ hQ.coin,← map_sub]; apply le_trans (glance_bound ..) ?_
    have hc := (show (C.S.gridPoint i) ∘ (fun _ : Unit=> (0:Cover))=z0 from funext fun _=> grid_zero ..)
    have hK := (show C.S.gridPoint i ∘ zoom C.S hi ∘ x=(T') ∘ x from funext fun _=> zoom_grid hi _)
    rw [← hK,← hc]
    refine unionCoast U h Y A h0 (x:=zoom C.S hi ∘ x) (y:=y i) (hk.trans hi) hψ ?_ (hK.symm ▸ hG) (hc.symm ▸ hQ) he hr hz ?_ hD hH
    · change ApartFrom _ ((C.S.gridPoint i) ∘ _) (z i); rw [hc]; exact hκ
    filter_upwards [hB.receipt, ((Cards.largeMesh F).eventually_ge_atTop i).filter_mono hr] with w hw hV; change i≤w.1 at hV; unfold Cards.register at *; simp only [comp_apply,zoom_local _ hi _ _ hV]; simpa only [comp_apply] using hw

open RG Frontier6 Frontier6.Tale

/-- Explicit symbolic residual on the theory whose prescription already extends these
words. Evaluate not at phase-wise projection but joint `poll` of a live word and its tests. -/
abbrev peal (s:StateIndex U) := poll S (state U s)
def spendsWord {X:Type*}[Fintype X](x:X→ E4)(d:X→ℕ)(v:∀i,S.Field (d i)):= assembly S x (fun i=>⟨d i,v i⟩)
-- product-valued cut, centroid may translate but rule invariant
lemma peal_view {I:Type}[Fintype I](s:StateIndex U){x:I→ E4}(hx:Injective x)(v:I→ C.book.Token): peal U s (assembly S x (S.classTokens ∘ v)) = glance U s (viewing U x v):=by
   rw [peal,Tale.acast U s,if_pos hx,glance_sees U s _ _ hx];
   have ht:state U s=spectator U s:=by cases s <;> rfl
   rw [ht]; exact (observe_exact _ v (spectate U s|>.laws.toSymmetric) (spectate_respects U s) hx).symm

lemma peal_meter {x:I→ E4} {y:J→E4}(s:StateIndex U)(hx:Injective (beside x y))(v:I→ C.book.Token)(w:J→ C.book.Token): peal U s (assembly S x (S.classTokens ∘ v) * assembly S y (S.classTokens ∘ w))= glance U s (viewing U (beside x y) (beside v w)) :=by
   rw [← Tale.concatenates, ← peal_view U s hx, beside_commutes];rfl
lemma peal_slot {x:E4}{y:J→E4} {k:C.book.Token} {w:J→ C.book.Token} (s:StateIndex U)(h:Injective (beside (fun _ : Unit=>x) y)) :peal U s (letter S x (S.classTokens k)*assembly S y (S.classTokens ∘ w))= glance U s (viewing U (beside (fun _ : Unit=>x) y) (beside (fun _ : Unit=>k) w)):=by simpa [assembly,Fintype.prod_unique] using peal_meter U s h (fun _=>k) w

-- `Stall` stores exactly the candidate field projection and preserves witnesses; still junk if outside geometry.
def Stall (𝓛:Ultrafilter (ℕ×ℕ))(S:Table C.book)(k m j:ℕ) (A A':ℝ)(d:ℕ)(x:I→ Cover)(v:I→ S.Tag) (y:S.Field d):Prop:=∃ (y':C.label d)(w:I→C.book.Token), S.project d y'=y ∧ S.classTokens ∘ w=v ∧ Dress (𝓛:Filter (ℕ×ℕ)) S k m j A A' w x d y'

variable {𝓛:Ultrafilter (ℕ×ℕ)}
include U
lemma stall_create [DecidableEq I] (B:ℝ)(k m j r' d:ℕ)(a:ℝ)(q:I→ℕ)(x:I→ Cover)(v:∀i,S.Field (q i)) (C' D:ℝ)
    (u:I→ℝ) (ht: ∀ i, Turnkey U 𝓛 a j r' (q i) B)(hp:Plot C k m j x) (he: ShortPrice C D C' u d q k m j) (hx:∀ i,C.S.a j^(q i)*B*Ascent.cost U (q i) a (v i) ≤ u i)(h𝓛:(𝓛:Filter (ℕ×ℕ))≤F.fuse): ∃ y,Stall (C:=C) 𝓛 S k m j C' D d x (fun i=>⟨q i,v i⟩) y :=by
   choose y z hy hv hw using fun i=>(ht i).coin (v i)
   let w':= fun i=>(⟨q i,y i⟩:C.book.Token); obtain ⟨K,hK⟩:= price_plot_M U (v:=w') he y (Y:=z) h𝓛 hv (fun _=>rfl) (fun i=> (hw i).mono fun n ht=>ht.1.trans (hx i)) hp
   exact ⟨_, K, w',rfl,funext fun i=> congr_arg (Sigma.mk (q i)) (hy i),hK⟩

-- `Y` uses cost bound measured at `a`, replaces even when listener separation can be finer than a!
variable (h𝓛:(𝓛:Filter (ℕ×ℕ))≤F.fuse) {r j m k':ℕ} {C' D':ℝ}
include h h𝓛
lemma stall_emit {s:ℝ}(v:I→ S.Tag) (d:J→ℕ) (y:S.Field t) (w:∀ j,S.Field (d j)) (hS: Stall (C:=C) 𝓛 S q m k A C' t x v y) (ht:Screen (C.S.gridPoint k ∘ x))(hk:b≤k)
     (hp: Apart (2*C.S.a l) Z')(hd:ApartFrom (2*C.S.a b) z0 Z') (hT:Injective (beside ((T') ∘ x) Z'))(he:Cards.Hall C.S b l q f n 1 (Fintype.card J)) (hh:∀i, Turnkey U 𝓛 s k' n (d i) D') (u:StateIndex U) :
       ‖peal U u ((assembly S (C.S.gridPoint k ∘ x) v-letter S 0 ⟨t,y⟩)*spendsWord (S:=S) Z' d w)‖ ≤ A* ∏ j,D'*Ascent.cost U (d j) s (w j) := by
   obtain ⟨y',w₀,rfl',ht₀,Q⟩:=hS; obtain ⟨l',f',hl',hl,h',⟨w₁,hT₀,Y₀,hP,hQ⟩,-⟩:=Q.wins
   choose X W hX hW hW' using fun i=> (hh i).coin (w i); let w':J→ C.book.Token:=fun i=> ⟨d i,X i⟩; let z:= spendsWord (S:=S) Z' d w; have hW'' : z=assembly S Z' (S.classTokens ∘ w'):= congr_arg (assembly S Z') (funext fun i=> Eq.symm (congr_arg (Sigma.mk (d i)) (hX i)))
   let a:= viewing U (beside (C.S.gridPoint k ∘ x) Z') (beside w₁ w')-viewing U (beside z0 Z') (beside (fun _ : Unit=> ⟨t,y'⟩) w')
   have hV: peal U u ((assembly S (C.S.gridPoint k ∘ x) v - letter S 0 ⟨t,y⟩)*z)=glance U u a:=by
      rw [sub_mul,map_sub,hW'', ← show S.classTokens ∘ w₁=v from hT₀.trans ht₀, ← rfl',peal_meter U u hT]
      have hG := hd.together (mul_nonneg zero_le_two (C.S.a_pos _|>.le)) (injective_of_subsingleton _) (hp.coin (mul_nonneg zero_le_two (C.S.a_pos _|>.le)))
      unfold a; rw [map_sub,← peal_slot U u hG]
   change ‖peal _ _ ((assembly _ _ _ - letter _ _ _) * z)‖ ≤ _; rw [hV]; refine (glance_bound U u a).trans ?_; exact stylus_clime (w:=w') U h W hP hk ht hp hd hT he (hl.trans h𝓛) h' hQ (fun i=> ((hW' i).mono fun n hn=> hn.2).filter_mono hl) (fun j=> (hW j).mono_left hl)
end YM.GapsContact.Seams
