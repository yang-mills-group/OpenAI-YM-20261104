import YM.FormalBulk08.Glide.Stunt

noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Glide
open Chapel Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Lotus Shore Mesa Gorge City Cork Rift Lava
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G : Gauge}{σ η A B C D : ℝ}{m r:ℕ}{L : Side}{I J : Type}
lemma jackets (S : Fin (m+1) → I→J→ℝ) (H:∀ i j,Summable fun v=> S i v j) (T:Tile I (m+1))(h:∀ v,‖T v‖ ≤ C)(v): prism S T v=∑' w:chain I m, (∑' y:I,T (Fin.cons y w)* S 0 y (v 0))* ∏ i, S (Fin.succ i) (w i) (v i.succ) := by
   let e : chain I m× I ≃ chain I (m+1):= (Equiv.prodComm (chain I m) I).trans (Fin.consEquiv (fun _: Fin (m+1)=>I)); let F(w):=T w*∏ i,S i (w i) (v i); have he: Summable (F ∘ e):= e.summable_iff.mpr (lenses v S H T h); unfold prism; rw [← Equiv.tsum_eq e (fun w=> T w*∏ i,S i (w i) (v i))]; change (∑' w,(F ∘ e) w)= _; rw [he.tsum_prod]
   refine tsum_congr fun w=> ?_; rw [←tsum_mul_right]; refine tsum_congr fun y=>?_ ; change T _*(∏ i,S i ((Fin.cons y w : chain I (m+1)) i) (v i))= _; rw [Fin.prod_univ_succ]; simp only [Fin.cons_zero,Fin.cons_succ]; exact (mul_assoc ..).symm
lemma rotate_prism (S: Fin m→ I→J→ℝ)(T: Tile I m)(v)(s: Equiv.Perm (Fin m))(h:Agate T): prism S T v = prism (S∘s) T (v∘s) := by
   let e:=Equiv.arrowCongr s.symm (Equiv.refl I);unfold prism;rw [← Equiv.tsum_eq e (fun w=> T w*∏ i,(S ∘ s) i (w i) ((v ∘ s) i))]; refine tsum_congr fun w=>?_ ;change _ = T (w∘s)*_; rw [h w s]; congr 1; symm; exact Fintype.prod_equiv s _ _ fun i=>rfl
variable {S: Cross L (colorsL G) I}{U:Cross L (spots G) I}{T:Tile (edgeL G) (m+1)}(h:trench S U)(p:0≤σ)(q:0≤η)(hp:Bail (fame _) σ T B)(hq:Bail (fame _) σ (tap T) D)(hw:S.strip η C)(ha:U.strip η C)(hc:0≤C) [Fintype I]
include h p q hp hq hw ha hc
lemma prism_trench (M: Fin (m+1)→Cross L (colorsL G) I)(ht:∀ i, (M i).strip η C) :
   prism (fun i=>merit (update M 0 S i)) T= -prism (fun i=> merit (update M 0 (proxy U) i)) (tap T) := by
   let Z (S:Cross L (colorsL G) I) (v) := merit (update M 0 S v); have he v a (V:Cross L (colorsL G) I) (H:V.strip η C): Summable fun x=> Z V v x a:= center_row _ (by by_cases hx:v=0 <;> simp [hx,ht,H]) q hc a
   ext v; change prism (Z S) T v= -prism (Z (proxy U)) (tap T) v; rw [jackets (Z S) (fun i j=>he i j S hw) T (fun v=>hp.value p v 0), jackets (Z (proxy U)) (fun i j=>he i j _ (proxy_pay ha hc)) _ (fun v=>hq.value p v 0),←tsum_neg]; unfold Z; simp_rw [update_self, update_of_ne (Fin.succ_ne_zero _), trench_tally h p q hp hq hw ha hc, neg_mul]
-- actually cost independent of B
lemma prism_tap (M: Fin (m+1)→Cross L (colorsL G) I)(ht:∀ i,(M i).strip η C)(H:Agate T)(a : Fin (m+1))(hy:η ≤ L.val * σ):
   Bail (fame _) η (prism (fun i=> merit (update M a S i)) T) (Real.exp (8*η)*D*(Fintype.card (Co L (colorsL G))*(Fintype.card I:ℝ)^m)*C^(m+1)):=by
    let s:= Equiv.swap (0:Fin (m+1)) a
    let G1:= prism (fun i=> merit (update (M∘s) 0 S i)) T
    have he (v: Fin (m+1)): update M a S (s v)= update (M∘s) 0 S v:= by
       by_cases hx:v=0
       · simp [s,hx]
       rw [update_of_ne (show s v≠a from fun k=> hx (s.injective (k.trans (Equiv.swap_apply_left ..).symm))),update_of_ne hx];rfl
    rw [show prism (fun i=> merit (update M a S i)) T=(fun v => G1 (v ∘ s)) from (by ext v; rw [rotate_prism _ T v s H];unfold G1;rw [show ((fun i=> merit (update M a S i)) ∘ s)=_ from funext fun v=> by rw [comp_apply, he]])]
    apply Bail.spins (T:=G1) _ s; unfold G1; rw [prism_trench h p q hp hq hw ha hc (M∘s) (fun i=>ht _)]
    have hu (i:Fin (m+1)):Row.strip (update (M∘s) 0 (proxy U) i) η C:= by by_cases hi:i=0 <;> simp [hi,proxy_pay ha hc,ht]
    exact (sides q hy _ _ _ hu (fun _=>hc) (pow_nonneg hc (m+1)) (by simp) _ hq).neg -- dot Nat subtraction
end YM.FormalBulk08.Glide
