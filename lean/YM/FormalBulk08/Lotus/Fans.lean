import YM.FormalBulk08.Lotus.Pan

noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Lotus
open Lava Gorge Lattice Laurent Filter Set Function
open scoped BigOperators Classical ENNReal Topology
variable {I : Type*} {r : ℕ} (i j : Fin r) (n : Side) (v : chain (Tor n I) r)

def ferryP (w : Picks i n (boil n (v i)) v) : Picks j n (boil n (v j)) v:=
   let b:= (boil n (v j)).1-(w.val j).1
   ⟨tint b ∘ w.val,by
       have he (a) : drip n (w.val a)= v a:=congr_fun w.property.2 a
       have hg : wrap n b=0 := by unfold b; rw [map_sub]; apply sub_eq_zero.mpr; exact (show (drip n _).1=(drip n _).1 from congr_arg Prod.fst ((drip_boil n _).trans (he j).symm))
       constructor
       · apply Prod.ext
         · simp [b]
         exact congr_arg (fun a: Tor n I=>a.2) (he j)
       funext k; rw [comp_apply,comp_apply,drip_tint,hg,he]; ext <;> simp⟩
lemma odyssee (w : Picks i n (boil n (v i)) v) : ferryP j i n v (ferryP i j n v w)=w := by
   let b:= (boil n (v j)).1-(w.val j).1
   apply Subtype.ext; change tint ((boil n _).1 - (tint b (w.val i)).1) ∘ (tint b ∘ w.val)=w.val
   funext k; apply Prod.ext <;> simp [w.property.1]
lemma cum_root (T : Tile (Biglot I) r) (h : Up T) : cum i n T v= cum j n T v:= by
   let e : Picks i n (boil n (v i)) v ≃ Picks j n (boil n (v j)) v:=⟨ferryP i j n v,ferryP j i n v,odyssee i j n v,fun w=>odyssee j i n v w⟩
   unfold cum vat; rw [←Equiv.tsum_eq e]; exact tsum_congr fun w=> (h _ _).symm

def swapP (s : Equiv.Perm (Fin r)) : Picks (s i) n (boil n (v (s i))) v ≃ Picks i n (boil n (v (s i))) (v ∘ s) where
   toFun w:= ⟨w.val ∘ s,w.property.1,funext fun k=> congr_fun w.property.2 (s k)⟩
   invFun w:= ⟨w.val ∘ s.symm,by constructor
                                 · change w.val (s.symm (s i))=_;rw [s.symm_apply_apply];exact w.property.1
                                 funext k; have he:=congr_fun w.property.2 (s.symm k);simp only [comp_apply,s.apply_symm_apply] at *; exact he⟩
   left_inv w:=Subtype.ext (funext fun k=>by simp)
   right_inv w:=Subtype.ext (funext fun k=>by simp)
lemma cum_agate (T : Tile (Biglot I) r) (h : Up T) (A : Agate T) : Agate (cum i n T) := by
   intro v s; rw [cum_root i (s i) n v T h]; unfold cum vat;
   simp only [comp_apply]; rw [←Equiv.tsum_eq (swapP i n v s)]; exact tsum_congr fun w=> A w.val s
lemma cum_charge {T : Tile (Biglot I) r} (h : Up T) {σ C : ℝ} (hs : 0≤σ) (H : Bail (fame I) σ T C) : Bail (lake n I) σ (cum i n T) C := by
   refine ⟨H.1,fun j a=>?_⟩
   let f (v : pack j a) (w:Picks j n (boil n a) v.val):= glitter (fame I) σ T w.val
   let g (v : (Σ v:pack j a,Picks j n (boil n a) v.val)) : pack j (boil n a):=⟨v.2.val,v.2.property.1⟩
   refine le_trans (b:= ∑' v:pack j a,∑' w, f v w) (ENNReal.tsum_le_tsum fun v=>?_) ?_
   · unfold glitter; rw [cum_root i j n _ T h, cum_near j n h _ (boil n a) (by rw [v.property,drip_boil])]; unfold vat; refine le_trans (mul_le_mul_right enorm_tsum_le_tsum_enorm _) ?_
     rw [← ENNReal.tsum_mul_left];refine ENNReal.tsum_le_tsum fun w=>?_; unfold f glitter; gcongr; apply shine_le _ hs; exact (congr_arg (wide (lake n I)) w.property.2.symm).le.trans (skirt_wide n _)
   rw [←ENNReal.tsum_sigma f]; refine H.watch g ?_
   rintro ⟨v,w⟩ ⟨u,z⟩ e; have he : w.val=z.val:= congr_arg Subtype.val e
   have hh:v=u:=Subtype.ext (w.property.2.symm.trans ((congr_arg (fun t=> drip n ∘ t) he).trans z.property.2));subst u;rw [Subtype.ext he]
end YM.FormalBulk08.Lotus
