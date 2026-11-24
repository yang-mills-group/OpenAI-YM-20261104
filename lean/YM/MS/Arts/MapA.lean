import YangMills.WilsonProof.NativeSupport.YM.MS.Arts.Range
/-!
# Prefix embeddings, leg warp. Rotation tensor transforms through prefix.

Uses numerical pref m exactly. Auxiliary ext wrap; Pen BP signs appear on Leg. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Arts
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux
open Momentum Landau Pilot
open scoped Topology ContDiff InnerProductSpace
variable {G:Gauge}{A B C P:Type}[Fintype A][Fintype B][Fintype C]
 [DecidableEq A][DecidableEq B][DecidableEq C]{b:Bool}{m n k:ℕ}
variable (h:m≤n)
omit [Fintype A][Fintype B][Fintype C][DecidableEq A][DecidableEq B][DecidableEq C] in
lemma risesP (f:A ↪ B)(i:Leg A C): Landau.parity (embA f i)=Landau.parity i:= by rcases i with ⟨⟨_|a,_|_⟩,t⟩ <;> rfl
lemma lifts_net (i:Legs (Shore G m)): net (lift h i)= Left h (net i):= by induction i with| nil=>simp [net,lift]| cons a l ih=> simpa only [lift, List.map_cons,net_cons,map_add, Prod.map_apply'] using congr_arg (Left h a.2 + ·) ih -- unification prod
lemma lifts_link (hp:n≤k)(i:Legs (Shore G m)): lift hp (lift h i)=lift (Nat.le_trans h hp) i:= by
    unfold lift; rw [List.map_map]; induction i with
    | nil=>rfl
    | cons i l ih=>
        simp only [List.map_cons,Prod.map_apply',Function.comp_apply, ih]; congr 2; · rcases i with ⟨⟨⟨_|a,p⟩,c⟩,i⟩ <;> rfl
        exact (sons (rises h) (rises hp) i.2).trans (by rw [rides_link])
lemma lifts_id (i:Legs (Shore G m)): lift (Nat.le_refl m) i=i:= by
   unfold lift; induction i with
   | nil=>rfl
   | cons a l ih=>
        rw [List.map_cons, ih]; congr 1; apply Prod.ext; · rcases a with ⟨⟨⟨_|i,x⟩,q⟩,v⟩ <;> rfl
        exact funext fun v=> by exact lasts (rises (Nat.le_refl m)) a.2 v
lemma lifts_degree (i:Legs (Shore G m)): degree (field Landau.parity) (lift h i)=degree (field Landau.parity) i:= by induction i with| nil=>rfl|cons a l ih=> rw [degree_cons,show lift h (a::l)=(embA (rises h) a.1,Left h a.2)::lift h l from rfl,degree_cons, ih]; unfold field; rw [risesP]

namespace Spin
-- arch transforms leg through prefix
lemma ray_taller (X:Spin (L m))(i j:L m): (X.arch h).profile (rises h i) (rises h j)= X.profile i j:= by unfold profile; rw [← send_spray, X.arch_on h,lasts]
lemma ray_away (X:Spin (L m))(i:L m)(j: Apart m n): (X.arch h).profile (rises h i) (aside h j)=0:= by unfold profile; rw [← send_spray,X.arch_on h]; exact offt _ _ _ fun i=>nowhere h i j
-- evaluate on full transform list & restrict
lemma telescopeS (X:Spin (L m))(v:Rack G n)(x): (flagS (X.arch h) G).beam v (lift h x)= (flagS X G).beam (fun i=>v (lift h i)) x:= by
    induction x generalizing v with
    | nil=> simp [lift]
    | cons a x ih=>
        let Y:= X.arch h; let W:= flagS Y G; rcases a with ⟨⟨⟨_|a,s⟩,c⟩,p⟩
        · change (leggo G.ColorIndex Y).beam v ((( (none,s),c),Left h p)::lift h x)=(leggo G.ColorIndex X).beam _ ((( (none,s),c),p)::x); rw [fromG,fromG, show Y.turn _= _ from X.arch_on h p]; exact ih _ 
        change (leggo G.ColorIndex Y).beam v ((((some (rises h a),s),c),Left h p)::lift h x)=(leggo G.ColorIndex X).beam _ ((((some a,s),c),p)::x); rw [fromV,fromV, cut_sum h, show Y.turn _= _ from X.arch_on h p]; simp only [Y, ray_taller,ray_away,Complex.ofReal_zero,zero_mul,Finset.sum_const_zero,add_zero]; apply Finset.sum_congr rfl; intro i hi; congr 1; exact ih _
end Spin
end YM.MS.Arts
