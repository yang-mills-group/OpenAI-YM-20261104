import YM.MS.Arts.GridPop
/-!
# Stable Ward operator extends dimension actions

Hypotheses spin and actual symbol tie. Costmerom later. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Arts
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux
open Momentum Landau Pilot Spin
open scoped Topology ContDiff
variable {G:Gauge}{I:Type}{m n k:ℕ}{b c:Bool}{F H:Mob G}{U:Rip G}
variable (h:m≤n)
abbrev Shade (G:Gauge):= ∀ m:ℕ,Charge (Landau.parity (A:=L m) (C:=G.ColorIndex)) (SectorP m) ℂ
structure CountsD (b:Bool)(K: Shade G): Prop where
   spin m (X: Spin (L m)): within b X → Counts (flagS X G) (K m) (K m)
   wall {m n:ℕ}(h:m≤n)(a b p): (K n).table (embA (rises h) a) (embA (rises h) b) (Left h p)=(K m).table a b p

lemma roof_v (L:Slash (Cfield G n) (SectorP n) ℂ)(l:Legs (Shore G m)): Plane.visit c Landau.parity (lift h l) L=Plane.visit c Landau.parity l (fun l i r=>L (lift h l) (embA (rises h) i.1,Left h i.2) (lift h r)) := by
    induction l generalizing L with| nil=>rfl | cons i l ih=> rw [visit_cons,show lift h (i::l)= (embA (rises h) i.1,Left h i.2)::lift h l from rfl,visit_cons,ih]; dsimp only; rw [risesP]; rfl
variable {K:Shade G}
def portZ (K:Shade G)(F:Mob G) : Mob G:= fun m=>(K m).raise (F m)
variable (HE:Sturdy b F)(HK:CountsD b K)
include HE HK
lemma hike_up (l: Legs (Shore G m)) : portZ K F n (lift h l)=portZ K F m l:= by
    unfold portZ; simp_rw [visit_Z]; rw [roof_v]; apply visit_agree; intro l i r ht; rw [more h];
    have hp (j:Apart m n)(b)(c): F n (lift h l ++ (vleg b (aside h j) c,Left h i.2)::lift h r) =0:= vanish_one h HE l r j i.2 c b
    dsimp only; simp_rw [hp,mul_zero, Finset.sum_const_zero,add_zero]; apply Finset.sum_congr rfl; intro p _; rw [HK.wall]; congr 1; convert HE.grows h (l++(p,i.2)::r) using 2; simp only [lift,List.map_append,List.map_cons]; rfl
lemma zMotion : Sturdy b (portZ K F):= ⟨fun n X hp=> by rw [portZ,(HK.spin n X hp).walk,HE.turn n X hp], fun h=> hike_up h HE HK⟩
end YM.MS.Arts
