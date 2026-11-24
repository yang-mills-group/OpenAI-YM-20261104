import YM.MS.Garment.Irrigate
/-!
# Sight on plow etc. Package the properties of interaction Phi.

Yuan. Does not forget stencil multiplicity or color; rank-zero part allowed throughout.
 Other operations on Hmaster of ghost excitation one may use one step versions later. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Garment
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps
open Momentum Metric
open scoped Topology ContDiff
variable {G:Gauge}{b c d:Bool}{m n:ℕ}{U:Rip G}{F H:Mob G}
variable (hs:Sight F)
lemma luminous (a:ℂ)(t:ℝ)(ha:star a=a): star ( amount a t)=amount a t:= by simp [amount,← Complex.exp_conj, show starRingEnd ℂ a=a from ha] -- wait
include hs
lemma glance (a:ℂ)(s:ℝ)(ha:star a=a): Sight (plow a s F) := by
   intro m l; have hx (l:Legs (Shore G m)): mass (invertMom l)=mass l:= by induction l with| nil=>rfl| cons i l ih=> unfold invertMom at *; rw [List.map_cons,Price_cons,Price_cons (i:=i),ih]
   unfold plow; rw [hx, show sr s (invertMom l)=invertMom (sr s l) from ?_, hs m,star_mul',luminous _ s]; simp_all; unfold sr invertMom; rw [List.map_map,List.map_map]; simp [Function.comp_def]
omit hs
lemma starch (b c:Bool): star (cross b c:ℂ)=cross b c:=by cases b <;> cases c <;> simp
lemma degree_inv (l:Legs (Shore G m)): degree (field Landau.parity) (invertMom l)=degree (field Landau.parity) l:= by induction l with|nil=>rfl| cons i l ih=> unfold invertMom at *; rw [List.map_cons,degree_cons,ih,degree_cons]
-- conjugating scatter: already lemma copy any
lemma aqua (l:Legs (Shore G m))(F:Shared (Shore G m) ℂ): scatter (field Landau.parity) (invertMom l) F=star (scatter (field Landau.parity) l (fun a b=>star (F (invertMom a) (invertMom b)))):= by
   induction l generalizing F with
   | nil=> simp [invertMom]
   | cons i l ih=> rw [show invertMom (i::l)=(i.1,-i.2)::invertMom l from rfl,scatter_cons,ih,scatter_cons]; congr! 2; funext; simp only [star_add,star_mul',starch,degree_inv]; rfl
include hs
lemma spotlight (hH:Sight H)(hv:veil U)(hr:reverseF U): Sight (arbor U F H):= by
   intro n l; unfold arbor tree; rw [aqua]; apply congr_arg; apply scatter_congr; intro a b he; rw [convertR (hr n),convertR (hr n)]; simp_rw [star_sum]; refine Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=>?_ ; unfold radius; dsimp only; -- see
   rw [net_invert,degree_inv,hv n i j (-net a),show F n ((i,- -net a)::invertMom a)=_ from hs n ((i,-net a)::a), show H n ((j,- - -net a)::invertMom b)=_ from hH n ((j,- -net a)::b)]; simp only [star_mul',starch,star_star, star_ofNat]
end YM.MS.Garment
