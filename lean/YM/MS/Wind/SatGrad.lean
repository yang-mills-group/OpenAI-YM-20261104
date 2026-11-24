import YM.MS.Wind.PDE
/-!
# Initial anomaly and PDE at all times

Apply the derived identities to the assembled master indicator.
 Descend through ranks afterward to recover Ward. This is a theorem in the
 momentum presentations, unrestricted even at kernel-only variable t (all ℝ).
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Wind
open Function Filter Set Finset Plane Koszul Flux MeasureTheory
open Landau Native Lattice Tone Momentum Heat Real Frame Wire Color Detect Native.Wilsonian Paint
open Book Convolve City Logarithm Program Signal Modeled
open Complex (I)
open scoped Topology ContDiff
variable {G: Gauge}{p:Team}{φ: Actor G}{F H: Dec G}{u:ℤ} {k:ℕ}{l:List (Lane4 G)}
variable (x:ℝ)
local notation "ξ" => Ω G
local notation "pb"=> (2:ℂ)⁻¹
def mat (F:Dec G)(x t:ℝ):= (Ω G t).matCont (payR F x t)
def res (F H:Dec G)(x t:ℝ):= (Ω G t).res (payR F x t) (payR H x t)

lemma born_int (a b: BH G)(p:QP): Mood G 0 a b p= Kzone G a b p:= by simp only [Mood,LegsX,Landau.choir,χ0,Kzone] -- Kzone def
lemma r0 (h:PC G p F)(H':G.Simple)(hl : net l=0)(i:ℕ): mat F x 0 i l=0:= by
   cases i with
   | zero=> unfold mat GridR.matCont; simp only [Pi.add_apply,promised,Pi.smul_apply,paired,centered h x 0,map_zero,Pi.zero_apply,Finset.Nat.antidiagonal_zero,Finset.sum_singleton]; simp -- maybe extra
   | succ n=>
       let K:=(payR F x 0); -- shadows!
       let S:=style G p x; let q:=promote run S; let v:=n+1; let he:=plane_core (G:=G) p x H' l hl (k:=v) (by unfold v; omega)
       have hv i (hi:1 ≤ i): payR F x 0 i= q i:= (h.recu i hi x).1;
       have hZ x' y' : Mood G 0 x' y'= Kzone G x' y':= funext fun u=>born_int ..; have h' : Mood G 0= Kzone G:= funext fun i=> funext (hZ i)
       unfold mat GridR.matCont; rw [Pi.add_apply,promised, Pi.smul_apply];
       have hm : pairW (ξ 0).C (payR F x 0) (payR F x 0) v=∑ j∈Domain.paths v 1, (ξ 0).C (q (v-j)) (q j):= by rw [paired,canon_corner (fun s t=>(ξ 0).C (payR F x 0 s) (payR F x 0 t)) _ (by unfold v; omega),centered h,map_zero,map_zero,LinearMap.zero_apply,zero_add,zero_add]; apply Finset.sum_congr rfl; intro i hi; obtain ⟨ha,hh⟩:=path_in hi; rw [hv i ha,hv (v-i) (by omega)]
       change ((ξ 0).J (payR F x 0 v)+pb • (pairW (ξ 0).C (payR F x 0) (payR F x 0) v)) l=0; rw [hm]; have hb:= period0 μzone cour0 (mood_f G) (t:=0) ((h.owes v).stay x).joint; change Pass (Mood G 0) (payR F x 0 v) μzone at hb; rw [hv v (by unfold v; omega)] at hb ⊢
       simp only [Ω,rack,LinearMap.add_apply, Pi.add_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul, blvd]; rw [finite_cc μzone hb]; simp_rw [h']; dsimp only at he; rw [one_div] at he; exact he
lemma initialS (h:PC G p F)(hx:PM φ F H u)(hm: Circle G φ false u)(he:Weightless (Spectrum G) (style G p x) (φ x))(i:ℕ): res F H x 0 i= 0:= by
   let X : ℝ→T (Law G):=payR F x; let B := φ x; let U:= style G p x; let D:=promote run U; let Z:=promote run B; have hy j : payR H x 0 j=Z j:= (hx.recu ..).1
   have ht j (hi:1 ≤ j): X 0 j=D j:= (h.recu j hi x).1
   let C:=(ξ 0).C; have hh : pairW C (X 0) (payR H x 0) i= ∑ j∈Domain.paths i 0,C (D (i-j)) (Z j):= by rw [paired,canon_sub (fun i j=>C (X 0 i) (payR H x 0 j)),show X 0 0=0 from centered h x 0,map_zero,LinearMap.zero_apply,zero_add]; exact Finset.sum_congr rfl (fun j hj=> by rw [hy,ht _ (by obtain ⟨a,b⟩:=path_in hj; omega)])
   ext l; have Hk:= plane_mark (k:=i) p x B he (fun i=>hm.actual i x) l; unfold res GridR.res; rw [Pi.add_apply, show pairW _ _ _ i= _ from hh]; -- see
   have hp:= period0 μzone cour0 (mood_f G) (t:=0) ((hx.owes i).stay x).joint; change Pass (Mood G 0) (payR H x 0 i) μzone at hp; rw [hy] at hp; rw [promised,hy]
   simp only [C,Ω,rack,LinearMap.add_apply,Pi.add_apply,Finset.sum_apply,blvd,finite_cc μzone hp]; rw [show Mood G 0=Kzone G from funext fun i=>funext fun j=>funext (born_int i j)]; exact Hk
end YM.MS.Wind
