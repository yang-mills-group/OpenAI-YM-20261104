import YM.RegulatorIR.Budget.TracePeriod

/-! Fixed-demand moment reserve pays loop closure failure, on the same
kernels projected for the equality. No new IR covariance prescription here. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Budget
open Set Function Tuple Deck Motion Spatial Layer Packet Copies Tariff
open scoped NNReal ENNReal Topology BigOperators Classical
variable {X Y:Type}{P l:ℝ} {r:ℕ} (A:Deck P X Y) (hp:0<P)(hl:0<l)

lemma pad_weight (u:ℕ) (z: Tuple X r) (p:X × X) :
    ((Premium.remnant P hp l hl u).uses A.atO).width (A.project z) ≤
       ((native l hl u).uses A.pos).diameter (linked z p)*amount l u (singular P (A.pos p.2)):=by
 let w:=linked z p
 let O:= (native l hl u).uses A.pos
 let B:= (Premium.remnant P hp l hl u).uses A.atO
 apply Premium.width_le
 · refine le_trans ?_ (mul_one (O.diameter w) ▸ mul_le_mul_right (amount_unit hl u (singular_nonneg ..)) (O.diameter w))
   apply (Tariff.diameter_le _ (O.diameter_unit w) fun i j=>?_)
   let I:= (onFold P hp l hl u).uses A.atO
   change I.road (A.orbit _) _ ≤ O.diameter w
   apply (A.cheap_d hp hl u ..).trans
   exact le_trans (O.diameter_ge z ..) (linked_diameter ..)
 intro i
 change amount l u (singular P (A.atO (A.orbit (z i))))≤ O.diameter w*_
 rw [A.s_tile hp]
 have he:=Premium.travel (Premium.remnant P hp l hl u) (A.pos (z i)) (A.pos p.2)
 apply he.trans
 rw [mul_comm]; apply mul_le_mul_left _ (amount l u (singular P (A.pos p.2)))
 have hv:= A.cheap_d hp hl u (z i) p.2
 change amount l u (distance P (A.atO (A.orbit (z i))) (A.atO (A.orbit p.2))) ≤ O.road _ _ at hv
 rw [A.d_tile _ hp] at hv
 have h:=O.diameter_ge (linked z p) i.succ.succ (0:Fin (r+1)).succ
 rw [link_here,link_second] at h
 exact hv.trans h

lemma length_trace (u b : ℕ)(z: Tuple X r)(p:X×X)(i: Fin r) :
 ((Premium.remnant P hp l hl u).uses A.atO).width (A.project z) * amount l b (singular P (A.pos (z i))) ≤
    ((native l hl (u+b)).uses A.pos).diameter (linked z p) * amount l (u+b) (singular P (A.pos p.2)):= by
 rw [diam_plus,amount_add,mul_mul_mul_comm]
 apply mul_le_mul' (pad_weight ..) _
 have hv := Premium.width_ge ((Premium.remnant P hp l hl b).uses A.atO) (A.project z) i
 have h:= hv.trans (pad_weight A hp hl b z p)
 change amount l b (singular P (A.atO (A.orbit (z i))))≤ _ at h
 rw [A.s_tile hp] at h; exact h
lemma tariff_center (x:Room)(u b:ℕ)(z:Tuple X r)(p:X×X) :
    ((Premium.rooted (onFold P hp l hl u) x).uses A.atO).width (A.project z) * amount l b (singular P x) ≤
     ((Premium.rooted (native l hl (u+b)) x).uses A.pos).width (linked z p) * amount l b (singular P (A.pos p.2)):= by
 let B:= (Premium.rooted (native l hl b) x).uses A.pos
 rw [width_plus,mul_assoc]
 apply mul_le_mul' ((A.cheap_mark hp hl ..).trans (linked_width ..))
 apply (Premium.travel (Premium.remnant P hp l hl b) x (A.pos p.2)).trans
 rw [mul_comm]
 apply mul_le_mul_left
 have h:=distance_le hp x (A.pos p.2) (across 0)
 rw [neutral_loc] at h
 apply (amount_mono hl b h).trans
 have H:= B.width_ge (linked z p) (0:Fin (r+1)).succ
 rw [link_second] at H; exact H
end YM.RegulatorIR.Budget
