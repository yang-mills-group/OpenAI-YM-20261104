import YM.X.Tot.Transport
/-!
# exposure bill. Single hole relocation exact. Cluster cost in occupied.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Tot
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter Set MeasureTheory Asymptotics
open PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Reed Shelf
open Stems hiding X
open Ocean Haze Fielding Print Fund Tri Plate LiftMark Hinge Bare Pulse Labels Pert.RawLabels Crystal Gravity
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} {F: Labels.Frames G} {d k m l:ℕ} {V W I:Type*} {r R:ℝ} {n:Side}
variable (q:ℕ+)(χ:Floor R)
local notation "μ"=> flow G n
local notation "o"=> side q k
local notation "Q"=> qu q G
local notation "ε"=>epsilon q k
variable (x y z:Fielding.Walk)(A B C:Foam G)
lemma maj_vol (z:Site (side q k))(A B C:Curly G): volS q k * majority (Q k) (EngineP q G k z) A B C=majority (Q k) (dress (lift z) (Tot.pillar G)) A B C:= by unfold majority; rw [← shape_jump q z,mscale,tri_scale]; rfl
lemma maj_realign (x y z:Cover)(e:Site n)(ht:wrap n y=wrap n x+e)(hy:wrap n z=e)(A B C U:Curly G): majority μ (dress y U) A B C = majority μ (dress x (dress z U)) A B C:= by
    rw [pay_sym (0:Site n) A B C, pay_sym (0:Site n) A B C (dress x _)]; rw [dress_addT,tint,tint,map_add,ht,hy]
local notation "L"=> cloak q x A
local notation "M"=> cloak q y B
local notation "T"=> cloak q z C
set_option maxHeartbeats 400000 in
lemma maj_at  : mantle q (bend q χ x) (cloak q x A) (cloak q y B) (cloak q z C) (EngineP q G) k=∑ a:Site o, bend q χ x k (a+wrap o (x k)) * tri (Q k) (dress (x k) (multi (Q k) (A k) (dress (lift a) (Tot.pillar G)))) (Lift y B k) (Lift z C k):= by
    unfold mantle crow; conv_lhs=> rw [← Equiv.sum_comp (Equiv.addRight (wrap o (x k)))];
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; let w:=i+wrap o (x k); change volS q k*(bend q χ x k w*majority _ _ (L k w) (M k w) (T k w)) = _; rw [mul_left_comm (volS q k)]; rw [maj_vol]; apply congr_arg (bend q χ x k w * ·); rw [multi_rot]; exact maj_realign (x k) (lift w) (lift i) i ((wrap_lift _).trans (add_comm ..)) (wrap_lift i) (dress (x k) (A k)) _ _ (Tot.pillar G) -- parameter order
lemma settlement (h:∀ z∈(Floor.maskL q χ k).support, lift (wrap (side q k) z)=z) : mantle q (bend q χ x) L M T (EngineP q G) k= tri (Q k) (dress (x k) (multi (Q k) (A k) (mask q χ k))) (Lift y B k) (Lift z C k):= by
   rw [maj_at q χ x y z A B C, bead_cast q χ h, show multi (Q k) (A k) _ =(toned (Q k) (A k)) _ from rfl,map_sum,map_sum,tri_sum]; apply Finset.sum_congr rfl; intro i _; rw [map_smul,map_smul,tri_scale]; unfold bend; rw [add_sub_cancel_right];rfl
lemma mantle_subL (f g:Weave q)(Z:Billboard G q): mantle q (f-g) L M T Z= mantle q f L M T Z- mantle q g L M T Z:= by unfold mantle; rw [sub_mul, crowd_sub]
lemma absorb (h:∀ z∈(Floor.maskL q χ k).support, lift (wrap (side q k) z)=z) :
    let p:= Q k; let U:= mask (G:=G) q χ k; Tot.bill q x y z χ (cloak q x A) (cloak q y B) (cloak q z C) (EngineP q G) k = (crow q (fun i v=> space (Q i) (Lift x A i) (Lift y B i) (Lift z C i) (EngineP q G i v))) k - (tri p (dress (x k) (multi p (A k) U)) (Lift y B k) (Lift z C k)+ tri p (dress (y k) (multi p (B k) U)) (Lift z C k) (Lift x A k) + tri p (dress (z k) (multi p (C k) U)) (Lift x A k) (Lift y B k) ) := by
    intro p U; unfold Tot.bill deckQ; rw [relev]; simp only [mantle_subL,Pi.add_apply,Pi.sub_apply,settlement (G:=G) q χ _ _ _ _ _ _ h]; rw [maj_swap (A:=M) (B:=L)]; unfold Lift U p; simp_rw [cape_val]; abel
end YM.PositionX.Tot
