import YM.X.Sage.Twice
/-!
# Beacon.Bus: ψ∆ single alignment. explicit room determinant. 𝔓∧ lower easing.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Sage
open Lattice Wilson Next.Rank Normal LiftMark PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Shelf Tot
open Filter Function Reed Ocean Hinge Haze Fielding Print Tri Plate Gravity Chir Fund
open Stems hiding X
open MvPolynomial Set
open scoped Topology BigOperators Classical
variable {G:Gauge} {d k:ℕ} {V I:Type*} {q:ℕ+}{r s t:ℝ}
local notation "U"=> G.ColorIndex
local notation "P"=> Curly G
local notation "T"=>Tet
local notation "o"=> side q k
local notation "ℓ"=> Hair G→₀ℂ
local notation "ε"=>epsilon q k
local notation "Q"=> qu q G k
local notation "E"=>tri Q
local notation "δ"=> edge Q
variable (B:Beacon q G r)
variable (A:Foam G)(X Y Z:Fielding.Walk)(ι μ:Axis)(u v p:Tet)(x y: Cover)(a b:G.ColorIndex)
local notation "kI"=> wrap o
lemma hpick(r':ℝ): δ (psiF q k x r' p a) (veil y k B.seed) =∑ i:T, Complex.ofReal (Wpp ε r i r' p o (kI y) (kI x)) • veil y k (B.shade i a) := by
   rw [B.ridge]; apply Finset.sum_congr rfl; intro i _; simp_rw [treats_comm (x:=psiF q k x r' p a),ψ_meetPP]; simp only [ite_smul,zero_smul,Finset.sum_ite_eq', Finset.mem_univ, if_true] -- orientation
lemma pickA : δ (psiA q k x ι a) (veil y k B.seed)= ∑ i:T, Complex.ofReal (Wpv ε r i ι o (kI y) (kI x)) • veil y k (B.shade i a):= by
    rw [B.ridge]; apply Finset.sum_congr rfl; intro i _; simp_rw [treats_comm (x:=psiA q k x ι a),ψ_meetPV]; simp [ite_smul]
variable (C:Beacon q G s) (r' :ℝ)
local notation "Tτ"=> Imprint.transit q
local notation "K"=> Weave q
abbrev View (q:ℕ+)(Y:Fielding.Walk)(s:ℝ)(p:T)(i:Axis): Weave q:= wef q Y 1 (transfer s p i)
abbrev Wheel (q:ℕ+)(X:Fielding.Walk)(p:T)(r:ℝ)(v:T): Weave q:=wef q X 2 (exchangeF r p (-1) v)
local notation "P₀"=> B.seed
local notation "Gτ"=> Tot.gather q X Y Z
lemma wp_view(w:Cover): View q Y r' p ι k (wrap o w)= ↑(Wpv ε r' p ι o (Tτ Y k) (kI w)):= rfl
lemma wh_view (w:Cover): Wheel q Y p r' v k (wrap o w) = ↑(Wpp ε r' p (-1) v o (Tτ Y k) (kI w)):= rfl
lemma gather_at : gather q X Y Z A B.seed C.seed k= tri Q (veil (X k) k A) (veil (Y k) k B.seed) (veil (Z k) k C.seed):= rfl
def staple : Weave q:= ∑ u:T,∑ v:T,View q Y r u ι * View q Z s v μ * ensign q (Gτ A (B.shade u a) (C.shade v b)) -- implicit args order annoying
local notation "stape"=> fun x i y j=> staple B A X Y Z x y i j C
set_option maxHeartbeats 480000 in
lemma accurst (w:Cover): staple B A X Y Z ι μ a b C k (wrap o w)= XEdge q k (psiA q k w ι a) (psiA q k w μ b) (veil (X k) k A) (veil (Y k) k B.seed) (veil (Z k) k C.seed):= by
   unfold XEdge; rw [pickA,pickA]; simp_rw [tri_sum₁,tri_sum₂,tri_scale₁, tri_scale₂,staple,Finset.sum_apply, Pi.mul_apply,wp_view, smul_eq_mul, mul_assoc]; rfl
def Lapiz {t:ℝ} : Weave q:= ∑ i:Ticket G, toll t p a i • ((stape) i.1.val.1 i.2.1 i.1.val.2 i.2.2 +(stape) i.1.val.2 i.2.2 i.1.val.1 i.2.1)
-- t omitted if implicit unbound; check output
lemma accounted (w:Cover): Lapiz (t:=t) B A X Y Z p a C k (wrap o w)= skirt q k t w p a (veil (X k) k A) (veil (Y k) k B.seed) (veil (Z k) k C.seed):= by
   unfold Lapiz skirt XBridge; simp only [Finset.sum_apply,Pi.smul_apply,Pi.add_apply,accurst];rfl
lemma groundC : readAt q X (Lapiz (t:=t) B A X Y Z p a C) = spotK (q:=q) X Y Z B.seed C.seed t A p a:= funext (fun k=> accounted ..)
lemma lofty (z:Site (side q k)): skirt q k t (lift z) p a (veil (X k) k A) (veil (Y k) k B.seed) (veil (Z k) k C.seed)= Lapiz (t:=t) B A X Y Z p a C k z:= (accounted (t:=t) B A X Y Z p a C (lift z)).symm.trans (congr_arg _ (wrap_lift ..))
end YM.PositionX.Sage
