import YM.X.Sage.Fusion
/-! # departures from classical marks sending double => vanishes exact or at limit. mask independent. -/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Sage
open Lattice Wilson Next.Rank Normal LiftMark PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Shelf Tot
open Filter Function Reed Ocean Hinge Haze Fielding Print Tri Plate Gravity Chir Fund
open Stems hiding X
open MvPolynomial Set
open scoped Topology BigOperators Classical
variable {G:Gauge} {d k:ℕ} {V I:Type*} {q:ℕ+}{r s r₁:ℝ}
local notation "U"=> G.ColorIndex
local notation "P"=> Curly G
local notation "Ω"=> Foam G
local notation "T"=> Tet
local notation "L"=>(atTop:Filter ℕ)
local notation "Θ"=> Reed.Horizontal G
local notation "ℓ"=> Hair G→₀ℂ
local notation "o"=> side q k
local notation "Q"=> qu q G k
local notation "W"=>μDeck q G
variable (x y z: Fielding.Walk)(A B C:Foam G)(p v:Tet)(a:G.ColorIndex)
lemma vanishY (A C:Curly G)(x y:Cover): twiceC q k r x p a A (veil y k W) C=0:= by
    unfold twiceC; apply Finset.sum_eq_zero; rintro ⟨u,i,j⟩ _; by_cases h:i=j; · rw [sleepy p a _ h,zero_mul] -- order
    apply mul_eq_zero_of_right; unfold Corner; rw [veils,snapμ]; simp_rw [map_sum];
    have he : ∀ (t:T)(s:U), edge Q (psiA q k x u.val.2 j) (edge Q (psiA q k x u.val.1 i) (glyph (psiF q k y (-1) t s)*glyph (psiF q k y (-1) t s)))=0:= by
        intro t s; apply bandit; rw [treats_comm (x:=psiA ..),treats_comm (x:=psiA ..),ψ_meetPV,ψ_meetPV]; by_cases ht:s=i; right; rw [if_neg (ht ▸ h)]; left; rw [if_neg ht]
    unfold suba subb; simp_rw [he,Finset.sum_const_zero, tri_z₁] -- simp
local notation "gτ"=> gather q x y z
local notation "G₀"=>restU q p a
lemma twice_g (i:Tops G)(j:Tops G): (fun k=> Corner q k (Vane q i k (x k)) (Vane q j k (x k)) (veil (x k) k A) (veil (y k) k B) (veil (z k) k C))= gather q x y z A (poke q x y j (poke q x y i B)) C:= by ext1 k; unfold Corner; simp_rw [←dressed];rfl
variable (h:Geom q r x y z)(hr:0<r) (hq:1<q.val)
local notation "K"=>terminals G (-1)
local notation "D"=>fades ℂ
include h hr hq
lemma proctor (F:Foam G)(H:F∈single q 1 K)(H':B∈single q 3 (Set.univ (α:=Marks G)))(hv:C∈single q 2 K)(x':Tops G)(y':Tops G): (fun k=> Corner q k (Vane q x' k (x k)) (Vane q y' k (x k)) (veil (x k) k F) (veil (y k) k B) (veil (z k) k C))∈ D:= by
      rw [twice_g, gather_s]; let U₀:= Set.univ (α:=Marks G); have hh:=h.1.sym q x y; have hp : poke q x y y' (poke q x y x' B) ∈ single q 1 U₀:= awakes x y y' _ hq hh hr.le (awakes x y x' B hq hh hr.le H' (m:=2) rfl) rfl; let hy:Geom q r y x z:=(h.circles q ..).swap q ..; exact Tot.lack _ _ _ _ _ _ _ _ (illA _ _ hp hq hr) H hv (d:=1) (Page.duty' hp (by simp)) (by simp) hy hr hq (same_wire hy.2.1 hr.le hq)
lemma proctB : (fun k=> twiceC q k r₁ (x k) v a (veil (x k) k (restU q p a)) (veil (y k) k (βDeck q G)) (veil (z k) k W))∈ D:= by
     let f(u:Ticket G)(k:ℕ):= Corner q k (suba q k (x k) u) (subb q k (x k) u) (veil (x k) k (restU q p a)) (veil (y k) k (βDeck q G)) (veil (z k) k W); change (fun k=>∑ u:Ticket G,toll r₁ v a u*f u k)∈ _; rw [show (fun k=> ∑ u: Ticket G, _)= (∑ u:Ticket G,toll r₁ v a u • f u) from (by ext1;simp [Finset.sum_apply])]; apply Submodule.sum_mem; intro i _;
     refine Submodule.smul_mem _ _ (proctor x y z _ _ h hr hq (restU q p a) ?_ ?_ degreeU (columnA _ _) (columnA _ _)); exact Submodule.smul_mem _ _ (degreeΦ p a); exact home_close q _ (Set.Subset.refl _) (subset_univ _) degreeB
omit h hr hq
variable (c: Beacon q G s)
def spotK (s':ℝ)(X:Foam G)(p:T)(a:U):ℕ→ℂ:= fun k=> skirt q k s' (x k) p a (veil (x k) k X) (veil (y k) k B) (veil (z k) k C) -- implicit q from notation? q used via k only.Manage variable `(q)`.
def ripple : ℕ→ℂ:= ∑ p:T,∑ v:U, spotK (q:=q) x y z B C s (c.shade p v) p v
lemma β_exit : gather q x y z (βLift q G) W W=ripple x y z W W (BMark q G):= by ext1 k; unfold ripple Tot.gather spotK; rw [B_offer0]; change tri _ (veil _ _ _) (veil _ _ _) (veil _ _ _) = _; simp_rw [map_sum,map_mul,tri_sum,birth,vanishY]; simp only [add_zero,Finset.sum_apply]; rfl
include h hq hr
lemma μ_exit : CostF (gather q x y z (μLift q G) (βDeck q G) W) (ripple x y z (βDeck q G) W (Umark q G)):= by
    let f(i:T)(a:U)(k:ℕ):= twiceC q k (-1) (x k) i a (veil (x k) k (restU q i a)) (veil (y k) k (βDeck q G)) (veil (z k) k W); let t:=∑ i:T,∑ a:U,f i a; unfold CostF; rw [show _-_=t from ?_]; swap; · ext1 k; rw [← U_offer]; unfold Tot.gather Offer ripple spotK; change tri _ (veil _ _ _) (veil _ _ _) (veil _ _ _) - _ = _; unfold t; simp_rw [map_sum,map_mul,tri_sum,birth,vanishY]; unfold Umark; simp [Finset.sum_apply, Finset.sum_add_distrib,f];
    exact (D).sum_mem fun i _=> (D).sum_mem fun j _=> proctB x y z i i j h hr hq
omit h hq hr
lemma ripple_swap : ripple x y z B C c= ripple x z y C B c:= by ext1 k; unfold ripple spotK; simp only [Finset.sum_apply]; apply Finset.sum_congr rfl; intro i _; exact Finset.sum_congr rfl fun v _=>skirt_swap ..
end YM.PositionX.Sage
