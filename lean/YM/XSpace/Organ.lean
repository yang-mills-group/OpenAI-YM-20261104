import YM.XSpace.Sounder
/-! # The three activated-body receipts pull back along common remaining edges -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Finale
open Function Set Filter Trace Mu Graph3 Gland Chart2 Octave Season Lattice Chiral MvPolynomial Player Asymptotics
open scoped Topology BigOperators Classical
variable {G:Gauge}(W:Initialize G)(g:G.Simple)(x y z w:Cover)
local notation "L" => Name G
local notation "M" => mum W
local notation "Y" => mrs W
local notation "F" => playAll W g x y z
local notation "X" => u_line g W y
local notation "Z" => u_line g W z
local notation "V" => b_line g W x
abbrev rootBeam (i j k:L):ℂ:= pair (Y j) (Y k) g x y z (b_s W 0 i)
def other (i j k:L):= station W g x z y i k j
abbrev weightX (i j k:L) := latch (M i) (Y j) (Y k) g x y z
lemma station_at (i j k:L) : station W g x y z i j k= pair (M i) (Y k) g y x z (u_s W 0 j):=by rw [pair_at,station,u_s, brace_move (W.surveys _) false j y]
lemma root_at (i j k:L) : rootBeam W g x y z i j k= peek G (Ξ (X j) (Ξ (Z k) (b_s W x i))):=by rw [rootBeam,pair_at,b_s, show b_s W x i=_ from brace_move (W.surveys _) true i x]
private lemma turn (i j k:L):fuel i k j=fuel i j k:=by rw [swap_fuel i k, turn_fuel k]
lemma played_flip (f:L→L→L→ℂ): playAll W g x z y f = F (fun i j k=> f i k j):=by
  unfold playAll; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>?_ ; unfold scoreX; refine Finset.sum_congr rfl fun k _=>?_ ; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun t _=> Finset.sum_congr rfl fun q _=>?_ ; rw [turn k t q]; ring -- infer
private lemma supremist (Aa Ba Ca Da:Line G)(p:Stamp G): highest Ca Da (p* harp Aa * harp Ba) =
    2*col Aa Ca * col Ba Ca *dual Da Da p + 2*col Aa Da * col Ba Da *dual Ca Ca p + 4*(col Aa Ca * col Ba Da+col Aa Da * col Ba Ca)*dual Ca Da p:=by
  rw [highs]; simp only [ξ_mul, ξ_harp,ξ_zero,map_add,map_mul,map_zero,zero_mul,mul_zero,add_zero,zero_add,peek_C,peek_leg]; simp only [dual,LinearMap.comp_apply,AlgHom.toLinearMap_apply]; ring
private lemma kill (i j k b:L)(hF:fuel i j k ≠0)(y:Cover) : col (V j) (u_line g W y b)=0 ∨ col (V k) (u_line g W y b)=0:= by
  have hk:j.2≠ b.2 ∨ k.2≠ b.2:= not_and_or.mp fun h=> (fuel_diff i j k hF).2.1 (h.1.trans h.2.symm); rcases hk with h|h; exact Or.inl (bstep_off W g x (fares_on g (W.surveys _) false b y) j h); exact Or.inr (bstep_off W g x (fares_on g (W.surveys _) false b y) k h)
private def coupon (b c i j k:L):ℂ:= 3*fuel i j k * bstep W g x j (X b)*bstep W g x k (Z c)* rootBeam W g x y z i b c
private lemma thresh (b c i j k:L) : (4:ℂ)⁻¹ • highest (X b) (Z c) ((3*fuel i j k) • (b_s W x i* harp (V j)* harp (V k)))=coupon W g x y z b c i j k+coupon W g x y z b c i k j:=by
  unfold coupon bstep; rw [root_at,turn i j k]; rw [show peek G (Ξ (X b) (Ξ (Z c) (b_s W x i)))=dual (X b) (Z c) _ from rfl, map_smul,supremist]; by_cases h:fuel i j k=0; simp [h]
  simp only [smul_eq_mul]; rcases kill W g x i j k b h y with e|e <;> rcases kill W g x i j k c h z with he|he <;> rw [e,he] <;> ring
lemma cap : upper W g y z (b_1 W x)= F (rootBeam W g x y z):=by
  rw [breadth g W x,upper,playAll]; simp only [LinearMap.sum_apply,LinearMap.smul_apply]; refine Finset.sum_congr rfl fun b _=> Finset.sum_congr rfl fun c _=>?_ ; unfold scoreX b_r; rw [_root_.map_sum]; simp only [map_sum,Finset.smul_sum,thresh]; apply Finset.sum_congr rfl; intro i _; let f:= coupon W g x y z b c i; simp_rw [Finset.sum_add_distrib]; change _+(∑ j:L,∑ k:L,f k j)=_; rw [Finset.sum_comm (f:=fun j k:L=> f k j)]; rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro j _; unfold f; rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun k _=>?_ ; unfold coupon; ring
end YM.XSpace.Finale
