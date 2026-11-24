import YM.XSpace.Ciphers
/-!
# Pair-graded integration representation

Native scene scale, exact at all positions. Keep all coupons before power normalization.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Graph3
open Function Set Filter Lattice Trace Chart2 Maxwell Maxwell.Free MvPolynomial Structure1 Chiral Finsupp Mu Next.Rank.Normal Stall Pages Foundation
open scoped Topology BigOperators InnerProductSpace Classical
variable {G:Gauge}
def highest (x y:Line G): Module.Dual ℂ (Stamp G):= (peek G).toLinearMap ∘ₗ Ξ x ∘ₗ Ξ x ∘ₗ Ξ y ∘ₗ Ξ y
def slower (x y:Line G): Module.Dual ℂ (Stamp G):= (4*col x y) • ((peek G).toLinearMap ∘ₗ Ξ x ∘ₗ Ξ y) + (2*col x y^2) • (peek G).toLinearMap
lemma highs (x y:Line G)(P:Stamp G): highest x y P= peek G (Ξ x (Ξ x (Ξ y (Ξ y P)))):=rfl
lemma slows (x y:Line G)(P:Stamp G): slower x y P= 4*col x y*peek G (Ξ x (Ξ y P)) + 2*col x y^2*peek G P:=rfl
lemma range_h (x y:Line G)(P:Stamp G)(h:P∈DegZ (UnitIndex G) 3): highest x y P=0:=by rw [highs, ξ_end x (ξ_low x (ξ_low (n:=1) y (ξ_low (n:=2) y h))),map_zero]
variable (W:Initialize G)(g:G.Simple)(z x y:Cover)
local notation "A" => b_w W z
local notation "X" => u_line g W x
local notation "Y" => u_line g W y
local notation "J" => Name G
def upper : Module.Dual ℂ (Stamp G):= ∑ i:J,∑ j:J,(4:ℂ)⁻¹ • highest (X i) (Y j)
def bottom : Module.Dual ℂ (Stamp G):= ∑ i:J,∑ j:J,(4:ℂ)⁻¹ • slower (X i) (Y j)
lemma color_mix (P:Stamp G): F3 P (u_w W x) (u_w W y)= upper W g x y P+bottom W g x y P:=by
  rw [upper,bottom, u_w,u_w,under g,under g]; unfold u_r F3; rw [← clasp]; simp only [map_smul,map_sum,LinearMap.sum_apply,LinearMap.smul_apply, Finset.smul_sum]; rw [Finset.sum_comm, ← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i _; rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro j _; rw [clasp];
  change (2:ℂ)⁻¹ • ((2:ℂ)⁻¹ • F3 P (harp (X i) * _) (harp (Y j)*_))=_; rw [ψ_angles, highs, slows]; simp only [smul_eq_mul]; ring
lemma slaughter (P:Stamp G)(h:P ∈ DegZ (UnitIndex G) 3): upper W g x y P=0:=by unfold upper; simp only [LinearMap.sum_apply, LinearMap.smul_apply, range_h _ _ P h,smul_zero, Finset.sum_const_zero]
include g in
lemma mid (a b:Line G)(P:Stamp G)(h:Hom P 3): peek G (Ξ a (Ξ b (tie G A P))) = F2 G (Ξ a A) (Ξ b P)+F2 G (Ξ b A) (Ξ a P) :=by
  have H:= b_power W g z; have he:=γ_between (Ξ a (Ξ b A)) P (ξ_rule _ (ξ_rule _ H)) h (by decide); have hh:=γ_between A (Ξ a (Ξ b P)) H (ξ_rule _ (ξ_rule _ h)) (by decide)
  unfold F2 at *; simp only [map_add,ξ_tie,he,hh,zero_add,add_zero]; ring
include g in
lemma vers (a b:Line G){i j:G.ColorIndex}(hp:a∈Tint i)(hq:b∈Tint j)(P:Stamp G)(h:Hom P 3): highest a b (tie G A P)=4*F2 G (Ξ a (Ξ b A)) (Ξ a (Ξ b P)):=by
  have hb (a:Line G)(r:G.ColorIndex)(p:a∈ Tint r):= double_off W g z p; have ht : Ξ a (Ξ a (Ξ b A))=0:=by rw [ξ_comm a b, ξ_comm a b, hb a i hp,map_zero ]
  have ha:= b_power W g z
  have he : Ξ a (Ξ a (Ξ b (Ξ b P)))=0:= ξ_end a (hom_g (ξ_rule _ (ξ_rule _ (ξ_rule _ h))))
  rw [highs,angles _ _ b, hb b j hq, map_zero]; simp only [LinearMap.zero_apply, add_zero]; rw [map_add,map_add, map_smul,map_smul, angles _ _ a, angles _ _ a,hb a i hp,ht,he]; simp only [map_zero, LinearMap.zero_apply,add_zero,zero_add]
  have h1 := γ_between (Ξ a A) (Ξ a (Ξ b (Ξ b P))) (ξ_rule _ ha) (ξ_rule _ (ξ_rule _ (ξ_rule _ h))) (by decide)
  have h2 := γ_between (Ξ b A) (Ξ a (Ξ a (Ξ b P))) (ξ_rule _ ha) (ξ_rule _ (ξ_rule _ (ξ_rule _ h))) (by decide)
  unfold F2 at *; simp only [map_smul, map_add,h1,h2,smul_zero,zero_add]; simp only [smul_eq_mul]; ring

def scoreX (F:J→J→J→ℂ) (i j:J):=∑ k:J,∑ l:J,∑ m:J,(6*fuel k l m)*bstep W g z l (X i)*bstep W g z m (Y j) * F k i j
def playAll (F:J→J→J→ℂ):=∑ i:J,∑ j:J,scoreX W g z x y F i j
abbrev internal (P:Stamp G) (i j k : J):= peek G (Ξ (b_line g W z i) (Ξ (X j) (Ξ (Y k) P)))
lemma wall (P:Stamp G)(h:Hom P 3): upper W g x y (tie G A P)= playAll W g z x y (internal W g z x y P):=by
  unfold upper playAll scoreX; simp only [LinearMap.sum_apply, LinearMap.smul_apply]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>?_ ; rw [vers W g z _ _ (i:=i.2) (j:=j.2) (fares_on g (W.surveys _) false i x) (fares_on g (W.surveys _) false j y) _ h, smul_eq_mul, inv_mul_cancel_left₀ (by norm_num),double_strike W g, bound_up,← clasp]; simp_rw [_root_.map_sum, map_smul,clasp]; simp_rw [bound_up (Ξ (X i) (Ξ (Y j) P)), show ∀ (v t), F2 G (harp v) t=_ from fun v t=>ζ_line v t]; rfl
end YM.XSpace.Graph3
