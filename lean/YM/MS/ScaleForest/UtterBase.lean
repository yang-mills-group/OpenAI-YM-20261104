import YM.MS.ScaleForest.DoubleCross
/-!
# Solve the two-mark triangle system in its rank-two slice

Tactics structured to not change the momentum sign convention on the
phase when observing a mark. Specialize only the legitimately
holomorphic D-part beforehand. Solve at finite upper radius (all s)
first. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest.Triangle
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum Motif Literal Halo
open Lattice Momentum Tone Detect Osc Fiddle Snap XSpace XSpace.Chiral Cylinder Planted Beamline Quadratic
open scoped Topology ContDiff
variable {G : Gauge} {I:Type} (X Y:Pupil) (x:E4) {m:ℕ} (p q:QP) (i j:Shaft G 0)(s:ℝ)

-- symmetric ink (used for both the pair and its parent)
def tinct (z:Ω G):= allot X Y x p q i j z + allot X Y x q p j i z
def stained (V : Ω G→ℂ):= ∑ z:Ω G,tinct X Y x p q i j z*V z
lemma stain_bind (V W : Ω G→ℂ): stained X Y x p q i j (V+W)=stained X Y x p q i j V+stained X Y x p q i j W:= by simp only [stained,Pi.add_apply,mul_add,Finset.sum_add_distrib]
lemma tint_pair (V : Ω G→ℂ): tincture X Y x p q i j V+tincture X Y x q p j i V= stained X Y x p q i j V:= by unfold stained tinct tincture; rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun i _=> (add_mul ..).symm )

lemma stain_side {V F:Ω G→ℝ→ℂ}(h:∀ z,HasDerivAt (V z) (F z s) s) : HasDerivAt (fun s=> stained X Y x p q i j (fun z=> V z s)) (stained X Y x p q i j (fun z=>F z s)) s:= HasDerivAt.fun_sum (fun z _=> (h z).const_mul _)
lemma fade_stain (F:Ω G→ℝ→ℂ) (h:∀ z,Tendsto (F z) atBot (𝓝 0)) : Tendsto (fun s=>stained X Y x p q i j (fun z=>F z s)) atBot (𝓝 0):= by unfold stained; simpa only [mul_zero,Finset.sum_const_zero] using! tendsto_finsetSum Finset.univ (fun z _=> (h z).const_mul (tinct X Y x p q i j z))

private lemma trans_tinct (V:Ω G→ℂ): stableA p (fun i=>stained X Y x p q i j V) := by
   have h (v:Ω G)(u:Shaft G 0): tinct X Y x p q u j v=(premium X Y v*Φ x p* Cur Y v.2 q j)*Cur X v.1 p u+(premium X Y v*Φ x q*Cur X v.1 q j)*Cur Y v.2 p u:= by unfold tinct allot; ring
   intro a; simp_rw [stained,Finset.mul_sum]; rw [Finset.sum_comm]; refine Finset.sum_eq_zero fun b _=>?_ ; simp_rw [← mul_assoc (↑(p _):ℂ), ← Finset.sum_mul,h, mul_add ];
   rw [Finset.sum_add_distrib]; let u:=premium X Y b; let c:=u*Φ x p*Cur Y b.2 q j; let d:= u*Φ x q* Cur X b.1 q j;
   change ((∑ i:L 0,(p i:ℂ)*(c*Cur X b.1 p (a,i))) + (∑ i:L 0,(p i:ℂ)*(d* Cur Y b.2 p (a,i))))*V b=0
   simp_rw [mul_left_comm _ c,mul_left_comm _ d, ← Finset.mul_sum, show (∑ i:L 0,(p i:ℂ)* Cur X b.1 p (a,i) )=0 from antenna_right (m:=0) p X b.1 a,show (∑ i:L 0,(p i:ℂ)* Cur Y b.2 p (a,i) )=0 from antenna_right (m:=0) p Y b.2 a, mul_zero,add_zero,zero_mul ]

lemma sameStain {F:Mob G}(ht:Goods 2 F)(V:Ω G→ℂ)(he:∀ (p q:QP) (i j:Shaft G 0),aim F p q i j= stained X Y x p q i j V): GoodAim 0 F where
    paid:= ht
    sym p q i j:= by rw [he,he]; apply Finset.sum_congr rfl; intro _ _; unfold tinct; rw [add_comm]
    direct p q j:= by simp_rw [he]; exact trans_tinct X Y x p q j V

abbrev sunV (z:Ω G)(s:ℝ):= sunRise X Y z.1 z.2 x s
abbrev dotV (z:Ω G)(s:ℝ):= sunDot X Y z.1 z.2 x s
abbrev moonV (z:Ω G)(s:ℝ):= moonRise X Y z.1 z.2 x s
abbrev dotM (z:Ω G)(s:ℝ):= moonDot X Y z.1 z.2 x s

variable [TopologicalSpace I] [FirstCountableTopology I] {A:I→QP} (y:I) (μ:ℝ)
   (hp: Theater.out x=A y)
include hp
local notation "d" => cursor false

def Lead (μ:ℝ) (p:QP)(q:QP) (i j:Shaft G 0)(x:I) (V:Planted G I true)(s:ℝ):= aim (absNom μ V s x) p q i j

theorem mid_push : aim (absPush μ (mid X Y A G) s y) p q i j=stained X Y x p q i j (fun z=>dotV X Y x z s):= by
    unfold mid; rw [pushedP μ s y d (show (bed (originPin X G) : Planted G I false).Stand from trivial) (show (bed (originPin Y G) : Planted G I false).Stand from trivial) ]; obtain hX:= (Planted.observing μ s y (bed (originPin X G)) trivial).1; obtain hY:= (Planted.observing μ s y (bed (originPin Y G)) trivial).1;
    have he(t:Pupil): absNom μ (bed (originPin t G)) s y=(enrol t G 0).symbol:= pinnedAtom ..; simp_rw [he] at hX hY ⊢;
    rw [ prim_0 G s,← hp,← tint_pair, expense_cross x p q s μ hX hY (Por_base X G) (Por_base Y G) i j (T:=fun _ _ z=> dotV X Y x z s) ?_ ]; intro p q z; unfold Christ; simp only [mul_one,one_mul]; exact ⟨ sunSupported ..,rfl⟩
variable (h:AdmittedGap A)
include h
omit hp [FirstCountableTopology I] in
lemma mid_walk : (mid X Y A G).Stand := ⟨ trivial,trivial,h⟩
omit [FirstCountableTopology I] in
lemma point_gap : x≠0:= by rintro rfl; rw [map_zero] at hp; obtain ⟨r,hr,hl⟩:= h.lower; specialize hl y; rw [ ← hp,norm_zero] at hl; exact hr.not_ge hl

theorem mid_progress : aim (absNom μ (mid X Y A G) s y) p q i j=stained X Y x p q i j (fun z=> sunV X Y x z s) := by
    let T:=mid X Y A G; let F(t:ℝ):=aim (absNom μ T t y) p q i j
    have hX:= StartZero μ y (V:=T) [armI i p,armI j q]; have he (t:ℝ): HasDerivAt F (stained X Y x p q i j fun z=> dotV X Y x z t) t:= by rw [ ← mid_push X Y x p q i j t y μ hp ]; exact Speed μ t y _ (mid_walk X Y h)
    apply congr_fun (ode_solver he (fun t=> stain_side X Y x p q i j t (fun z=> sunSpeed X Y z.1 z.2 x t)) hX
         (fade_stain X Y x p q i j _ (fun _=> sunStart X Y _ _ x (point_gap x y hp h)))) s

theorem mid_right (G:Gauge): GoodAim 0 (absNom μ (mid X Y A G) s y) := sameStain X Y x (Planted.observing μ s y (mid X Y A G) (mid_walk X Y h)).2 _ (fun p q i j=> mid_progress X Y x p q i j s y μ hp h)

end YM.MS.ScaleForest.Triangle
