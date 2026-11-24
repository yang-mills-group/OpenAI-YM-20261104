import YM.MatchingLedger.Mountain.Miner

/-! # Keep double ELL explicitly! The square of a row is a priced pair of entries.
 Not calling `coefficient bound × volume` before summing a rank hierarchy.
 -/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.MatchingLedger.Mountain.Miner
open Set Function Filter Precision RG MeasureTheory Lattice Wilson Metric Push.Uniform Exterior
open Work.F02
open scoped ContDiff Topology BigOperators Matrix.Norms.Frobenius InnerProductSpace Classical
variable {G:Gauge} {n:Side} {p:Clip} {W:PathData G} {σ C Λ:ℝ}
local notation "E"=> fieldDir G n 1
variable (q : Signed)(a:Site n) {μ:ℝ} (hp:0<μ)(ht:2*μ≤σ) (k:ℕ) (hW:W.Bounds p σ C Λ)
include hW hp ht
lemma rates (b:PlaqAxes) : revenue 1 k μ (high b W) (ore W q a b) (C*height G k μ):=by
   let u i:= W.row b i; let t:= height G k μ
   let m i:=Real.exp (μ * high b W i); let f(i:ℕ):= |(u i).1| * m i*t
   have he:= height_nn G k hp; have hh(i): 0≤ f i:= by unfold f m t; positivity
   let g(i:ℕ):= |(u i).1| * Real.exp (σ * high b W i)
   let Z (i:ℕ):= m i*f i; have hx i: Z i ≤ g i*t:=by
      have hx' : m i * m i ≤ Real.exp (σ*high b W i):= by unfold m; rw [←Real.exp_add]; exact Real.exp_monotone (by have hh:= mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg (high b W i) (α:=ℝ)); linarith only [hh])
      refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx' (abs_nonneg ((u i).1))) he); unfold Z f; ring
   have hZ(i):0≤ Z i:= mul_nonneg (Real.exp_pos _).le (hh _)
   have hy: SumBudget g C:= hW.rows b; have hy':=hy.2.1.mul_right t
   have hu:= hy'.of_nonneg_of_le hZ hx
   refine ⟨f, hh,⟨hZ,hu,(hu.tsum_le_tsum hx hy').trans ?_⟩,fun i _ hx=> miners q a hp k hx (u i).2 (u i).1⟩
   rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right hy.2.2 he

-- REAL inner product convention. Keep ordered pairs.
abbrev beam : ℝ:=1/2
def bunion (W:PathData G)(q:Signed)(a:Site n)(b:PlaqAxes)(i:ℕ×ℕ): E → ℝ:= fun x=> beam*inner ℝ (ore W q a b i.1 x) (ore W q a b i.2 x)
def fare₁ (b:PlaqAxes)(W:PathData G)(i:ℕ×ℕ):= high b W i.1 +high b W i.2

def garnet (G:Gauge)(k:ℕ)(C μ:ℝ) : ℝ:= beam*(2:ℝ)^k*(C*height G k μ)^2
lemma located (b:PlaqAxes) : revenue 1 k μ (fare₁ b W) (bunion W q a b) (garnet G k C μ):=by
   let H:= rates q a hp ht k hW b; let t:= H.book
   let u i:= Real.exp (μ*high b W i)* t i
   have hu : SumBudget u (C*height G k μ):= H.budget
   let e:ℝ:=beam* (2:ℝ)^k; let g(i:ℕ×ℕ):=e*(t i.1*t i.2)
   have he : 0 ≤ e:= by unfold e beam; positivity
   have hg(i:ℕ×ℕ):0≤g i:=mul_nonneg he (mul_nonneg (H.straight _) (H.straight _))
   have hy: Summable (fun p:ℕ×ℕ=>u p.1 * u p.2):= summable_mul_of_summable_norm hu.2.1.norm hu.2.1.norm
   let f(i:ℕ×ℕ):= Real.exp (μ*fare₁ b W i)*g i
   have hx : f=(fun i:ℕ×ℕ=> e* (u i.1*u i.2)):=by ext i; unfold f u fare₁ g; push_cast; rw [mul_add,Real.exp_add]; ring
   refine ⟨g,hg,⟨fun i=> mul_nonneg (Real.exp_pos _).le (hg _), show Summable f from hx.symm ▸ (hy.mul_left e),?_⟩,fun i x hX=> ?_⟩
   · change ∑' i,f i ≤ _; rw [hx,tsum_mul_left,←(hu.2.1.tsum_mul_tsum hu.2.1 hy),←pow_two]; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (tsum_nonneg hu.1) hu.2.2 _) he
   have ht: ‖innerSL ℝ («E»:=G.Color)‖≤ 1:=by apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x=>?_ ; simp
   have h := (H.proceeds i.1 x hX).bilinear (innerSL ℝ) (H.proceeds i.2 x hX) ht |>.smul beam
   exact h.mono (le_of_eq (by rw [abs_of_nonneg (show 0≤beam from by norm_num [beam])]; unfold g e t; ring))

include k in
lemma revenue_bunion (b:PlaqAxes){x:E}(hx:x∈ball 0 1):
    ∑' i,bunion W q a b i x= ‖W.ell (fortune q x) (a,b)‖^2/2 := by
   let Z(n:ℕ):=ore W q a b n x; let f := ∑' i,Z i
   have hF: Summable Z:= (rates q a hp ht k hW b).values hp.le hx
   have h (u : G.Color) (Z:ℕ→G.Color)(hp:Summable Z): (∑' i,inner ℝ u (Z i))=inner ℝ u (∑' i, Z i):= (hp.hasSum.mapL (innerSL ℝ u)).tsum_eq
   have he(i): (∑' j:ℕ,bunion W q a b (i,j) x)=beam* inner ℝ f (Z i):=by unfold bunion; change ∑' j, beam* inner ℝ (Z i) (Z j)=_; rw [tsum_mul_left, h (Z i) Z hF,real_inner_comm]
   rw [((located q a hp ht k hW b).values hp.le hx).tsum_prod]; simp_rw [he]; rw [tsum_mul_left,h f Z hF]; change beam* inner ℝ f f=_; rw [real_inner_self_eq_norm_sq]
   change beam*‖_‖^2= ‖f‖^2/2; ring
end YM.MatchingLedger.Mountain.Miner
