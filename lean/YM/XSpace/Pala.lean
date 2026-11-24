import YM.XSpace.Banter
/-!
# Weight-leading convolution spectral coefficient
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Octave
open Function Set Filter Lattice Trace Relief Sail Asymptotics Chiral
open scoped Topology BigOperators
variable (x y: Cover)
local notation "𝕆" => Sail.cover
abbrev curled (a b:P)(t:P):= fun x y:Cover=> ∑ i:Axis,∑ j:Axis,q false t i j*res (field false a i) (field false b j) x y
def disc (a b t:P)(i j:Axis):=∑ m:Axis,∑ n:Axis,q false a i m*q false t m n*q false b j n
lemma curled₁ (a b:P)(t:P): curled a b t x y=∑ i:Axis,∑ j:Axis,disc a b t i j* chordal i j x y:=by
  have he(x y:Cover)(a:P)(k:Axis)(f:Toe)(H:f∈Terrain 3) : res (field false a k) f x y=∑ m:Axis, q false a m k * res (η m 𝕆) f x y:=by unfold field; rw [ret_fin (i:=3) _ _ (fun i _=> Submodule.smul_mem _ _ (down_hill hill2 i)) H (by norm_num)]; simp_rw [ret_smul]
  unfold curled disc chordal; simp_rw [he x y a _ _ (bunker false b _), ret_swap (η _ 𝕆) (field false b _), he y x b _ _ (down_hill hill2 _), ret_swap (η _ 𝕆) (η _ 𝕆) y x, Finset.mul_sum,Finset.sum_mul]; calc -- reorganize
   _ = ∑ u:Axis,∑ v:Axis,∑ i:Axis,∑ j:Axis,q false a i u*q false t u v*q false b j v*res (η i 𝕆) (η j 𝕆) x y:= by refine Finset.sum_congr rfl fun u _=> Finset.sum_congr rfl fun v _=> Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>?_ ; ring
   _ = _:= ?_
  let f(i j m n:Axis):=q false a i m*q false t m n*q false b j n*res (η i 𝕆) (η j 𝕆) x y
  change ∑ m:Axis,∑ n:Axis,∑ i:Axis,∑ j:Axis, f i j m n=∑ i:Axis,∑ j:Axis,∑ m:Axis,∑ n:Axis,f i j m n; conv_lhs => enter [2,m]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _=>?_ ; conv_lhs=> enter [2,m]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
lemma curled₂ (a b t:P): (∑ i:Axis,∑ j:Axis, disc a b t j i*chordal j i x y)=curled a b t x y:=by rw [curled₁,Finset.sum_comm]
lemma curled₃ (a b t:P): (∑ i:Axis,∑ j:Axis, disc a b t j i* chordal i j x y)=2 * liftedSign a t b * 𝕆 (x-y)-curled a b t x y:=by
  apply eq_sub_iff_add_eq.mpr; rw [curled₁]; simp_rw [← Finset.sum_add_distrib,← add_mul]; unfold disc; simp_rw [convolve a t b, dot_at, mul_ite]; simp only [mul_one,mul_zero,ite_mul,zero_mul,Finset.sum_ite_eq', Finset.mem_univ,↓reduceIte]; rw [← Finset.mul_sum,coil] -- try
variable {ι:Type}{L:Filter ι}{a:ι→ℝ}{x y:ι→Cover}{u:E4}(s:Relief.Stage L a)(H:distFee L a (fun i=> x i-y i))
include s H in
lemma bravo (i j k:P): Little L a 2 (fun v=> curled i j k (x v) (y v) - liftedSign i k j * 𝕆 (x v-y v)):=by
  let f (t w:Axis)(v:ι):= disc i j k w t * (chordal w t (x v) (y v)-chordal t w (x v) (y v)); have ht (B v:Cover): (∑ t:Axis,∑ w:Axis,disc i j k w t*(chordal w t B v-chordal t w B v))=2*(curled i j k B v-liftedSign i k j* 𝕆 (B-v)):=by simp_rw [mul_sub,Finset.sum_sub_distrib,curled₂, curled₃]; ring
  have h:Little L a 2 (fun v=> ∑ t:Axis,∑ w:Axis, f t w v):= IsLittleO.sum (fun t (_: t∈Finset.univ)=> IsLittleO.sum (fun w (_:w∈Finset.univ)=> (conductor s H w t).const_mul_left _)); refine (IsLittleO.const_mul_left h ((2:ℝ)⁻¹)).congr (fun v=>?_) (fun _=>rfl); unfold f; rw [ht]; ring
include s in
lemma tune_hari (X:distance L a (fun i=> x i-y i) u)(h:u≠0)(i j k:P): Tendsto (fun v=> (a v)⁻¹^2*curled i j k (x v) (y v)) L (𝓝 (liftedSign i k j* Maxwell.Green u)):=by
  have hh:= tau s (bravo s (finite_pay s X h) i j k); have hg:Tendsto (fun v=> (a v)⁻¹^2*𝕆 (x v-y v)) L (𝓝 (Maxwell.Green u)):= Tide.greenBeam.beams s.good s.zero X h [] -- defeq
  have hr:= hh.add (hg.const_mul (liftedSign i k j)); rw [zero_add] at hr; refine hr.congr fun v=> ?_; simp only [smul_eq_mul]; ring
end YM.XSpace.Octave
