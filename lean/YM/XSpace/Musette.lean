import YM.XSpace.Viola
/-!
# Field-independent 3-leg interaction value in unnormalized E⁰ labels

Numeric parameter preread. Before test & representation in e normalized. Geometry `estn` equivalent $5$ units (and arbitrary). Limit *uniform angle* even permitting angle and height to go together.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Angle
open Function Set Filter Relief Season Trace Litter Tide Sail Playpen Lattice Chiral
open scoped Topology BigOperators
variable {ι:Type}{L:Filter ι}{R:ι→ℝ}{v:ι→E4}{b:E4}{E:ℝ}
local notation "P₀" => spoken
local notation "ℓ" => Season.line false
-- local point value of C with mixed chiralities
abbrev est (p m n:P)(z x y:E4):=∑ i:Axis,∑ j:Axis,q true p i j * ℓ m i (z-x)* ℓ n j (z-y)
variable (c:Shade.Cut)
def atria (p m n:P)(z x y:E4): ℝ:= est p m n z x y - ∑ t:P,sweepT c p t m n z x y
def op (i j k:P)(z x y:E4): ℝ:=∑ m:P,∑ n:P, P₀ (z-x) j m* P₀ (z-y) k n * atria c i m n z x y
def tens (z x y:E4): ℝ:=∑ i:P,∑ j:P,∑ k:P,liftedSign i j k * op c i j k z x y
abbrev answer (G:Gauge)(x y z:E4):= (6:ℝ)*S_color G * tens c x y z
abbrev θs : ℝ:=5
local notation "a" => θs
abbrev height (R:ι→ℝ)(v:ι→E4)(i:ι):= R i • v i
abbrev root (v:ι→E4)(i:ι):= a • v i
abbrev tip := Maxwell.normal*(a^2)⁻¹
lemma tip_ok : 0<tip:=mul_pos Maxwell.normal_pos (by norm_num [θs])
structure Motion (L:Filter ι)(R:ι→ℝ)(v:ι→E4)(b:E4): Prop where
 flight : Tendsto R L atTop
 tends : Tendsto v L (𝓝 b)
 norm : ∀ i, ‖v i‖=1
 unit : ‖b‖=1
variable (M:Motion L R v b)
local notation "X" => height R v
local notation "Z" => root v
lemma sphere_n (H:‖b‖=1): b ≠ 0 := norm_pos_iff.mp (H.symm ▸ one_pos)
lemma sphere_len {p:ℝ} (h:‖b‖=1)(ht:0≤p): ‖p • b‖=p:=by rw [norm_smul,Real.norm_of_nonneg ht,h,mul_one]
include M
lemma up : ∀ᶠ i in L,0<R i:= M.flight.eventually_gt_atTop 0
lemma top : ∀ᶠ i in L,a<R i:= M.flight.eventually_gt_atTop a
lemma wherewithal (i:ι): X i - Z i=(R i-a) • v i:= by rw [sub_smul]
lemma clear (K:c.rOut<1): ∀ᶠ i in L,Gleam c (X i) 0 (Z i) ∧ 512*‖(0:E4)-Z i‖ ≤ ‖(0:E4)-X i‖:=by
  filter_upwards [up M,M.flight.eventually_gt_atTop 4096] with i hi hh; have h' : θs <R i:=by unfold θs; linarith
  have hx:‖X i‖=R i:= sphere_len (M.norm i) hi.le; have hz:‖Z i‖=a:=sphere_len (M.norm i) (by norm_num [θs]); rw [zero_sub, norm_neg]; have ho:Gleam c (X i) 0 (Z i):= ⟨by unfold Season.range; rw [sub_zero,hx]; linarith,by unfold Season.range; rw [wherewithal M,sphere_len (M.norm i) (by linarith : 0≤R i-a)]; dsimp [θs]; linarith,by unfold Season.range; rw [zero_sub,norm_neg,hz]; unfold θs; linarith⟩; refine ⟨ho,?_⟩; rw [zero_sub,norm_neg,hx,hz]; unfold θs; linarith
lemma paid (i:ι):Maxwell.Green (0-Z i)=tip:=by unfold Maxwell.Green; rw [zero_sub,norm_neg, show ‖Z i‖=_ from sphere_len (M.norm i) (by norm_num [θs] : (0:ℝ)≤a)]
lemma costs_shift {D:ℕ} {F:Breeze}{H:Toe}(P:Beam D H F):
    Tendsto (fun i=> R i ^ D * F (X i-0)) L (𝓝 (F b)):= by simp_rw [sub_zero]; refine ((P.value b (sphere_n M.unit)).continuousAt.tendsto.comp M.tends).congr' ?_; filter_upwards [up M] with i hi; unfold Function.comp height; rw [share_hom _ hi P (sphere_n (M.norm i)),inv_pow]; field_simp
lemma from_lip {D:ℕ}{F:Breeze}{H:Toe}(P:Beam D H F): Tendsto (fun i=> R i ^D * F (X i-Z i)) L (𝓝 (F b)):=by
  have hR : Tendsto (fun i=>R i-a) L atTop:=by simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right _ (-a) M.flight
  let S i:= R i-a; have hh: Tendsto (fun i=> a*(S i)⁻¹+1) L (𝓝 1):=by simpa using (hR.inv_tendsto_atTop.const_mul a).add_const 1
  have he:= (hh.pow D).mul ((P.value _ (sphere_n M.unit)).continuousAt.tendsto.comp M.tends); rw [one_pow,one_mul] at he; apply he.congr'; filter_upwards [top M] with i hi; unfold comp; rw [wherewithal M, share_hom (R i-a) (sub_pos.mpr hi) P (sphere_n (M.norm i)), show a*(S i)⁻¹+1=R i*(S i)⁻¹ from ?_, mul_pow, mul_assoc]; unfold S; have hp:=sub_pos.mpr hi; field_simp; ring
lemma direct_quiet (p m n:P): Tendsto (fun i=>R i^4 * est p m n (X i) 0 (Z i)) L (𝓝 0):=by
  let f (i j:Axis)(w:ι): ℝ:= R w^3*ℓ m i (X w-0)*(R w^3* ℓ n j (X w-Z w))
  have ht (i j:Axis): Tendsto (fun w=> R w^4 * (q true p i j*ℓ m i (X w-0)* ℓ n j (X w-Z w))) L (𝓝 0):=by
    have he:= ((costs_shift M (shore false m i)).mul (from_lip M (shore false n j))).const_mul (q true p i j); have hk:= (M.flight.inv_tendsto_atTop.pow 2).mul he; rw [zero_pow (by decide), zero_mul] at hk; apply hk.congr'; filter_upwards [up M] with w hw; simp only [Pi.inv_apply]; field_simp
  unfold est; simp_rw [Finset.mul_sum]
  have he:= tendsto_finsetSum (Finset.univ) (fun i hi=> tendsto_finsetSum _ (fun j (_:j∈Finset.univ)=> ht i j)); simpa using he
lemma transposeT (i:ι)(p r:P) (hi:0<R i): surfT false true r p (0-X i)= spoken (X i-0) p r := by
  have hp:X i≠0:= smul_ne_zero hi.ne' (sphere_n (M.norm i)); rw [sub_zero, zero_sub, hes _ _ _ _ hp, hesSym _ _ _ _ hp]
include c in
lemma skylight (K:c.rOut<1)(p m n t:P): Tendsto (fun i=>R i^4 * sweepT c p t m n (X i) 0 (Z i)) L (𝓝 (spoken b p t*(liftedSign m t n*tip))):=by
  obtain ⟨D,hD,H⟩:= payroll c p t m n; let W:= liftedSign m t n*tip
  let F i:= R i^4 * sweepT c p t m n (X i) 0 (Z i); let G i:= R i^4 *spoken (X i-0) p t*W; have ht:Tendsto G L (𝓝 (spoken b p t* W)):= (costs_shift M (charted true false p t)).mul_const _; have hf:Tendsto (fun i=> F i-G i) L (𝓝 0):= by
    refine tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall fun i=> norm_nonneg _) ?_ (show Tendsto (fun i=> (R i)⁻¹*(D/a)) L (𝓝 0) from by simpa using M.flight.inv_tendsto_atTop.mul_const (D/a))); filter_upwards [clear c M K,up M] with i hi hp; have he:=H _ _ _ hi.1 hi.2; rw [paid M,transposeT M i _ _ hp,zero_sub,zero_sub,norm_neg,norm_neg,sphere_len (M.norm i) (by norm_num [θs]: 0≤a), sphere_len (M.norm i) hp.le] at he
    unfold F G; rw [mul_assoc _, ← mul_sub,norm_mul,Real.norm_of_nonneg (pow_pos hp _).le]; exact (mul_le_mul_of_nonneg_left he (by positivity)).trans_eq (by unfold θs; field_simp)
  refine (zero_add (spoken b p t*W)) ▸ (hf.add ht |>.congr fun _=>sub_add_cancel ..) -- check orientation
end YM.XSpace.Angle
