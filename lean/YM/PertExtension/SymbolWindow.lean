import YM.PertExtension.PolarBound
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! Resolving frequency zero in the free native Wilson curl-curl propagator.
Gauge-color trace not taken; physical orthonormal index used, not adjoint component
with an extra Casimir multiplier. This uses frequency partitioning before period
sampling. There is no modification of lattice step scales. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace YM.PertExtension.LatticePT.Band
open MeasureTheory Measure Filter Maxwell Next Next.Rank Next.Rank.Radian Topology Analysis Asymptotics Set Real Metric Lattice Beamer Atlas Normal Perch Wall CellsInt Prayer RG
open Function Finset
open scoped ContDiff Topology BigOperators Classical NNReal FourierTransform RealInnerProductSpace
local notation "𝑒" => Real.exp
local notation "ℑ" => Complex.I

-- centered product cutoff with integer shifts summing to one (smaller than nearest singular point)
def rise (u : ℝ):ℂ := smoothTransition (2*u-1/2)
def tent (u : ℝ):ℂ := 1-rise u-rise (-u)
def hood (z:E4) := ∏ i, tent (z i)
lemma rise_zero {u} (h : u≤1/4) : rise u=0:= by unfold rise; rw [smoothTransition.zero_of_nonpos (by linarith)]; rfl
lemma rise_one {u} (h : 3/4≤u) : rise u=1:= by unfold rise; rw [smoothTransition.one_of_one_le (by linarith)]; rfl
lemma tent_small {u} (h : 3/4≤|u|) : tent u=0:= by
  rcases le_abs.mp h with h|h
  · rw [tent,rise_one h,rise_zero (u:= -u) (by linarith)]; simp
  rw [tent, rise_one h,rise_zero (u:=u) (by linarith)]; simp
lemma hood_away {z : E4}(h : 2<‖z‖) : hood z=0 := by
  unfold hood; rw [Finset.prod_eq_zero_iff]
  by_contra! hh
  have hp i :|z i|<3/4:= lt_of_not_ge fun h=>hh i (Finset.mem_univ i) (tent_small h)
  have ht:= EuclideanSpace.real_norm_sq_eq z
  have he := Finset.sum_le_sum (f:=fun i=>(z i)^2) (g:=fun (_:Axis)=>(1:ℝ)) (fun i (_:i∈Finset.univ) =>by nlinarith [abs_lt.mp (hp i)]) -- assumes nonneg, replace
  have hp: Fintype.card Axis=4:=rfl -- maybe not
  rw [Finset.sum_const, Finset.card_univ,hp] at he
  norm_num at he; nlinarith only [ht,h,he]

lemma rise_smooth : ContDiff ℝ ∞ rise:=by
  refine Complex.ofRealCLM.contDiff.comp <| smoothTransition.contDiff.comp (?_:ContDiff ℝ ∞ fun x=>_)
  exact (contDiff_const.mul contDiff_id).sub (contDiff_const.div_const _)
lemma tent_smooth : ContDiff ℝ ∞ tent:= (contDiff_const.sub rise_smooth).sub (rise_smooth.comp contDiff_neg)
lemma hood_smooth : ContDiff ℝ ∞ hood:= contDiff_prod fun i _=> tent_smooth.comp (EuclideanSpace.proj (𝕜:=ℝ) i).contDiff
lemma hood_zero : hood 0=1:= by
  have h: rise 0=0:=rise_zero (by norm_num)
  unfold hood tent; rw [show WithLp.ofLp (0:E4)=fun _=>0 from rfl];simp [h]


def increment (i:Axis)(z:E4):= readD (basis i) z
def location (z:E4) := ∑ i, ‖increment i z‖^2
abbrev polarPoint (q : ℝ×E4):E4:= q.1 • q.2

def takeoff (i : Axis)(q : ℝ × E4) := chirp i q.2 * dslope Complex.exp 0 (q.1 * chirp i q.2)
lemma exp_div : ContDiff ℝ ∞ (dslope Complex.exp 0) :=by
  have h:ContDiff ℂ ω (dslope Complex.exp 0):=(contDiff_omega_iff_analyticOnNhd.mpr ?_) -- x? 
  exact (h.of_le (n:=ω) (m:= ∞) le_top).restrict_scalars _
  have he := (Complex.differentiableOn_dslope (f:=Complex.exp) (c:=0) (s:=Set.univ) univ_mem).mpr Complex.differentiable_exp.differentiableOn
  exact fun w _ => he.analyticAt univ_mem
lemma takeoff_smooth (i : Axis) : ContDiff ℝ ∞ (takeoff i) :=
by
    have H : ContDiff ℝ ∞ ((chirp i) ∘ Prod.snd (α:=ℝ)) := (show ContDiff ℝ ∞ (chirp i) from (show chimes (basis i)=chirp i from chore i) ▸ glides (basis i)).comp contDiff_snd
    exact H.mul (exp_div.comp ((Complex.ofRealCLM.contDiff.comp contDiff_fst).mul H))
lemma increment_r (i:Axis) (q:ℝ×E4) : increment i (polarPoint q)=↑q.1 * takeoff i q:=by
    have h:= sub_smul_dslope Complex.exp 0 (q.1 * chirp i q.2)
    change (↑q.1 * chirp i q.2 - 0)*dslope Complex.exp 0 (q.1 * chirp i q.2)=_ at h
    unfold takeoff increment polarPoint readD; rw [← mul_assoc,sub_zero, Complex.exp_zero] at * -- maybe LHS
    rw [h, Pi.sub_apply, terrel]; congr 1
    rw [congr_fun (chore i)];unfold chirp
    congr 1
    change _* (((q.1 * q.2 i):ℝ):ℂ)=_
    rw [Complex.ofReal_mul]; ring
@[simp] lemma takeoff_zero i z: takeoff i (0,z)=chirp i z:=by
    unfold takeoff; change _*dslope Complex.exp 0 ((0:ℝ)*_) = _
    rw [Complex.ofReal_zero,zero_mul,dslope_same,(Complex.hasDerivAt_exp 0).deriv] -- instead deriv_exp
    simp

lemma increment_pole (z : E4)(i) : increment i z=0 ↔ ∃ m : ℤ,(m:ℝ)=z i := by
    unfold increment readD; rw [Pi.sub_apply, terrel,congr_fun (chore _)]
    change Complex.exp _-1=0 ↔ _
    rw [sub_eq_zero, Complex.exp_eq_one_iff]
    have hp : ((2*Real.pi:ℝ):ℂ)*ℑ≠0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity))) Complex.I_ne_zero
    constructor
    · rintro ⟨m,h⟩
      refine ⟨m,Complex.ofReal_injective (mul_left_cancel₀ hp (b:=((m:ℝ):ℂ)) (c:=↑(z i)) ?_)⟩
      rw [Complex.ofReal_mul]; push_cast; rw [show (2:ℂ)*π*ℑ*(m:ℂ)=(m:ℂ)*(2*π*ℑ) from mul_comm ..,← h]; rfl
    rintro ⟨m,h⟩; exact ⟨m, by unfold chirp;rw [← h];push_cast;ring⟩
lemma location_pos {z : E4}{i : Axis}(h : ∀ m : ℤ,(m:ℝ)≠z i) : 0<location z :=
  (pow_pos (norm_pos_iff.mpr (fun hf=>(increment_pole z i|>.mp hf).elim h)) 2).trans_le
    (Finset.single_le_sum (f:=fun i=> ‖increment i z‖^2) (fun i (_:i∈ Finset.univ)=>sq_nonneg _) (Finset.mem_univ i))

def masswell (q:ℝ×E4):= ∑ i:Axis,‖takeoff i q‖^2
lemma location_at (q : ℝ×E4): location (polarPoint q)=q.1^2*masswell q:=by
  unfold location masswell;rw [Finset.mul_sum];exact Finset.sum_congr rfl fun i _ =>by rw [increment_r,norm_mul, Complex.norm_real,Real.norm_eq_abs, mul_pow, sq_abs]
lemma origin_mass (z:E4):masswell (0,z)=(2*π)^2*‖z‖^2:=by
    rw [masswell,EuclideanSpace.real_norm_sq_eq,Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _=>?_ ; rw [takeoff_zero,chirp]
    simp only [norm_mul,norm_pow,Complex.norm_ofNat, Complex.norm_real,Complex.norm_I,mul_one,Real.norm_eq_abs,abs_of_pos Real.pi_pos,mul_pow]
    rw [sq_abs]
lemma masswell_pos {q : ℝ × E4}{i:Axis}(h : ∀ m : ℤ,(m:ℝ)≠(polarPoint q) i) : 0<masswell q:=by
    apply pos_of_mul_pos_right (a:=(q.1:ℝ)^2) ?_ (sq_nonneg q.1)
    simpa [location_at,mul_comm] using location_pos h
lemma mass_near {q : ℝ × E4}(h : q.2≠0)(hp:∀ i,|polarPoint q i|≤3/4) : 0<masswell q:=by
    rcases q with ⟨r,z⟩; by_cases he:r=0
    · subst r; rw [origin_mass]; positivity
    suffices hp':∃ i,∀ m :ℤ,(m:ℝ)≠polarPoint (r,z) i from hp'.elim (fun i h=>masswell_pos h)
    by_contra! hz
    choose m hm using hz
    apply h; ext i
    have hv:= hp i;rw [←hm i] at hv
    have hc : m i=0:= by
      have ha : |(↑(m i):ℝ)| < (1:ℝ):= lt_of_le_of_lt hv (by norm_num)
      have hu: |(m i:ℤ)|<1:= by exact_mod_cast ha
      have he:= abs_lt.mp hu; omega
    have hs: z i=0:=(mul_eq_zero.mp (show r*z i=0 from by change polarPoint (r,z) i=0; rw [←hm i, hc];simp)).resolve_left he
    exact hs
variable {G : Gauge}(a b:Degree G)

def pipe (i j:Axis) (z:E4) : ℂ := -(increment i z)*increment j (-z)
def pipeM (i j :Axis) (z : ℝ×E4) : ℂ:= -(takeoff i z)*takeoff j (z.1,-z.2)
lemma pipe_dilation (i j) (q:ℝ×E4): pipe i j (polarPoint q)= (q.1^2:ℝ) • pipeM i j q:= by
   unfold pipe;rw [show -polarPoint q=polarPoint (q.1,-q.2) from (smul_neg ..).symm]; simp_rw [increment_r];unfold pipeM; simp_rw [RCLike.real_smul_eq_coe_smul (K:=ℂ), smul_eq_mul];push_cast; ring_nf
   exact congr_arg Neg.neg (by ac_rfl)
lemma pipe_smooth (i j): ContDiff ℝ ∞ (pipeM i j):= ((takeoff_smooth i).neg).mul ((takeoff_smooth j).comp ((contDiff_fst).prodMk (contDiff_neg.comp contDiff_snd)))
lemma pipe_origin (i j) (z:E4) :pipeM i j (0,z)=chirp i z * chirp j z:= by simp [pipeM,chirp]

-- angular continuation used as test piece before multiplying damping
def raw := paints (origin a) (origin b) pipe
def tensor (v : ℝ×E4) := paints (origin a) (origin b) (fun i j z=> pipeM i j (v.1,z)) v.2
lemma raw_dilation (v : ℝ×E4):raw a b (polarPoint v)=v.1^2 • tensor a b v:= by
    unfold raw tensor paints origin feather; split_ifs <;> simp [pipe_dilation,RCLike.real_smul_eq_coe_smul (K:=ℂ),smul_eq_mul] <;> ring
lemma tensor_smooth : ContDiff ℝ ∞ (tensor a b):=by
    unfold tensor paints feather; have h i j := pipe_smooth i j; split_ifs<;>(try simp only [Pi.sub_apply, Prod.mk.eta, Pi.smul_apply, origin, zero_sub, sub_zero,sub_self, pow_zero,one_smul,Pi.zero_apply,Pi.neg_apply])
    all_goals
      repeat first | apply ContDiff.sub | apply (show ∀ f : ℝ×E4→ℂ, ContDiff ℝ ∞ f → ContDiff ℝ ∞ (fun x=> - f x) from fun f h=>contDiff_neg.comp h) | apply contDiff_const | apply h
      done -- adjust

def shell (z:E4):ℂ:=hood z * raw a b z/(location z:ℝ)
def sight (v:ℝ×E4):ℂ:= hood (polarPoint v)*tensor a b v/(masswell v:ℝ)
lemma mask_local {A : Type*}[TopologicalSpace A]{f : A→ℝ}{z : A}(hf:ContinuousAt f z)(hx:3/4 < |f z|): (fun x=>tent (f x)) =ᶠ[𝓝 z] (0:A→ℂ):=by
   filter_upwards [((continuous_abs.continuousAt.comp hf).tendsto (le_mem_nhds hx))] with l hl
   exact tent_small hl
lemma polar_nice : ContDiff ℝ ∞ polarPoint:= contDiff_fst.smul contDiff_snd
open Angular
lemma sight_nice : Smooth (sight a b):=by
    rintro ⟨r,x⟩ hx; unfold sight
    by_cases ht:∀ i, |polarPoint (r,x) i|≤3/4
    · simp_rw [show ∀ x:ℂ, ∀ y : ℝ,x / (y:ℂ)=(y)⁻¹ • x from fun x y=> by rw [RCLike.real_smul_eq_coe_smul (K:=ℂ),smul_eq_mul,div_eq_inv_mul];congr 1;exact (Complex.ofReal_inv y).symm]
      refine ((ContDiffAt.inv ?_ (mass_near hx.2 ht).ne').smul (?_:ContDiffAt ℝ ∞ _ _))
      have hv : ContDiff ℝ ∞ masswell := ContDiff.sum fun i _=>(contDiff_norm_sq ℝ).comp (takeoff_smooth i)
      exact hv.contDiffAt
      exact ((hood_smooth.comp polar_nice).mul (tensor_smooth a b)).contDiffAt
    obtain ⟨i,hi⟩:= not_forall.mp ht; refine ContDiffAt.congr_of_eventuallyEq (contDiffAt_const (c:=(0:ℂ))) ?_
    have h := mask_local (hf:=((EuclideanSpace.proj (𝕜:=ℝ) i).continuous.comp polar_nice.continuous).continuousAt) (lt_of_not_ge hi)
    filter_upwards [h] with y hy
    change tent ((EuclideanSpace.proj (𝕜:=ℝ) i) (polarPoint y))=0 at hy
    rw [hood, Finset.prod_eq_zero (Finset.mem_univ i) hy,zero_mul,zero_div]

def shellModel : Model (shell a b) 0 where
   drawing := sight a b
   nice:=sight_nice a b
   sees r x hr h:=by
      change shell a b (polarPoint (r,x)) = r^0 • _
      unfold shell sight; simp only [location_at,raw_dilation]
      push_cast
      simp_rw [RCLike.real_smul_eq_coe_smul (K:=ℂ),smul_eq_mul]; push_cast
      field_simp [Complex.ofReal_ne_zero.mpr hr.ne'] <;> ring_nf <;> ac_rfl
end Band
end YM.PertExtension.LatticePT
