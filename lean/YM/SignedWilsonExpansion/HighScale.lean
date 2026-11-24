import YM.MS.Port.Spire

/-! One-loop scale response on the archive used by FVA2. We start
by characterising time-constant kernel components. Time here is the
logarithmic **heat** length; it is not the log renormalization mass. -/
set_option autoImplicit false
noncomputable section
open Function Filter Set Finset
namespace YM.SignedWilsonExpansion.HighScale
open MS MS.Plane MS.Koszul MS.Landau MS.Landau.Detect MS.Port MS.Pearl MS.Rake MS.High
open MS.Logarithm MS.Alps
open scoped Topology BigOperators ContDiff

-- smooth and scale-equivariant momentum symbols, with a shared polynomial degree in the stamp
structure Rays (f : ℝ → ℝ → ℂ) (d : ℤ) : Prop where
  scale (y z a : ℝ) : f y a = (Real.exp z)^(-d) • f (y+z) (Real.exp z * a)
  cap : Logarithm.Ready f
  smooth (y : ℝ) : ContDiff ℝ ∞ (f y)

namespace Rays
variable {f : ℝ → ℝ → ℂ} {d : ℤ} (H : Rays f d)
include H
lemma deriv_shift (j : ℕ) (y z a : ℝ) :
    iteratedDeriv j (f y) a = (Real.exp z)^(-d+(j:ℤ)) • iteratedDeriv j (f (y+z)) (Real.exp z * a) := by
  rw [show f y = (Real.exp z)^(-d) • (fun a : ℝ=> f (y+z) (Real.exp z * a)) from funext (H.scale y z),
    iteratedDeriv_const_smul_field, iteratedDeriv_comp_const_smul
      ((H.smooth (y+z)).of_le (by exact_mod_cast le_top)),smul_smul,
    zpow_add₀ (Real.exp_pos _).ne', zpow_natCast]

lemma scaled_cost (j : ℕ) : ∃ N:ℕ,∀ y z a:ℝ, iteratedDeriv j (f y) a =
     ∑ i∈Finset.range N, (MS.Alps.amount (((-d+j:ℤ):ℝ):ℂ) z *((plate N i).eval (y+z):ℝ)) *
       iteratedDeriv j (f (i:ℝ)) (Real.exp z * a) := by
  obtain ⟨N,hN⟩:= H.cap
  refine ⟨N,?_⟩
  intro y z a
  rw [H.deriv_shift j y z a, interpret hN (y+z), Logarithm.evaluate, iteratedDeriv_sum]
  · simp_rw [iteratedDeriv_const_smul_field]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl; intro i _
    simp only [Complex.real_smul]
    rw [show ((((Real.exp z)^(-d+j:ℤ)):ℝ):ℂ)=MS.Alps.amount ((((-d+j:ℤ):ℝ)):ℂ) z from ?_, mul_assoc]
    rw [Complex.ofReal_intCast,τ_amt]
  intro i hi
  exact (((H.smooth (i:ℝ)).of_le (show (j:ℕ∞ω) ≤ ∞ from by exact_mod_cast le_top)).contDiffAt.const_smul ((plate N i).eval (y+z))) 

lemma high (j : ℕ) (p : d < j) (y a : ℝ) : iteratedDeriv j (f y) a=0:= by
  obtain ⟨N,bill⟩:= H.scaled_cost j
  have hp (i : ℕ) : Tendsto (fun z:ℝ =>
      (MS.Alps.amount (((-d+j:ℤ):ℝ):ℂ) z *((plate N i).eval (y+z):ℝ)) * iteratedDeriv j (f (i:ℝ)) (Real.exp z * a)) atBot (𝓝 0):= by
    have h : 0 < ((-d+j:ℤ):ℝ):= by exact_mod_cast (by omega : 0 < -d+(j:ℤ))
    have hp:= MS.Pearl.pos_exp (plate N i) y h
    have hs:= (H.smooth (i:ℝ)).continuous_iteratedDeriv j (by exact_mod_cast le_top)
    have hV: Tendsto (fun z=> iteratedDeriv j (f (i:ℝ)) (Real.exp z * a)) atBot (𝓝 (iteratedDeriv j (f (i:ℝ)) (0*a))) :=
      (hs.tendsto _).comp (Real.tendsto_exp_atBot.mul_const a)
    simpa only [zero_mul] using hp.mul hV
  have hh:= tendsto_finsetSum (Finset.range N) (fun i _=> hp i)
  simp only [sum_const_zero,← bill y] at hh
  exact tendsto_nhds_unique tendsto_const_nhds hh

lemma low (j : ℕ) (p : (j:ℤ) < d) (y : ℝ) : iteratedDeriv j (f y) 0=0:= by
  obtain ⟨N,bill⟩:= H.scaled_cost j
  have hp (i : ℕ) : Tendsto (fun z:ℝ =>
      (MS.Alps.amount (((-d+j:ℤ):ℝ):ℂ) z *((plate N i).eval (y+z):ℝ)) * iteratedDeriv j (f (i:ℝ)) (Real.exp z * 0)) atTop (𝓝 0):= by
    have h : ((-d+j:ℤ):ℝ)<0:= by exact_mod_cast (by omega : -d+(j:ℤ)<0)
    simpa only [mul_zero,zero_mul] using (MS.Pearl.neg_exp (plate N i) y h).mul_const (iteratedDeriv j (f (i:ℝ)) 0)
  have hh:= tendsto_finsetSum (Finset.range N) (fun i _=> hp i)
  simp only [sum_const_zero,← bill y] at hh
  exact tendsto_nhds_unique tendsto_const_nhds hh

lemma subzero (h : d<0) (y : ℝ) : f y=0:=by
  ext1 x
  simpa only [iteratedDeriv_zero,Pi.zero_apply] using H.high 0 (by omega) y x

lemma fixed (j : ℕ) (p : d=(j:ℤ)) (y z : ℝ) : iteratedDeriv j (f y) 0=iteratedDeriv j (f z) 0:= by
  simpa only [p,neg_add_cancel,zpow_zero,one_smul,mul_zero,add_sub_cancel] using H.deriv_shift j y (z-y) 0

lemma isJet (j : ℕ) (p : d=(j:ℤ)) (y a : ℝ) : f y a=a^j • reading j (f y) := by
  let g (t : ℝ) := t^j • reading j (f y)
  have hg: ContDiff ℝ ∞ g := by unfold g; fun_prop
  have dg (n : ℕ) (x : ℝ) : iteratedDeriv n g x= ((j.descFactorial n:ℝ)*x^(j-n)) • reading j (f y) := by
    dsimp only [g]
    rw [iteratedDeriv_smul_const (by fun_prop),iteratedDeriv_pow]
  let F:= f y - g
  have Hf: ContDiff ℝ ∞ F := (H.smooth y).sub hg
  have du (n : ℕ) (x : ℝ) : iteratedDeriv n F x=iteratedDeriv n (f y) x-iteratedDeriv n g x:=
    iteratedDeriv_sub ((H.smooth y).contDiffAt.of_le (by exact_mod_cast le_top)) (hg.contDiffAt.of_le (by exact_mod_cast le_top))
  have rest (n : ℕ) (hn : n≤j+1) (x : ℝ) : iteratedDeriv n F x=0 := by
    induction hn using Nat.decreasingInduction generalizing x with
    | self => simp [du,H.high (j+1) (by omega) y,dg]
    | of_succ k hk ih=>
      rw [is_const_of_deriv_eq_zero (Hf.differentiable_iteratedDeriv k (by exact_mod_cast (show (k:ℕ∞)<⊤ from WithTop.coe_lt_top _))) (fun z=>by rw [← iteratedDeriv_succ]; exact ih z) x 0,du,dg]
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with h|h
      · simp [H.low k (by omega) y,show j-k≠0 from by omega]
      rw [h]; simp only [Nat.sub_self,pow_zero,mul_one,Nat.descFactorial_self, reading]
      rw [smul_smul,mul_inv_cancel₀ (by positivity),one_smul,sub_self]
  have := rest 0 (by omega) a
  exact sub_eq_zero.mp (by simpa [F,g] using this)

lemma independent (y z : ℝ) : f y=f z:=by
  by_cases p : d < 0
  · rw [H.subzero p, H.subzero p]
  have hn:d=(d.toNat:ℤ):=by omega
  funext a
  rw [H.isJet _ hn, H.isJet _ hn, reading, H.fixed _ hn y z]
end Rays
open MS.Plane.Wire MS.Plane.Domain
variable {G : Gauge} {d : ℤ} {r : ℕ}

lemma dilate_line (s : ℝ) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : Wire (Branch G Axis) E FourP) (x:E) :
    sr s (sail w x)= sail w ((Real.exp s) • x) := by
  induction w with
  | nil=>rfl
  | cons u w ih=> simp only [sr,sail_cons,List.map_cons] at *; rw [map_smul,ih]

/-- Scale condition on a fixed valence. -/
def Covariant (f : Reading G) (b : Bool) (r : ℕ) (d : ℤ) := ∀ (y t s:ℝ) (w:Legs (Lane4 G)), Course b w → w.length=r →
      f (y,t) w = shift d s (f (y+s,t-s)) w
lemma Covariant.line {f : Reading G} {b : Bool} (H : Covariant f b r d) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : Wire (Branch G Axis) E FourP)(hc : Course b w)(hr : w.length=r)(y t s:ℝ) (x:E) :
    fieldVal (f (y,t)) w x = (Real.exp s)^(fieldDim wfield w-d) • fieldVal (f (y+s,t-s)) w ((Real.exp s) • x):=by
  unfold fieldVal
  rw [H y t s _ (sail_course x hc) (by simpa using hr),Port.shift,dilate_line]
  simp only [MS.Latch.pitch, sail_dim]; rfl

/-- The symbol on this fixed-valence sector has become independent of heat-time. -/
structure Static (f : Reading G) (r : ℕ) (d : ℤ) (b : Bool) : Prop where
  time (y t t' :ℝ)(w:Legs (Lane4 G)): Course b w → w.length=r → f (y,t) w=f (y,t') w
  scales : Covariant f b r d
  smooth (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (w:Wire (Branch G Axis) E FourP):
    Course b w → w.length=r → ∀ t:Clock ℝ, ContDiff ℝ ∞ (fieldVal (f t) w)
  size (t : ℝ)(w:Legs (Lane4 G)): Course b w → w.length=r →
    Ready (fun y=> fieldVal (f (y,t)) (ray w))

namespace Static
variable {f : Reading G}{b : Bool}(H:Static f r d b)
include H
lemma rays (t:ℝ)(w:Legs (Lane4 G))(hc:Course b w)(hr:w.length=r): Rays (fun y=> fieldVal (f (y,t)) (ray w)) (d-fieldDim wfield w) := by
  have hh: (ray w).length=r:=by simpa using hr
  refine ⟨?_,H.size t w hc hr,fun y=>H.smooth ℝ (ray w) (ray_course hc) hh (y,t)⟩
  intro y s a
  rw [H.scales.line _ (ray_course hc) hh y t s a]
  have hc': Course b (sail (ray w) (Real.exp s • a)):= sail_course _ (ray_course hc)
  unfold fieldVal
  rw [H.time _ (t-s) t _ hc' (by simpa using hr), ray_dim, neg_sub]; rfl

lemma same (y z t t':ℝ)(w:Legs (Lane4 G))(hc:Course b w)(hr:w.length=r): f (y,t) w=f (z,t') w:= by
  rw [H.time y t t' w hc hr]
  simpa [fieldVal] using congr_fun ((H.rays t' w hc hr).independent y z) (1:ℝ)

lemma form (y t : ℝ){E : Type}[NormedAddCommGroup E][NormedSpace ℝ E](w : Wire (Branch G Axis) E FourP)
    (hc : Course b w)(hr : w.length=r): Shape (fieldVal (f (y,t)) w) (d-fieldDim wfield w):=by
  let i:=fieldDim wfield w
  let rad(x:E):=H.rays t (sail w x) (sail_course x hc) (by simpa using hr) -- prop proof
  by_cases hs: d < i
  · suffices q:fieldVal (f (y,t)) w=0 by rw [q]; exact form_zero _
    funext x
    have u:=congr_fun ((rad x).subzero (by rw [sail_dim]; omega) y) (1:ℝ)
    dsimp only [fieldVal] at u ⊢; rw [ray_sail] at u; exact u
  let j:ℕ:=(d-i).toNat; have hj:d-fieldDim wfield w=(j:ℤ):=by dsimp only [j]; omega
  have cost:= H.smooth E w hc hr (y,t)
  suffices he: fieldVal (f (y,t)) w=Tensor.diagonal (Tensor.coeff (fieldVal (f (y,t)) w) j 0) by rw [he]; exact form_diag _ _ hj
  funext x
  rw [show Tensor.diagonal _ _=torch j (f (y,t)) (sail w x) from (lit _ w cost x).symm,torch_at]
  have hu:= (rad x).isJet j ((by rw [sail_dim]; exact hj)) y 1
  change f (y,t) (sail w x)=_
  simp only [one_pow,one_smul,fieldVal,ray_sail] at hu; exact hu

lemma over (y t : ℝ)(w : Legs (Lane4 G))(hc : Course b w)(hr : w.length=r)(e:d < fieldDim wfield w) : f (y,t) w=0 := by
  have hu:= congr_fun ((H.rays t w hc hr).subzero (by omega) y) (1:ℝ)
  change _=(0:ℂ) at hu
  simpa only [fieldVal,ray_sail] using hu
end Static

open MS.Outlook MS.Emit
variable {n k : ℕ} {f D : Reading G} {b : Bool}

lemma static_of (speed : ∀ (y t : ℝ) (w:Legs (Lane4 G)), Course b w → w.length=r → HasDerivAt (fun t=> f (y,t) w) 0 t)
    (cov : Covariant f b r d) (smooth : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (w:Wire (Branch G Axis) E FourP), Course b w → w.length=r → ∀ t:Clock ℝ, ContDiff ℝ ∞ (fieldVal (f t) w))
    (poly : High.stamp f) : Static f r d b := by
  refine ⟨?_,cov,smooth,?_⟩
  · intro y t u w hc hw
    exact is_const_of_deriv_eq_zero (fun t=> (speed y t w hc hw).differentiableAt) (fun t=> (speed y t w hc hw).deriv) t u
  intro t w _ _
  let L:(ℝ → Law G) →ₗ[ℝ] (ℝ → ℂ) := LinearMap.pi fun a=>
    (LinearMap.proj (sail (ray w) a) : Law G →ₗ[ℝ] ℂ) ∘ₗ (LinearMap.proj t)
  exact Ready.linear poly L

lemma timeJet (w:Legs (Lane4 G)) (track : Track b f D (ray w)) (hc : Course b w) (y t : ℝ) (a:ℝ) (j:ℕ) :
    HasDerivAt (fun t' => iteratedDeriv j (fieldVal (f (y,t')) (ray w)) a)
      (iteratedDeriv j (fieldVal (D (y,t)) (ray w)) a) t:= by
  let L : (ℝ [×j]→L[ℝ] ℂ) →L[ℝ] ℂ:= ContinuousMultilinearMap.apply ℝ _ ℂ (fun _=>1)
  simp_rw [iteratedDeriv_eq_iteratedFDeriv]
  exact L.hasFDerivAt.comp_hasDerivAt t ((track (ray_course hc)).2.2 y t a j)

lemma time_derivative (w:Legs (Lane4 G))(track : Track b f D (ray w))(hc : Course b w)(y t:ℝ) :
    HasDerivAt (fun t=> f (y,t) w) (D (y,t) w) t:= by
  simpa only [iteratedDeriv_zero, fieldVal, ray_sail] using timeJet w track hc y t 1 0

lemma quiet_static (A: Flats G)(hw:Host A n) (_nz:b=true → 0< r) (D:Reading G)
    (flow:∀(w:Legs (Lane4 G)), w.length=r → Track b (four n A) D (ray w))
    (kill:∀ s (w:Legs (Lane4 G)), Course b w → w.length=r → D s w=0) : Static (four n A) r n b := by
  refine static_of ?_ (fun _ _ _ _ _ _=> congr_fun (Bx4 hw) _) ?_ (plant hw)
  · intro _ _ w hc hr
    rw [← kill (_,_) w hc hr]
    exact time_derivative w (flow w hr) hc _ _
  intro E i j w _ _ s; exact Outlook.hair hw (n:=0) w

lemma shear_jet (H : Covariant f b r d) (w:Legs (Lane4 G))(hc : Course b w)(hr:w.length=r)
    (hf : ∀ t : Clock ℝ, ContDiff ℝ ∞ (fieldVal (f t) (ray w)))(y t z a:ℝ) (j:ℕ) :
    iteratedDeriv j (fieldVal (f (y,t)) (ray w)) a =
    Real.exp z^(fieldDim wfield w - d + j) • iteratedDeriv j (fieldVal (f (y+z,t-z)) (ray w)) (Real.exp z*a) := by
  let g:=fieldVal (f (y+z,t-z)) (ray w)
  have he:fieldVal (f (y,t)) (ray w) = Real.exp z^(fieldDim wfield w-d) • (fun a:ℝ=>g (Real.exp z*a)):= by
    funext x
    simpa only [g,ray_dim, Pi.smul_apply,smul_eq_mul] using H.line (ray w) (ray_course hc) ((ray_len w).trans hr) y t z x
  rw [he,iteratedDeriv_const_smul_field, iteratedDeriv_comp_const_smul (f:=g) ((hf _).of_le (by exact_mod_cast le_top)),smul_smul, zpow_add₀ (Real.exp_pos _).ne', zpow_natCast]

lemma shear_torch (H : Covariant f b r d) (w:Legs (Lane4 G))(hc : Course b w)(hr:w.length=r)(i:ℕ)
    (h:fieldDim wfield w+i=d)
    (hf : ∀ t : Clock ℝ, ContDiff ℝ ∞ (fieldVal (f t) (ray w)))(y t z:ℝ) :
    torch i (f (y,t+z)) w = torch i (f (y+z,t)) w := by
  change ((i.factorial:ℝ)⁻¹) • iteratedDeriv i (fieldVal (f (y,t+z)) (ray w)) 0 = ((i.factorial:ℝ)⁻¹) • iteratedDeriv i (fieldVal (f (y+z,t)) (ray w)) 0
  rw [shear_jet H w hc hr hf y (t+z) z, add_sub_cancel_right,mul_zero,show fieldDim wfield w-d+i=0 from by omega, zpow_zero,one_smul]

lemma shear_derivative (H : Covariant f b r d) (w:Legs (Lane4 G))(hc : Course b w)(hr:w.length=r)(i:ℕ)
    (h:fieldDim wfield w+i=d) (track : Track b f D (ray w)) (y t:ℝ): HasDerivAt (fun y=> torch i (f (y,t)) w) (torch i (D (y,t)) w) y:=by
  have he (z:ℝ): torch i (f (z,t)) w=torch i (f (y,t+(z-y))) w:= by simpa only [add_sub_cancel] using (shear_torch H w hc hr i h ((track (ray_course hc)).1) y t (z-y)).symm
  simp_rw [funext he] -- doesn't rewrite by simp? 
  have ht : HasDerivAt (fun x=> torch i (f (y,x)) w) (torch i (D (y,t)) w) t:=
    (timeJet w track hc y t 0 i).const_smul _
  have hp : HasDerivAt (fun x:ℝ=> t+(x-y)) 1 y:= ((hasDerivAt_id' y).sub_const y).const_add t
  have hx : HasDerivAt (fun x:ℝ=>torch i (f (y,t+(x-y))) w) ((1:ℝ) • torch i (D (y,t)) w) y:=
    HasDerivAt.scomp (h:=fun x:ℝ=>t+(x-y)) (g₁:=fun x:ℝ=>torch i (f (y,x)) w) y (by simpa only [sub_self,add_zero] using ht) hp
  simpa only [one_smul] using hx
end YM.SignedWilsonExpansion.HighScale
