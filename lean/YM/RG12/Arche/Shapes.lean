import YM.RG12.Canonical.Paired
import YM.RG12.Arche.Compose
import YM.Extra.FREE_DETECTOR_ALGEBRA.Columns
/-!
# Actual generic reflected geometries, rational grid-compatible across k
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Arche.Shapes
open Function Filter Set Finset Lattice RG Source Next.Rank.Price
open Work.G08 Next.Rank.East Analysis
open MergeProof.East PhysicalNext.RankCovariance PhysicalNext.InteractingRank.Soft Next.Rank Next.Rank.Tapes
open scoped Topology BigOperators RealInnerProductSpace
variable {G:Gauge}{C:Family G} {d m:ℕ}
open YM.RG12.Desk.Paired
open Extra.FD

-- use y perturbed in ALL spatial directions. generic x and reflected y.
def other (a:Axis)(t:ℝ): E4:= WithLp.toLp 2 fun i=> if i=a then 1 else t
lemma continuous_other (a:Axis): Continuous (other a) := by
   apply Continuous.comp (PiLp.continuous_toLp 2 _)
   apply continuous_pi; intro i; by_cases hi:i=a; simp only [if_pos hi]; exact continuous_const
   simp only [if_neg hi]; exact continuous_id

def compass (a:Axis)(t:ℝ)(s : ℝ) := arrangement a (s • basis a) (s • other a t)
lemma front (a i:Axis)(t s:ℝ) : compass a t s 0 i= if i=a then s else 0:=by
  change s*basis a i= _; by_cases he:i=a<;>simp [basis,he]
lemma rear (a i:Axis)(t s:ℝ) : compass a t s 1 i= if i=a then -s else s*t:=by
  change Ortho.move (Signed.reflect a) (s • other a t) i= _; rw [Signed.mirrored]
  change (if i=a then -(s*(if i=a then 1 else t)) else s*(if i=a then 1 else t))= _; split<;>simp_all
lemma opens (a:Axis)(t s:ℝ)(hs:0<s): compass a t s ∈ conf 2 :=
  clear a _ _ (show 0<s * _ from mul_pos hs (by simp [basis]))
    (show 0<s*(if a=a then (1:ℝ) else t) from mul_pos hs (by simp))
lemma all_directions (a:Axis)(t s:ℝ)(hs:0<s)(ht:t≠0): compass a t s ∈ generic 2:= by
  intro i u v hh; fin_cases u <;> fin_cases v
  · rfl
  · change compass a t s 0 i= compass a t s 1 i at hh; rw [front,rear] at hh; split at hh
    next he=> linarith
    next he=> exact (mul_ne_zero hs.ne' ht hh.symm).elim -- simp zero_mul_eq etc
  · change compass a t s 1 i= compass a t s 0 i at hh; rw [front,rear] at hh; split at hh
    next he=> linarith
    next he=> have hz:s*t≠0:=mul_ne_zero hs.ne' ht; exact (hz hh).elim
  rfl
lemma narrow (a:Axis)(s:ℝ): Tendsto (fun t=> compass a t s) (𝓝 0) (𝓝 (compass a 0 s)):= by
  apply Continuous.tendsto (x:=0)
  change Continuous fun t=> WithLp.toLp 2 (![_,Ortho.motion (Signed.reflect a) (s • other a t)] : Fin 2→E4)
  apply (PiLp.continuous_toLp 2 _).comp; apply continuous_pi; intro i; fin_cases i
  · exact continuous_const
  haveI : IsBoundedSMul ℝ E4:= .of_norm_smul_le NormedSpace.norm_smul_le
  exact (Ortho.motion (Signed.reflect a)).continuous.comp ((continuous_other a).const_smul s)

private lemma other_null (a:Axis): other a 0 = basis a:=by ext i; by_cases hi:i=a<;>simp [other,basis,hi]
lemma flat (a:Axis)(s:ℝ): compass a 0 s=couple (s • basis a) (-(s • basis a)):=by
   unfold compass arrangement couple; rw [other_null]
   have he : Ortho.move (Signed.reflect a) (s • basis a) = -(s • basis a):=by
      ext i; rw [Signed.mirrored]; change (if _ then -(s*basis a i) else s*basis a i) = -(s*basis a i)
      by_cases hi:i=a<;> simp [hi, basis]
   rw [he]
-- `face` is full Ortho reflection on tensors. Here realize with available Signed generator.
lemma facing (a:Axis)(s:ℝ)(hs:s≠0): face (s • basis a - -(s • basis a))=Signed.reflect a:=by
   apply Ortho.ext _ _; intro y; rw [face_apply]; ext i; rw [Signed.mirrored]
   have ht : s • basis a - -(s • basis a)=(2*s) • basis a:=by module
   rw [ht, real_inner_smul_left]
   have hf : ⟪basis a,y⟫ = y a := by rw [← real_dot]; simp [basis,ite_mul]
   rw [hf]
   change y i - (2*rr _*(2*s*y a) * ((2*s)*basis a i))=_
   have hv:‖basis a‖=(1:ℝ):= by simp [basis]
   have he : rr ((2*s) • basis a) * (2*s)^2=1:=by unfold rr;rw [norm_smul,Real.norm_eq_abs,hv,mul_one,sq_abs]; field_simp
   by_cases hi:i=a
   · subst i; rw [if_pos rfl, show basis a a=1 from by simp [basis]]; nlinarith [show rr ((2*s) • basis a) * (2*s)^2 * y a= y a from by rw [he,one_mul]]
   rw [if_neg hi,show basis a i=0 from by simp [basis,hi]]; ring

-- one scope; across tests may dilate by a natural (uniform costs for each fixed dilation).
def scope (a:Axis)(N:ℕ) : Scope 1 where
  weight _:=1
  axis _:=a
  incoming _:=basis a
  reflecting _:=other a ((N:ℝ)⁻¹)
  ahead _:=by simp [basis]
  stays _:=by simp [other]

def bearing (a:Axis)(t:ℝ) := compass a t 1
lemma scaling (a:Axis)(s t:ℝ): compass a t s=s • bearing a t := by
   ext j i; fin_cases j
   · change compass _ _ _ 0 i=s*compass a t 1 0 i; rw [front,front]; split<;>simp
   change compass _ _ _ 1 i=s*compass a t 1 1 i; rw [rear,rear]; split<;>simp
lemma stamped (a:Axis)(N:ℕ)(s:ℝ): configs (scope a N) s 0= s • bearing a (N:ℝ)⁻¹:= scaling a ..

def ticks (N:ℕ)(μ:ℝ):ℝ:= N*Nat.ceil (μ/N) -- use on μ≥1 and N≥1
def ratio (N:ℕ) (μ:ℝ):= ticks N μ/μ
def berth(a:Axis)(N n:ℕ)(μ:ℝ): Fin 2→ Cover := ![fun i=> if i=a then (n*N*Nat.ceil (μ/N):ℤ) else 0,fun i=> if i=a then -(n*N*Nat.ceil (μ/N):ℤ) else (n*Nat.ceil (μ/N))]
lemma ticketed (N:ℕ)(μ:ℝ)(hμ:0<μ)(hN:0<N): ratio N μ∈ Icc 1 (1+(N:ℝ)/μ):=by
   have ht:0<(N:ℝ):= Nat.cast_pos.mpr hN
   unfold ratio ticks; constructor
   · rw [le_div_iff₀ hμ,one_mul,mul_comm]; exact (div_le_iff₀ ht).mp (Nat.le_ceil _)
   rw [div_le_iff₀ hμ]; have hq:= Nat.ceil_lt_add_one (show 0 ≤ μ/(N:ℝ) from (div_pos hμ ht).le)
   field_simp at *; linarith
lemma datedC (a:Axis)(N n:ℕ)(μ c:ℝ)(hN:0<N) : Extraction.tag c (berth a N n μ) = compass a (N:ℝ)⁻¹ (c * ticks N μ*n):=by
   have ht:0<(N:ℝ):=Nat.cast_pos.mpr hN
   ext j i; fin_cases j
   · change _=compass _ _ _ 0 i;rw [front]
     change c*((↑(if i=a then (n*N*Nat.ceil (μ/N):ℤ) else 0):ℝ))=_; split
     · unfold ticks; push_cast; ring
     norm_num
   change _=compass _ _ _ 1 i;rw [rear]
   change c*((↑(if i=a then -(n*N*Nat.ceil (μ/N):ℤ) else (n*Nat.ceil (μ/N))):ℝ))=_; split
   · unfold ticks; push_cast; ring
   unfold ticks; push_cast; field_simp
lemma dated (a:Axis)(N n:ℕ)(μ:ℝ)(hN:0<N) : Extraction.tag μ⁻¹ (berth a N n μ) = (ratio N μ*n) • bearing a (N:ℝ)⁻¹:=by
   rw [← scaling]; unfold ratio; rw [div_eq_inv_mul]; exact datedC _ _ _ _ _ hN
lemma gears (C:Family G) (a:Axis)(N n k:ℕ)(μ:ℝ)(hN:0<N): Extraction.Order.grid C k (berth a N n μ)=(C.S.a k * ticks N μ*n) • bearing a (N:ℝ)⁻¹:=by
    rw [← scaling]; exact datedC _ _ _ _ _ hN
/-- Entire shape ray with bounded sampling overshoot. -/
def province (a:Axis)(N n:ℕ) : Set (Points 2) := (fun s:ℝ=>s • bearing a (N:ℝ)⁻¹) '' Icc 1 (2*n)
lemma thicket (a:Axis)(N n:ℕ): IsCompact (province a N n) ∧ province a N n ⊆ conf _:= by
   haveI : IsBoundedSMul ℝ (Points 2):= .of_norm_smul_le NormedSpace.norm_smul_le
   constructor
   · exact isCompact_Icc.image (by fun_prop)
   rintro _ ⟨s,hs,rfl⟩; change s • _ ∈ _; rw [← scaling]; exact opens a _ s (zero_lt_one.trans_le hs.1)

lemma still_tree (a:Axis) (N n:ℕ)(μ:ℝ)(hN:0<N)(hn:0<n)(hμ:N≤ μ): let P:= Extraction.tag μ⁻¹ (berth a N n μ); P∈ province a N n ∧ P∈ generic _:=by
   intro P; have h:(0:ℝ)<N:=Nat.cast_pos.mpr hN; have hh:(0:ℝ)<n:= Nat.cast_pos.mpr hn
   have hk: 0 < μ:=h.trans_le hμ; have hi:=ticketed N μ hk hN
   have ht: 1 ≤ ratio N μ := hi.1; have hv: ratio N μ ≤ 2:=by have he:= (div_le_one hk).mpr hμ; have hv:ratio N μ≤1+(N:ℝ)/μ:=hi.2; linarith
   unfold P; rw [dated _ _ _ _ hN]; constructor
   · exact ⟨_,Set.mem_Icc.mpr ⟨one_le_mul_of_one_le_of_one_le ht (Nat.one_le_cast.mpr hn), mul_le_mul_of_nonneg_right hv hh.le⟩,rfl⟩
   rw [← scaling]; exact all_directions a _ _ (mul_pos (zero_lt_one.trans_le ht) hh) (inv_ne_zero h.ne')
end YM.RG12.Arche.Shapes
