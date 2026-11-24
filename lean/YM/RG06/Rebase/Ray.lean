import YM.Next.RANK.Peano
import YM.Next.FOUNDATIONS.LinkBounds

/-!
# Rebase tools I : moving-center finite Taylor comparisons

Work with qualitative, finite-witness constants. The whole point is identifying the unmasked
operator and its projected translation exactly; a power-counting/all-orders error in a *density*
is quite different. `along` and `swirl` use true derivatives via the pinned calculus, and `peel`
tests equality by uniqueness of finite Peano coefficients (even for negative ray t).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG06.Rebase
open Function Set Tensor Filter Asymptotics Metric
open scoped Topology BigOperators ContDiff
variable {E F:Type*} [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]{k:ℕ}

lemma along {f:E4→F} {x:E4} (h:ContDiffAt ℝ k f x)(y:E4):
  iteratedDeriv k (fun t:ℝ=> f (x+t • y)) 0=diagonal (iteratedFDeriv ℝ k f x) y:=by
  let g:E4→F:=fun z=>f (x+z)
  have he:ContDiffAt ℝ k g 0:=(show ContDiffAt ℝ k f (x+0) by simpa using h).comp _ (contDiffAt_const.add contDiffAt_id)
  have hk: iteratedFDeriv ℝ k g 0=iteratedFDeriv ℝ k f x:=by unfold g; rw [iteratedFDeriv_comp_add_left,add_zero]
  change iteratedDeriv k (fun t:ℝ=>g (t • y)) 0=_; rw [Next.Foundations.iteratedDeriv_on_line he, hk]

-- general E (Next.Foundations lemma quantifies?)
lemma ray_at {f:E→F}(x y:E)(u:ℝ)(h:ContDiffAt ℝ k f (x+u • y)):
    iteratedDeriv k (fun t:ℝ=>f (x+t • y)) u= diagonal (iteratedFDeriv ℝ k f (x+u • y)) y:=by
  let z:=x+u • y
  let g:E→F:=fun w=> f (z+w)
  let U(t:ℝ):= f (x+t • y)
  have hf: (fun t:ℝ=> U (u+t))=fun t=> g (t • y):= by funext t; simp only [U,g,z,add_smul, add_assoc]
  have he: ContDiffAt ℝ k g 0:=(show ContDiffAt ℝ k f (z+0) by simpa only [z,add_zero] using h).comp _ (contDiffAt_const.add contDiffAt_id)
  have hp:=congr_fun (iteratedDeriv_comp_const_add k U u) (0:ℝ)
  rw [hf] at hp; change _ = iteratedDeriv k U (u+0) at hp; rw [add_zero] at hp
  change iteratedDeriv k U u= _
  rw [← hp,YM.Next.Foundations.iteratedDeriv_on_line he y, show iteratedFDeriv ℝ k g 0=iteratedFDeriv ℝ k f (x+u • y) from (by unfold g; rw [iteratedFDeriv_comp_add_left,add_zero])]

/-- Converse Peano at a point through any finite tested order. -/
lemma peel {f g:ℝ→E}(hF:ContDiffAt ℝ k f 0)(hG:ContDiffAt ℝ k g 0)
    (h:(f-g)=o[𝓝 0] fun t:ℝ=>t^k):∀ i≤k,iteratedDeriv i f 0=iteratedDeriv i g 0:=by
  let T(a:ℝ→E)(i:ℕ):=(i.factorial:ℝ)⁻¹ • iteratedDeriv i a 0
  have Hc := (Next.Rank.Spindle.taylor_data hF); have Hd:=Next.Rank.Spindle.taylor_data hG
  have hx := show ((f-Next.Rank.Spindle.Dims k (T f))=o[𝓝 0] fun t:ℝ=> t^k) from Hc
  have hy := show ((g-Next.Rank.Spindle.Dims k (T g))=o[𝓝 0] fun t:ℝ=> t^k) from Hd
  have he:= h.sub (hx.sub hy)
  have hz: Next.Rank.Spindle.asym k (Next.Rank.Spindle.Dims k (T f-T g)) := by
    rw [Next.Rank.Spindle.dims_sub]; unfold Next.Rank.Spindle.asym; -- abel equality
    have hv:(f-g)-((f-Next.Rank.Spindle.Dims k (T f))-(g-Next.Rank.Spindle.Dims k (T g)))=Next.Rank.Spindle.Dims k (T f)- Next.Rank.Spindle.Dims k (T g):=by abel
    exact hv ▸ he
  intro i hi
  have hv:= Next.Rank.Spindle.retreat k hz i hi
  exact smul_right_injective _ (show ((i.factorial:ℝ)⁻¹)≠0 by positivity) (sub_eq_zero.mp hv)
lemma peel_power {f g:ℝ→E}(hF:ContDiffAt ℝ k f 0)(hG:ContDiffAt ℝ k g 0)
    (h:∃ C:ℝ, ∀ᶠ t in 𝓝 (0:ℝ), ‖f t-g t‖≤ C*‖t‖^(k+1)) :∀ i≤k,iteratedDeriv i f 0=iteratedDeriv i g 0:=by
  obtain ⟨C,h⟩:=h; exact peel hF hG (Next.Rank.Spindle.error_power C h)

/-- Local moving-center bound: all displacements allowed (signs and no origin-line condition).
Smoothness of F at origin through `k+1` only. All terms on the left are ambient ordinary
Taylor coefficients. This identifies previous finite orders via `peel` without either
weakening for anisotropic dilation or assuming analyticity of a moved gauge.
-/
lemma swirl (k:ℕ) (x:E) (f:E→F) (h:ContDiffAt ℝ (↑(k+1):WithTop ℕ∞) f x):
    ∃ r:ℝ, 0<r ∧ ∃ C:ℝ, 0≤C ∧ ∀ y v:E, ‖y-x‖+‖v‖<r →
     ‖f (y+v) - ∑ i∈Finset.range (k+1), diagonal (coeff f i y) v‖ ≤ C*‖v‖^(k+1) := by
  -- local bound for ambient highest derivative
  have hf := (h.iteratedFDeriv_right (m:=(0:ℕ)) (i:=k+1) (by simp)).continuousAt
  let C:= ‖iteratedFDeriv ℝ (k+1) f x‖+1
  have hb : ∀ᶠ z in 𝓝 x, ‖iteratedFDeriv ℝ (k+1) f z‖< C:=(hf.norm.tendsto).eventually (Iio_mem_nhds (by dsimp [C]; linarith))
  obtain ⟨r,hr,ht⟩ := Metric.mem_nhds_iff.mp (hb.and (h.eventually (by simp)))
  have hy:C≥0:=by unfold C; positivity
  refine ⟨r,hr,C,hy,fun y v hd=>?_⟩
  let A(t:ℝ):= y+t • v
  let n:=k+1
  have hm(t:ℝ)(ha:t∈Icc (0:ℝ) 1): A t∈Metric.ball x r:=by
    rw [mem_ball,dist_eq_norm,show A t-x=y-x+t • v by unfold A; abel]; apply lt_of_le_of_lt (norm_add_le ..)
    apply lt_of_le_of_lt _ hd; rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ha.1]; gcongr
    exact mul_le_of_le_one_left (norm_nonneg _) ha.2
  have hv(t:ℝ)(ha:t∈Icc (0:ℝ) 1)(i:ℕ)(hi:i≤n): ContDiffAt ℝ i f (A t):=(ht (hm t ha)).2.of_le (by exact_mod_cast hi)
  have hw(t:ℝ)(ha:t∈Icc (0:ℝ) 1)(i:ℕ)(hi:i≤n):ContDiffAt ℝ i (f ∘ A) t:= (hv t ha i hi).comp t (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const))
  have he(t:ℝ)(ha:t∈Icc (0:ℝ) 1)(i:ℕ)(hi:i≤n): iteratedDerivWithin i (f∘A) (Icc 0 1) t=diagonal (iteratedFDeriv ℝ i f (A t)) v := by
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (zero_lt_one)) (hw t ha i hi) ha]; exact ray_at y v t (hv t ha i hi)
  have hC(t:ℝ)(ha:t∈Icc (0:ℝ) 1): ‖iteratedDerivWithin n (f∘A) (Icc 0 1) t‖ ≤ C*‖v‖^n := by
    let T:= iteratedFDeriv ℝ n f (A t)
    rw [he t ha n le_rfl]
    have hZ:=T.le_opNorm (fun _=>v)
    apply hZ.trans
    rw [Finset.prod_const]; refine mul_le_mul ?_ ?_ ?_ hy
    · exact (ht (hm t ha)).1.le
    · rw [Finset.card_univ,Fintype.card_fin]
    positivity
  have hp :ContDiffOn ℝ (k+1) (f ∘ A) (Icc 0 1):=by
     have ht':ContDiffOn ℝ ((k+1:ℕ):WithTop ℕ∞) (f ∘ A) (Icc 0 1):=fun t ha=>(hw _ ha n le_rfl).contDiffWithinAt
     simpa only [Nat.cast_add,Nat.cast_one] using ht'
  have hB:=taylor_mean_remainder_bound (n:=k) (x:=1) zero_le_one hp (right_mem_Icc.mpr zero_le_one) hC
  simp_rw [Function.comp_apply,A,one_smul] at hB
  rw [← show taylorWithinEval (f ∘ A) k (Icc 0 1) 0 1 = ∑ i∈Finset.range (k+1), diagonal (coeff f i y) v from (by
    rw [taylor_within_apply]; refine Finset.sum_congr rfl fun i hi=>?_; rw [he 0 (left_mem_Icc.mpr zero_le_one) i (Finset.mem_range.mp hi).le]; simp only [sub_zero,one_pow,mul_one,A,zero_smul,add_zero,coeff]; rfl)]
  apply hB.trans
  rw [sub_zero,one_pow,mul_one]; apply div_le_self _ _
  · positivity
  exact_mod_cast Nat.factorial_pos k

/-- Varying parameters through horizontal jets. No assertion of uniformity outside
some (qualitatively chosen) parameter neighborhood. Supplied `ContDiffAt` is *joint*. -/
lemma surf {F':ℝ×E→F} (q:ℝ→E) {k:ℕ}
    (h : ContDiffAt ℝ (↑(k+1):WithTop ℕ∞) F' (0,q 0))
    (hQ : ContinuousAt q 0)
    (hF : ∀ᶠ z in 𝓝 (q 0), ∀ i ≤ k, iteratedDeriv i (fun t:ℝ=>F' (t,z)) 0=0):
    ∃ C:ℝ, ∀ᶠ t in 𝓝 0, ‖F' (t,q t)‖ ≤ C*‖t‖^(k+1):=by
  let u:E→ℝ×E:=fun z=>(0,z)
  let v:ℝ→ℝ×E:=fun t=>(t,0)
  have ht : Tendsto (u∘q) (𝓝 0) (𝓝 ((u∘q) 0)):= ((show Continuous u from by fun_prop).continuousAt.comp hQ)
  have he : Tendsto v (𝓝 0) (𝓝 (v 0)):=(show Continuous v from by fun_prop).continuousAt
  obtain ⟨R,hR,C,_,hb⟩:= swirl k (0,q 0) F' h
  refine ⟨C,?_⟩
  have hu : ContinuousAt (fun t:ℝ=> ‖u (q t)-u (q 0)‖+‖v t‖) 0:=ContinuousAt.add (ContinuousAt.norm ((show ContinuousAt (fun t=>u (q t)) 0 from ht).sub (continuousAt_const))) (ContinuousAt.norm he)
  have hw: u (q 0)-u (q 0)=0:=sub_self _
  filter_upwards [hu (Iio_mem_nhds (a:=R) (show ‖u (q 0)-u (q 0)‖+‖v 0‖<R by simpa [hw,v,← Prod.zero_eq_mk] using! hR)), hQ hF, ht (h.eventually (by simp))] with t hY hZ hX
  change ‖u (q t)-u (q 0)‖+‖v t‖<R at hY
  have he(k:ℕ):‖v t‖^k=‖t‖^k:=by simp [v,Prod.norm_def]
  have hI: u (q t)+v t=(t,q t):=by ext <;> simp [u,v]
  specialize hb (u (q t)) (v t) hY
  rw [hI,Finset.sum_eq_zero ?_,sub_zero, he] at hb
  · exact hb
  intro i hi
  change (i.factorial:ℝ)⁻¹ • Tensor.diagonal (iteratedFDeriv ℝ i F' (u (q t))) (v t)= _
  change ContDiffAt ℝ (↑(k+1):WithTop ℕ∞) F' (u (q t)) at hX
  change ∀ i≤k,_ at hZ
  -- horizontal scaling
  rw [show v t=t • v 1 by ext <;> simp [v],Tensor.homogeneous]
  have hp' := ray_at (k:=i) (f:=F') (u (q t)) (v 1) 0 (by rw [zero_smul,add_zero]; exact hX.of_le (by exact_mod_cast (Finset.mem_range.mp hi).le))
  rw [zero_smul,add_zero, show (fun s:ℝ=> F' (u (q t) + s • v 1)) = fun s:ℝ=>F' (s,q t) by funext s; congr 1; ext <;> simp [u,v]] at hp'
  rw [← hp',hZ i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)),smul_zero,smul_zero]
end YM.RG06.Rebase
