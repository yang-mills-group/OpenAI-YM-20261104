import YM.MS.Vane.Houses

/-! The actual signed open Wilson/MS join at an arbitrary moving separation.
All orders of the native oscillatory gain are retained on the fine lengths.
On the complement the unsuppressed native integral is exactly the required price. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorMixedKernel
open Set Function Filter Finset Metric MeasureTheory Real
open YM.MS
open Koszul Plane Landau Detect Tone Momentum Heat High Frame Wire Signal Flux Wind Garment Outlook Latch Job Belt Rake Geo
open Osc Fiddle Snap Book.Convolve City
open scoped Topology ContDiff Classical

variable {ι : Type} {S : Scale ι} {G : Gauge}

private theorem coefficient_cases {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g y : ι → E → ℂ} {a b c : ι → ℝ} (hf : Bound S f a) (hg : Bound S g b)
    (hc : ∀ i, (y i=f i ∧ c i=a i) ∨ (y i=g i ∧ c i=b i)) : Bound S y c := by
  constructor
  · intro i
    rcases hc i with ⟨hi,_⟩ | ⟨hi,_⟩
    · rw [hi]; exact hf.smooth i
    · rw [hi]; exact hg.smooth i
  intro j
  obtain ⟨A,hA,d,hF⟩ := hf.quoted j
  obtain ⟨B,hB,e,hG⟩ := hg.quoted j
  refine ⟨A+B,add_pos hA hB,d+e,fun i u hu => ?_⟩
  have h₀ := S.full.one_le i u hu
  have up (v w : ℕ) (H V : ℝ) (hv : v≤w) (hH : 0≤H) (hV : H≤V) :
      H*(S.full.cheap i u)^v ≤ V*(S.full.cheap i u)^w :=
    mul_le_mul hV (pow_le_pow_right₀ h₀ hv) (pow_nonneg (zero_le_one.trans h₀) _) (hH.trans hV)
  change ‖iteratedFDeriv ℝ j (y i) u‖ ≤ (A+B)*(S.full.cheap i u)^(d+e)*(c i*S.length i^j)
  rcases hc i with ⟨hi,hc⟩ | ⟨hi,hc⟩
  · rw [hi,hc]
    exact (hF i u hu).trans (mul_le_mul_of_nonneg_right
      (up d (d+e) A (A+B) (by omega) hA.le (by linarith only [hB]))
      (mul_nonneg (hf.nonneg i u hu) (pow_nonneg (S.pos i).le _)))
  · rw [hi,hc]
    exact (hG i u hu).trans (mul_le_mul_of_nonneg_right
      (up e (d+e) B (A+B) (by omega) hB.le (by linarith only [hA]))
      (mul_nonneg (hg.nonneg i u hu) (pow_nonneg (S.pos i).le _)))

private theorem kernel_cases {f g y : ι → Law G} {a b c : ι → ℝ}
    (hf : Lease false false S f a) (hg : Lease false false S g b)
    (hc : ∀ i, (y i=f i ∧ c i=a i) ∨ (y i=g i ∧ c i=b i)) : Lease false false S y c := by
  intro E _ _ w hw hv
  apply coefficient_cases (hf E w hw hv) (hg E w hw hv)
  intro i
  rcases hc i with ⟨hy,ha⟩ | ⟨hy,ha⟩
  · left
    exact ⟨congrArg (fun F : Law G => fun x => F (sail w x)) hy,congrArg (S.length i^pitch w * ·) ha⟩
  · right
    exact ⟨congrArg (fun F : Law G => fun x => F (sail w x)) hy,congrArg (S.length i^pitch w * ·) ha⟩

variable (S) (A : ι → QP) {K : ι → Edge G} {X Y : ι → Law G} {a x y : ι → ℝ}

/-- The temporal/UV side and the coarse side of each individual join use the
same signed native Cabin, original species, laws, kinetic line and Fourier measure.
This estimate has no uniform-comparability assumption on the collection of distances. -/
theorem kernel (hk : Sheet S a K) (hx : Lease false true S X x) (hy : Lease false true S Y y)
    (ha : nn a) (hX : nn x) (hY : nn y) (k : ℕ) :
    Lease false false S (fun i => Cabin (A i) (K i) planeF (X i) (Y i))
      (fun i => a i*(x i*y i)*(S.length i / max (S.length i) ‖A i‖)^k) := by
  let v := fun i => max (S.length i) ‖A i‖
  let big := fun i => if S.length i ≤ ‖A i‖ then A i else fun _ : Axis => S.length i
  let small := fun i => if S.length i ≤ ‖A i‖ then (0:QP) else A i
  have big_norm (i : ι) : ‖big i‖=v i := by
    by_cases h : S.length i≤‖A i‖
    · simp [big,v,h]
    · simp [big,v,h,max_eq_left (le_of_not_ge h),Real.norm_eq_abs,abs_of_pos (S.pos i)]
  have small_norm (i : ι) : ‖small i‖≤S.length i := by
    by_cases h : S.length i≤‖A i‖
    · simpa [small,h] using (S.pos i).le
    · simpa [small,h] using (le_of_not_ge h)
  have fast := PulseQ (S:=S) (A:=big) (v:=v) (T:=1) hk hx hy ha hX hY
    (fun i=>(S.pos i).trans_le (le_max_left ..)) (fun i=>by rw [big_norm,one_mul])
    (fun _=>le_max_left ..) (paidMono (fun i=>(big_norm i).le)) zero_lt_one k
  have slow := hob (S:=S) (A:=small) (μ:=fun _=>planeF) hk hx hy ha hX hY
    (Tall S 5 (by decide)) (fun E _=> tom S 5 (by decide))
    (fun E _ _=> Cost.of_le (fun i _ _=>small_norm i))
  apply kernel_cases fast slow
  intro i
  by_cases h : S.length i≤‖A i‖
  · left
    simp only [big,h,if_pos,v,and_self]
  · right
    simp [small,h,max_eq_left (le_of_not_ge h),(S.pos i).ne',Pi.mul_apply]

end YM.Integration.WilsonPhysicalExteriorMixedKernel
