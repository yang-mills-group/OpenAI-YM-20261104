import YangMills.WilsonProof.NativeSupport.Commissioned259.ScaleCost.Metrics
/-! # Towards Flash259HorizonFork: QScale fields polymer-log tariff

(G.2) norm prices only. Finite step estimate on both determinant and columns, not
contraction proof of all-power estimate on strictly lower entries.
Derivative/flow assertions are not claimed. No continuity assumed at any anchor.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.ScaleCost
open Filter Set Function Asymptotics MeasureTheory PowerSeries
open MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land Register FVA2.Scale
open XSpace XSpace.Normalize O.Score O.Enh Dframe Comparing
open scoped Topology Classical BigOperators Matrix
local notation "late" => 𝓝[>] (0:ℝ)
variable {G : Gauge} {V : Arenas G} {R : ℝ→PowerSeries ℂ}
    {B : ℝ→Frames G} {D : Route G}
    {d : ℕ} (hG : G.Simple)
-- concrete coefficient fed into the polynomial; no small-radius window here
lemma linear (N : WilsonPrescription G) (ν : ℝ) (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ : Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match N hG M σ dial) (s : ℝ) :
    coeff 1 (GroupS.gaugeN N.scheme N.criterion M ν s d)=0 := by
  let W := H.details.toServed.toPosted.toQuoted.toContract.toMission.born
  exact Generator.Q.lifted _ _ _ _ σ s hG W.Taylor W.still W.base
lemma fare_quadratic {t : ℝ→ℝ} (h : Law V R B) (hz : ∀ s: ℝ, coeff 1 (B s d)=0) (field : FieldQuote G B t D d 1) :
    ∃ C:ℝ,0<C ∧ ∀ᶠ r in late, ∀ T ≥ 1, T ≤ 2 → stiffness (actual D d r T-engine G d (-Real.log T)) ≤ C*g0 G r^2 := by
  have H (r T : ℝ) : form B d T 1 (t r)= engine G d (-Real.log T) := by
    apply Matrix.ext; intro i j; rw [form, crop_apply]; simp only [ Finset.sum_range_succ,Finset.sum_range_zero,badge,coeff_mk,zero_add,pow_zero,one_mul,conversion,coeff_C_mul,hz,mul_zero,LinearMap.zero_apply,map_zero,(h.paid ..).zero,mul_one]; simp only [mul_zero,add_zero]; rfl
  simpa only [FieldQuote, H] using field

abbrev cash (r : ℝ) := Real.log r⁻¹
def Income (f : ℝ→ℝ) := ∃ k:ℕ, f=O[late] fun s=>cash s ^ k
-- Convert the polylog requests of G into powers of g⁻¹, retaining possibly phases etc.
lemma holds_cash : Tendsto cash late atTop := Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
include hG
lemma twice_cap : ∀ᶠ r in late, (g0 G r)^2=G.slopeConstant⁻¹/cash r := by
  filter_upwards [holds_cash.eventually_gt_atTop 0] with i h; unfold g0; rw [inv_pow, Real.sq_sqrt (mul_nonneg (Gauge.slopeConstant_pos hG).le h.le),mul_inv_rev]; ring
lemma adjustment : ∀ᶠ r in late, cash r=G.slopeConstant⁻¹*((g0 G r)⁻¹)^2 := (twice_cap hG |>.and (g0_pos hG)).and (holds_cash.eventually_gt_atTop 0) |>.mono fun r ⟨⟨h,l⟩,v⟩=>by rw [inv_pow,←div_eq_mul_inv]; field_simp [l.ne',v.ne']; rw [mul_comm,one_div]; exact (div_eq_iff v.ne').mp h.symm |>.symm
lemma payload {f : ℝ→ℝ} (h : Income f) : ∃ k:ℕ, f=O[late] fun i=> (g0 G i)⁻¹^k := by
  obtain ⟨k,H⟩:= h; refine ⟨2*k, H.trans ?_ ⟩
  refine IsBigO.congr' ((isBigO_refl (fun i=> (g0 G i)⁻¹^(2*k)) late).const_mul_left (G.slopeConstant⁻¹^k)) ?_ (EventuallyEq.refl ..)
  filter_upwards [adjustment hG] with i hi; rw [hi, mul_pow,pow_mul]

lemma log_growth (F : ℝ→ℝ) (A : ℝ) (hA : 0 ≤ A) (hf : ∀ᶠ r in late, ∀ T ≥ 1, T ≤ 2 → ‖F r‖ ≤ (1+A*g0 G r ^ 2)*‖F (r*T)‖) : Income F := by
  let l:= Real.log 2; have hl : 0 < l := Real.log_pos (by norm_num)
  let B := A*G.slopeConstant⁻¹
  let k:= ⌈B/l⌉₊; have hk : B ≤ k*l := (div_le_iff₀ hl).mp (Nat.le_ceil _)
  have hb : 0 ≤ B := mul_nonneg hA (inv_pos.mpr (Gauge.slopeConstant_pos hG)).le
  have he : ∀ᶠ r in late, ∀ T ≥ 1,T ≤ 2 → ‖F r‖ ≤ (1+B / cash r)*‖F (r*T)‖ := by
    filter_upwards [hf,twice_cap hG] with i h v T hT j; exact (h T hT j).trans_eq (by rw [v]; unfold B; ring)
  obtain ⟨L,hL,E⟩:= mem_nhdsGT_iff_exists_Ioc_subset.mp (he.and (holds_cash.eventually_ge_atTop 1))
  let C:=(1+B)*‖F L‖; have hC : 0 ≤ C := by positivity
  let u : ℝ→ℝ:= cash
  suffices H : ∀ n:ℕ, ∀ s∈ Ioc 0 L, L / s ≤ n+1 → ‖F s‖ ≤ C*u s^k by
    refine ⟨k,IsBigO.of_bound C ?_⟩
    filter_upwards [show ∀ᶠ r in late,r ∈ Ioc 0 L from Ioc_mem_nhdsGT hL] with r h
    rw [Real.norm_of_nonneg (pow_nonneg (zero_le_one.trans (E h).2) _)]; exact H ⌈L/r⌉₊ r h (by linarith [Nat.le_ceil (L/r)])
  have start (s:ℝ) (h:s∈Ioc 0 L) (hs:L/s ≤ 2) : ‖F s‖ ≤ C*u s^k := by
    have hp := (E h).1 (L/s) ((one_le_div h.1).mpr h.2) hs
    rw [mul_div_cancel₀ _ h.1.ne'] at hp
    exact (hp.trans (mul_le_mul_of_nonneg_right (add_le_add le_rfl (div_le_self hb (E h).2)) (norm_nonneg _))).trans (le_mul_of_one_le_right hC (one_le_pow₀ (E h).2))
  intro n; induction n with
  | zero=> intro s h e; exact start s h (by norm_num at e; linarith)
  | succ n ih=>
    intro s h e
    rcases le_total (L/s) 2 with p|p; exact start s h p
    let r:= s*2; have hp : 0<s := h.1
    have hv : r∈Ioc 0 L := ⟨mul_pos hp (by norm_num),by unfold r; rw [mul_comm]; exact (le_div_iff₀ hp).mp p⟩
    have hi := ih r hv (by unfold r; rw [←div_div]; push_cast at e; nlinarith only [e,Nat.cast_nonneg (α:=ℝ) n])
    apply ((E h).1 2 (by norm_num) le_rfl).trans ((mul_le_mul_of_nonneg_left hi (by have h : 1 ≤ cash s := (E h).2; positivity)).trans ?_)
    change (1+B/u s)*(C*u r^k) ≤ C*u s^k
    rw [mul_left_comm]; apply mul_le_mul_of_nonneg_left _ hC
    have hz := zero_lt_one.trans_le (E hv).2
    have eq : u r+l=u s := by unfold u l cash r; rw [Real.log_inv,Real.log_inv,Real.log_mul hp.ne' (by norm_num)]; ring
    have lo : 0 < u r := hz
    rw [ ← le_div_iff₀ (pow_pos lo _), ← div_pow]
    calc (1:ℝ)+B/u s ≤ 1+B/u r := add_le_add le_rfl (div_le_div_of_nonneg_left hb lo (by linarith))
         _ ≤ 1+k*(l/u r) := add_le_add le_rfl (by rw [ ← mul_div_assoc]; exact div_le_div_of_nonneg_right hk lo.le )
         _ ≤ (1+l/u r)^k := one_add_mul_le_pow (by linarith [div_pos hl lo]) k
         _ = (u s/u r)^k := by rw [ ← eq,add_div,div_self lo.ne' ]
end YM.FVA2.GradedFar259.ScaleCost
