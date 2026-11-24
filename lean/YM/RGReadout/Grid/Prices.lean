import YM.RGReadout.Capture.Fields
import YM.OPE.Columns.SectorCost

/-!
# Costs of the actual (not just formal) literal maps

Op norm for any `N ≥ k`, `p` fitting. Inverse bound `exp((d+o(1))s_k)`
uniform in those N,p. Used for existence and for the initial *spatial* error
interface only; not coupling-order price through perturbative window lengths.
No arbitrary choice of nulls could be assumed to leave these bills invariant.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGReadout.Literal
open Finset Function Filter MeasureTheory Wilson Lattice RG Source Extra.Histories
open MergeProof MergeProof.Accent MergeProof.Ribbons Trace.Physical Trace.Physical.GermGraph
open Overlay Work.G08 Bid Next.Rank Next.UVStress Price OPE
open Planned.PrimaryIntegral295 PPX
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical

variable {G : Gauge} (C : Family G) (H : C.Makes) (d k N p : ℕ)
set_option quotPrecheck false
local notation "F" => C.labels.level d

include H in
/-- Prefix top calibration (not tail). -/
lemma quota_from_reference (hk : C.ref d ≤ k) (hp : k ≤ N) (x : C.label d) :
    quota C d k N p x ≤ Columns.juice C.path.levels k * (C.labels.level d).coeffSize x := by
  induction k,hk using Nat.le_induction with
  | base =>
    rw [quota,show ((C.factory d N p).entries (C.ref d) _).x = x from C.normalized H hp x]
    exact le_mul_of_one_le_left (size_nonneg ..) (Columns.juice_pos ..)
  | succ i hi ih =>
    have hn := i.le_succ.trans hp
    rw [Columns.juice_step,mul_assoc]
    exact ((H.calibrated d N p (hi.trans hn)).back i hi hp _).trans
      (mul_le_mul_of_nonneg_left (ih hn) (zero_le_one.trans (C.path.levels.params _).columns_ge))

lemma number_cost (x : C.label d) :
    (C.labels.level d).coeffSize x ≤ (Fintype.card (C.labels.level d).Index : ℝ)*‖x‖ := by
  refine Finset.sum_le_sum (s:=univ) (g:=fun i:(F).Index=>‖x‖) (fun i _=> ?_)|>.trans ?_
  · exact norm_le_pi_norm x i
  simp

def normAllow (d k) := (Price.outward C d k) * ((C.S.a k)^d * (2*lensPrice C d k)) *
    (Fintype.card (C.labels.level d).Index : ℝ)
lemma allow_pos (d k) : 0 < normAllow C d k := mul_pos (mul_pos (zero_lt_one.trans_le (Price.outward_nn C d k))
    (mul_pos (pow_pos (C.S.a_pos k) _) (mul_pos zero_lt_two (lensPrice_pos C d k))))
    (Nat.cast_pos.mpr Fintype.card_pos)
lemma meter_cost (h : Opened C d k p) (hp : k ≤ N) (x : C.label d) :
    ‖meter C H d k N p h hp x‖ ≤ normAllow C d k * ‖x‖ := by
  let y := meter C H d k N p h hp x
  have hw : ‖y‖ ≤ Price.outward C d k * quota C d k N p y :=
    (Size.norm_le ..).trans (Price.at_current C H h.post hp p y)
  rw [← Log.obey_quota] at hw
  have hg : 0 ≤ C.S.a k^d := pow_nonneg (C.S.a_pos _).le _
  have he : Spindle.paid C d k N p y ≤ (2*lensPrice C d k)*((Fintype.card (F).Index:ℝ)*‖x‖) :=
    (meter_paid C H d k N p h hp x).trans (mul_le_mul_of_nonneg_left (number_cost C d x)
      (mul_nonneg (by norm_num) (lensPrice_pos C _ _).le))
  apply (hw.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he hg)
    (zero_le_one.trans (Price.outward_nn C d k)))).trans_eq
  unfold normAllow; ring

include H in
lemma reduction_top (hp : k ≤ N) : Price.shrink C k N p ≤ 2 := by
  let H₀ := C.path.levels.clock
  let B := H₀.hatBeta k
  let b := C.path.β N p k
  have hx : B/2 ≤ b := (H.wilson.represents N p k hp).band.1
  have he : 0 < B := zero_lt_one.trans (C.path.levels.fits.delayed _)
  have ht := lt_of_lt_of_le (half_pos he) hx
  unfold Price.shrink
  rw [div_le_iff₀ (show 0 < C.path.levels.clock.threshold k from (C.path.levels.budget k).threshold_pos)]
  have h₁ : 0 < Real.sqrt B := Real.sqrt_pos.mpr he
  have h₂ : 0 < Real.sqrt b := Real.sqrt_pos.mpr ht
  have hv : (Real.sqrt b)⁻¹ ≤ 2*(Real.sqrt B)⁻¹ := by
    field_simp; nlinarith only [hx,h₁,h₂,Real.sq_sqrt he.le, Real.sq_sqrt ht.le]
  apply hv.trans
  change _ ≤ 2*((Real.sqrt B)⁻¹*(H₀.monitor k))
  exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (inv_pos.mpr h₁).le
    (Real.one_le_exp (sq_nonneg _))) zero_le_two
lemma reduction_cost (hp : k ≤ N) (x : C.label d) :
    (C.labels.level d).coeffSize ((toThreshold C H d k N p hp).symm x) ≤
       (2:ℝ)^d * (C.labels.level d).coeffSize x := by
  let a := Price.shrink C k N p
  have he : a ≤ 2 := reduction_top C H k N p hp
  have ht : 0<a := Price.shrink_pos C H hp p
  change (F).coeffSize ((F).scaled a x) ≤ _
  unfold Labels.Frame.coeffSize; rw [mul_sum]
  apply sum_le_sum
  intro i hi
  rw [Labels.Frame.scaled_apply,norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_right
    ((pow_le_pow_left₀ ht.le he _).trans (pow_le_pow_right₀ one_le_two (Film.second_fits F i)))
    (norm_nonneg _)

/-- Inverse bill exp((d+o(1))s_k). -/
def normReverse (d k) := 2^d * (C.S.a k^d)⁻¹ * 2 * Columns.juice C.path.levels k *
    (Fintype.card (C.labels.level d).Index : ℝ)
lemma reverse_pos (d k) : 0 < normReverse C d k :=
  mul_pos (mul_pos (mul_pos (mul_pos (pow_pos zero_lt_two d)
    (inv_pos.mpr (pow_pos (C.S.a_pos k) d))) zero_lt_two)
    (zero_lt_one.trans_le (Columns.juice_pos ..))) (Nat.cast_pos.mpr Fintype.card_pos)
lemma reverse_byQuota (h : Opened C d k p) (hp : k ≤ N) (x : C.label d) :
    ‖(meter C H d k N p h hp).symm x‖ ≤ (2^d * (C.S.a k^d)⁻¹ * 2) * quota C d k N p x := by
  let y := (meter C H d k N p h hp).symm x
  let Q := measuring C d N p k ((C.factory d N p).terminal.symm x)
  have hh := reads_meter C H _ _ _ _ h hp y
  rw [show meter C H d k N p h hp y = x from (meter C H d k N p h hp).apply_symm_apply x] at hh
  let a := spacing C k d
  let U := toThreshold C H d k N p hp
  have he : Q = a • U y := hh
  have ha : ‖a‖ = C.S.a k^d := by rw [show a=(C.S.a k:ℂ)^d from rfl,norm_pow,
                                             Complex.norm_real,Real.norm_of_nonneg (C.S.a_pos _).le]
  have hy : ‖y‖ ≤ 2^d * ((C.S.a k^d)⁻¹ * (F).coeffSize Q) := by
    apply (Size.norm_le F y).trans
    have he' : y = U.symm (a⁻¹ • Q) := by rw [he,inv_smul_smul₀ (spacing_ne C _ _),U.symm_apply_apply]
    rw [he',← ha, ← norm_inv,← Size.smul]
    exact reduction_cost C H _ _ _ _ hp _
  have hh' := (size_gap d N p k H h hp ((C.factory d N p).terminal.symm x)).1
  apply (hy.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh'
    (inv_pos.mpr (pow_pos (C.S.a_pos _) d)).le) (by positivity))).trans_eq
  unfold quota; ring

lemma reverse_cost (h : Opened C d k p) (hp : k ≤ N) (x : C.label d) :
    ‖(meter C H d k N p h hp).symm x‖ ≤ normReverse C d k * ‖x‖ := by
  have hh := (quota_from_reference C H d k N p h.post hp x).trans
    (mul_le_mul_of_nonneg_left (number_cost C d x) (zero_le_one.trans (Columns.juice_pos ..)))
  apply ((reverse_byQuota C H d k N p h hp x).trans (mul_le_mul_of_nonneg_left hh
    (mul_nonneg (mul_nonneg (by positivity)
      (inv_pos.mpr (pow_pos (C.S.a_pos k) d)).le) (by norm_num)))).trans_eq
  unfold normReverse; ring

variable {ι : Type*} {l : Filter ι} {T : ι → ℝ} {v : ι → ℕ}
lemma reverse_rate (h : Tendsto T l atTop) (ht : Height C.S l T v 1) :
    RateIs l T (fun i => normReverse C d (v i)) (d:ℝ) := by
  have hu := (((((RateIs.const h zero_lt_two).power d).mul (ht.mesh.power d).inv).mul
    (RateIs.const h zero_lt_two)).mul (Columns.juice_rate_seq C ht.grows ht.pace)).mul
    (RateIs.const h (show 0 < (Fintype.card (F).Index : ℝ) from Nat.cast_pos.mpr Fintype.card_pos))
  exact hu.swap (by ring)

-- Uniform linear interfaces, with reversible padding off domain.
def dialRaw (i : ℕ × ℕ) : C.label d ≃ₗ[ℂ] C.label d :=
  if h:Opened C d k i.2 ∧ k ≤ i.1 then meter C H d k i.1 i.2 h.1 h.2 else LinearEquiv.refl ℂ _
def flow (i : ℕ × ℕ) := LinearMap.toContinuousLinearMap (dialRaw C H d k i).toLinearMap
def inflow (i : ℕ × ℕ) := LinearMap.toContinuousLinearMap (dialRaw C H d k i).symm.toLinearMap
lemma toll_out (i : ℕ × ℕ) : ‖flow C H d k i‖ ≤ 1+normAllow C d k := by
  have hh : 0 < normAllow C d k := allow_pos ..
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun x=> ?_)
  change ‖dialRaw C H d k i x‖ ≤ _
  unfold dialRaw; split
  next h =>
    exact (meter_cost C H _ _ _ _ h.1 h.2 _).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (norm_nonneg _))
  exact le_mul_of_one_le_left (norm_nonneg _) (le_add_of_nonneg_right hh.le)
lemma toll_in (i : ℕ × ℕ) : ‖inflow C H d k i‖ ≤ 1+normReverse C d k := by
  have hh : 0 < normReverse C d k := reverse_pos ..
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun x=> ?_)
  change ‖(dialRaw C H d k i).symm x‖ ≤ _
  unfold dialRaw; split
  next h =>
    exact (reverse_cost C H _ _ _ _ h.1 h.2 _).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (norm_nonneg _))
  exact le_mul_of_one_le_left (norm_nonneg _) (le_add_of_nonneg_right hh.le)
lemma flows (i : ℕ × ℕ) (h : Opened C d k i.2) (hN : k ≤ i.1) (x : C.label d) :
    flow C H d k i x = meter C H d k i.1 i.2 h hN x := by
  change dialRaw C H d k i x = _; unfold dialRaw; rw [dif_pos ⟨h,hN⟩]
lemma inflows (i : ℕ × ℕ) (h : Opened C d k i.2) (hN : k ≤ i.1) (x : C.label d) :
    inflow C H d k i x = (meter C H d k i.1 i.2 h hN).symm x := by
  change (dialRaw C H d k i).symm x = _; unfold dialRaw; rw [dif_pos ⟨h,hN⟩]

end YM.RGReadout.Literal
