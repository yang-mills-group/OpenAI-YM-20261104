import YM.Integration.WilsonPositionBareScalarDiagonal
import YM.Integration.WilsonPositionRawDetector

/-! On the funded auxiliary dates the physical temperature determines the small real
branch of the actual finite bare Wilson detector continuously, at every finite order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionBareDetectorStability
open Filter Function Finset Set Maxwell XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open FVA2 FVA2.Register FVA2.Scale MS MS.Land MS.Fleet
open WilsonPositionRawMesh WilsonPositionRawDetector
open scoped Topology BigOperators Classical
variable {G : Gauge} (Z : WilsonPrescription G) (m : Mesh) (q : ℕ)

theorem secant (hq : 0<q) (ρ : ℝ) (room : ρ ≤ 1) {x y : ℝ} (hx : |x|≤ρ) (hy : |y|≤ρ) :
    |(forward Z m q x - forward Z m q y) - linear Z m*(x-y)| ≤
      mass Z m q * (|x-y| *(q:ℝ)*ρ) := by
  let one : Fin (q+1) := ⟨1,by omega⟩
  let terms (k : Fin (q+1)) := detector Z m q k*(x^(k:ℕ)-y^(k:ℕ))
  have valid : forward Z m q x - forward Z m q y = ∑ k,terms k := by
    simp [WilsonPositionRawMesh.forward,terms,mul_sub,Finset.sum_sub_distrib]
  have first : terms one=linear Z m*(x-y) := by simp [terms,one,detector,linear]
  rw [valid,←sum_erase_add univ terms (mem_univ one),first,add_sub_cancel_right]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ k∈univ.erase one, |detector Z m q k| *(|x-y| *(q:ℝ)*ρ) := by
      apply sum_le_sum
      intro k hk
      dsimp only [terms]
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      by_cases hz : (k:ℕ)=0
      · simp [hz]; positivity [(abs_nonneg x).trans hx]
      have hn : (k:ℕ) ≠ 1 := fun e=>(mem_erase.mp hk).1 (Fin.ext e)
      have deg : (k:ℕ) ≤ q := by omega
      have power : max |x| |y|^((k:ℕ)-1) ≤ ρ := by
        calc
          _ ≤ max |x| |y| ^ (1:ℕ) := pow_le_pow_of_le_one
            ((abs_nonneg x).trans (le_max_left ..)) ((max_le hx hy).trans room) (by omega)
          _ ≤ ρ := by simpa using max_le hx hy
      exact (abs_pow_sub_pow_le x y (k:ℕ)).trans (mul_le_mul
        (mul_le_mul_of_nonneg_left (by exact_mod_cast deg) (abs_nonneg _)) power
        (pow_nonneg ((abs_nonneg x).trans (le_max_left ..)) _) (by positivity))
    _ ≤ _ := by
      rw [←sum_mul]
      exact mul_le_mul_of_nonneg_right (sum_le_sum_of_subset_of_nonneg (erase_subset ..)
        (fun _ _ _=>abs_nonneg _)) (mul_nonneg (by positivity) ((abs_nonneg x).trans hx))

theorem inverse (hq : 0<q) (first : 1/2 ≤ linear Z m) {a b : ℝ} (t : ℝ)
    (ha : |a|≤t) (hb : |b|≤t) (room : 4*t≤1) (fee : (32*(q+1:ℝ))*mass Z m q*t≤1) :
    |bare Z m q a - bare Z m q b| ≤ 4*|a-b| := by
  have hm : 0 ≤ mass Z m q := sum_nonneg fun _ _=>abs_nonneg _
  have ht : 0≤t := (abs_nonneg a).trans ha
  have hq' : 0≤(q:ℝ) := Nat.cast_nonneg _
  have funded : 32*(q+1:ℝ)*(mass Z m q*t)≤1 := by linarith only [fee]
  have regular : 16*(mass Z m q*t)≤1 := (mul_le_mul_of_nonneg_right
    (show 16 ≤ 32*(q+1:ℝ) by linarith) (mul_nonneg hm ht)).trans funded
  have good (c : ℝ) (hc : |c| ≤ t) := set Z m q hq first c (by linarith) (calc
    16*mass Z m q*|c| ≤ 16*mass Z m q*t := mul_le_mul_of_nonneg_left hc (by positivity)
    _ ≤ 1 := by linarith only [regular])
  obtain ⟨xa,ea⟩ := good a ha
  obtain ⟨xb,eb⟩ := good b hb
  let d := bare Z m q a-bare Z m q b
  have error := secant Z m q hq (4*t) room (xa.trans (by linarith)) (xb.trans (by linarith))
  rw [ea,eb] at error
  change |(a-b)-linear Z m*d| ≤ mass Z m q*(|d| *(q:ℝ)*(4*t)) at error
  have step : mass Z m q*((q:ℝ)*(4*t)) ≤ 1/4 := by
    have lim := (mul_le_mul_of_nonneg_right (show (16*(q:ℝ)) ≤ 32*(q+1:ℝ) by linarith)
      (mul_nonneg hm ht)).trans funded
    nlinarith only [lim,fee,mul_nonneg (mul_nonneg hq' hm) ht]
  have slip : |(a-b)-linear Z m*d| ≤ (1/4)*|d| := error.trans (by
    calc _ = (mass Z m q*((q:ℝ)*(4*t)))*|d| := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_right step (abs_nonneg _))
  have tri := abs_sub_le (linear Z m*d) (a-b) 0
  rw [sub_zero,sub_zero,abs_mul,abs_of_nonneg (by linarith : 0≤linear Z m),abs_sub_comm (linear Z m*d)] at tri
  linarith only [tri,slip,mul_le_mul_of_nonneg_right first (abs_nonneg d)]

variable {g : G.Simple} {M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {σ : Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match Z g M σ dial)

include H in
theorem measured (hq : 0<q) {t : ℝ→ℝ} (l : Filter ℝ)
    (pos : ∀ᶠ r in l,0<t r) (small : Tendsto t l (𝓝 0)) (C : ℝ) (b : ℕ) :
    ∀ᶠ r in l, ∀ i≥WilsonPositionAuxiliaryMesh.floor Z.run q (t r), (i:ℝ)≤C*(-Real.log (t r))^b →
      ContinuousAt (bare Z (Z.run.step i) q) (t r) := by
  let κ := (64*(q+1:ℝ))⁻¹
  have kpos : 0<κ := by dsimp [κ]; positivity
  obtain ⟨i₀,first⟩ := eventually_atTop.mp (ready Z g)
  have past := (WilsonPositionAuxiliaryMesh.grows Z.run q l pos small).eventually_ge_atTop i₀
  have prices := WilsonPositionBareScalarDiagonal.paid Z H q b C l pos small kpos
  filter_upwards [past,prices,pos, small.eventually_lt_const (show (0:ℝ)<1/8 by norm_num)] with r before bills positive tiny
  intro i hi upper
  let m := Z.run.step i
  have hm : 0 ≤ mass Z m q := sum_nonneg (fun _ _=>abs_nonneg _)
  have wider : mass Z m q ≤ (1+mass Z m q)^q := by
    calc
      _ ≤ (1+mass Z m q)^(1:ℕ) := by simp
      _ ≤ _ := pow_le_pow_right₀ (by linarith) hq
  have fee : (32*(q+1:ℝ))*mass Z m q*(2*t r) ≤ 1 := by
    have h := (mul_le_mul_of_nonneg_right wider positive.le).trans
      (by simpa [abs_of_pos positive] using bills i hi upper)
    dsimp only [κ] at h
    have a := (le_inv_mul_iff₀' (by positivity : 0<64*(q+1:ℝ))).mp (show mass Z m q*t r ≤ (64*(q+1:ℝ))⁻¹*1 by simpa using h)
    nlinarith only [a]
  rw [Metric.continuousAt_iff]
  intro ε he
  refine ⟨min (t r) (ε/4),lt_min positive (by linarith),?_⟩
  intro x near
  rw [Real.dist_eq] at near ⊢
  have xfit : |x|≤2*t r := by
    have h := abs_sub_le x (t r) 0
    rw [sub_zero,sub_zero,abs_of_pos positive] at h
    linarith [lt_of_lt_of_le near (min_le_left ..)]
  have bound := inverse Z m q hq (first i (before.trans hi)) (2*t r) xfit
    (b:=t r) (by rw [abs_of_pos positive];linarith) (by linarith) fee
  exact bound.trans_lt (by linarith [lt_of_lt_of_le near (min_le_right ..)])

end YM.Integration.WilsonPositionBareDetectorStability
