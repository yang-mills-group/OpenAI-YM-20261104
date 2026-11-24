import YM.UVExtension.Free.History
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# A rate for the actual history filter in the cover prescription

Mass here is literally the inverse mesh ratio (`YM.Next.Free.flying`). Take
real, unrestricted (unwrapped) momentum. The cost of the drive estimate is
set before any block lengths; in particular J is not being held constant
along the tail. We won't bound alias differences by changing smoothing every
step throughout the history; the increments here are *fine-end* increments,
for the compatible trains needed in the UV proof.
-/

set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Flat
open Filter Set Function Lattice Laurent Bloch Precision RG Next.Free UVExtension.Free
open scoped Topology BigOperators
variable {G : Gauge} (A : Levels G)

/-- Use real comparison (not division close to poles in complex momentum). -/
lemma real_chip (z : ℂ) (hz : z.im=0) : ‖chip z‖ ≤ ‖z‖ := by
  have h : (z.re:ℂ)=z := Complex.ext (by simp) (by simp [hz])
  nth_rw 1 [← h]; conv_rhs => rw [← h, Complex.norm_real]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

lemma real_twirl (z : ℂ) (hz : z.im=0) (j : ℤ) : ‖twirl z j-1‖ ≤ ‖(j:ℂ)‖ * ‖z‖ := by
  rw [← norm_mul, show twirl z j-1=chip ((j:ℂ)*z) by unfold twirl chip; ring_nf]
  exact real_chip _ (by simp [Complex.mul_im,hz])

lemma mean_real_close (M : Side) (z : ℂ) (hz : z.im=0) :
    ‖rail M z-1‖ ≤ (M.val:ℝ)*‖z‖ ∧ ‖plank M z-1‖ ≤ (M.val:ℝ)*‖z‖ := by
  have H (f : ℕ → ℤ) (hf : ∀ i<M.val, |f i| ≤ M.val) :
      ‖(M.val:ℂ)⁻¹ * (∑ i∈Finset.range M.val, twirl z (f i))-1‖ ≤ (M.val:ℝ)*‖z‖ := by
    have he : (M.val:ℂ)⁻¹ * ∑ i∈Finset.range M.val, (twirl z (f i)-1)=_ :=
      show _=(M.val:ℂ)⁻¹ * (∑ i∈Finset.range M.val, twirl z (f i))-1 by
        rw [Finset.sum_sub_distrib,mul_sub]; simp
    rw [← he]
    apply average_bound _ _; intro i hi
    refine (real_twirl z hz _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    rw [Complex.norm_intCast]
    exact_mod_cast hf i (Finset.mem_range.mp hi)
  rw [plank_centers]
  refine ⟨H (fun i=>i) ?_,H _ (fun i hi => all_centers M i hi)⟩
  intro i hi
  rw [abs_of_nonneg (Int.natCast_nonneg _)]
  exact_mod_cast hi.le

lemma along_real (P : Patch) (p : Momentum) (a : Axis) (hp : physical p) :
    ‖pullLine P a (narrow P.L p)‖ ≤ 1 ∧
      ‖pullLine P a (narrow P.L p)-1‖ ≤ (4*(P.J:ℝ)+1)*‖p‖ := by
  let M := P.L; let q := narrow M p
  let x (i : Axis) := plank M (q i)
  have hr (i) : (q i).im=0 := (physical_iff _).1 (narrow_real M hp) i
  have hd i : (M.val:ℝ)*‖q i‖ ≤ ‖p‖ := by
    unfold q; rw [narrow_apply,norm_div,Complex.norm_natCast,mul_div_cancel₀ _ (side_pos M).ne']
    exact norm_le_pi_norm _ _
  have hx i : ‖x i‖ ≤ 1 := (plank_height M (q i)).trans_eq (by simp [hr i])
  have hy i : ‖x i-1‖ ≤ ‖p‖ := ((mean_real_close M _ (hr i)).2).trans (hd i)
  have hg (u v : ℂ) (h : ‖u‖ ≤ 1) : ‖u*v-1‖ ≤ ‖v-1‖+‖u-1‖ := by
    rw [show u*v-1=u*(v-1)+(u-1) by ring]
    exact (norm_add_le ..).trans (add_le_add_left ((norm_mul_le ..).trans (mul_le_of_le_one_left (norm_nonneg _) h)) _)
  have hh (s : Finset Axis) : ‖(∏ i ∈ s, x i)-1‖ ≤ s.card * ‖p‖ := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hs ih => rw [Finset.prod_insert hs,Finset.card_insert_of_notMem hs]; exact (hg _ _ (hx i)).trans ((add_le_add ih (hy i)).trans_eq (by push_cast; ring))
  let w := ∏ i : Axis, x i
  have hb : ‖w‖ ≤ 1 := by unfold w; rw [norm_prod]; exact Finset.prod_le_one (fun _ _=> norm_nonneg _) (fun i _=> hx i)
  have hw : ‖w-1‖≤4*‖p‖ := by simpa only [w,Axis,Finset.card_univ,Fintype.card_fin,Nat.cast_ofNat] using hh Finset.univ
  have he (n : ℕ) : ‖w^n-1‖ ≤ n*(4*‖p‖) := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ']; exact (hg _ _ hb).trans ((add_le_add ih hw).trans_eq (by push_cast; ring))
  have ht : ‖w^P.J‖≤1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hb
  change ‖w^P.J * rail M (q a)‖ ≤ 1 ∧ ‖w^P.J * rail M (q a)-1‖ ≤ _
  rw [norm_mul]
  refine ⟨mul_le_one₀ ht (norm_nonneg _) ((rail_height M _).trans_eq (by simp [hr a])),?_⟩
  exact (hg _ _ ht).trans ((add_le_add (((mean_real_close M _ (hr a)).1).trans (hd a)) (he _)).trans_eq (by ring))

lemma drive_factor (d i : ℕ) (a : Axis) (p : Momentum) :
    (flying A (d+1) i).drive a (narrow (A.S.steps i (d+1)) p)=
      (flying A d i).drive a (narrow (A.S.steps i d) p) *
        pullLine (A.clock.op (i+d) 0).patch a (narrow (A.S.steps i (d+1)) p) := by
  have H (L M : Side) (p : Momentum) : narrow (L*M) p=narrow M (narrow L p) := by
    ext j; rw [narrow_apply,narrow_apply,narrow_apply,mul_side_complex,div_div]
  have hx (d i : ℕ) (p : Momentum) : narrow (A.S.steps i (d+1)) p=narrow (A.S.steps (i+1) d) (narrow (A.S.block i) p) := by
    rw [steps_tail,H]
  have hy (d i : ℕ) (p : Momentum) :
      (flying A (d+1) i).drive a (narrow (A.S.steps i (d+1)) p)=
      pullLine (A.clock.op i 0).patch a (narrow (A.S.block i) p) *
        (flying A d (i+1)).drive a (narrow (A.S.steps (i+1) d) (narrow (A.S.block i) p)) := by
    rw [hx,flying,Flight.land,Train.drive_links]; congr 2
    let x := narrow (A.S.block i) p
    change (flying A d (i+1)).mass.val • narrow (A.S.steps (i+1) d) x=x
    rw [flying_mass]
    ext j
    change (A.S.steps (i+1) d).val • (narrow (A.S.steps (i+1) d) x j)=x j
    rw [narrow_apply,nsmul_eq_mul,mul_div_cancel₀ _ (side_ne _)]
  induction d generalizing i p with
  | zero => rw [hy]; simp only [flying,Train.drive,Train.smooth_top,Train.mass,rail_unit, mul_one,one_mul,Nat.add_zero]; simp [Schedule.steps]
  | succ d ih => rw [hy _ i p,hy _ i p,ih,hx (d+1) i p,show i+(d+1)=i+1+d by omega]; rw [mul_assoc]

lemma installment_real (i d : ℕ) (a : Axis) (p : Momentum) (hp : physical p) :
    let P := (A.clock.op (i+d) 0).patch
    let U := pullLine P a (narrow (A.S.steps i (d+1)) p)
    ‖U‖ ≤ 1 ∧ ‖U-1‖ ≤ (4*(P.J:ℝ)+1)*‖p‖/(A.S.steps i d).val := by
  intro P U; let M:=A.S.steps i d
  have hx : narrow (A.S.steps i (d+1)) p=narrow P.L (narrow M p) := by
    change narrow (M*P.L) p= _; ext i; rw [narrow_apply,narrow_apply,narrow_apply,mul_side_complex,div_div]
  have he : ‖narrow M p‖ ≤ ‖p‖/M.val := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro i
    rw [narrow_apply,norm_div,Complex.norm_natCast]; gcongr; exact norm_le_pi_norm _ _
  unfold U; rw [hx]
  obtain ⟨ht,hg⟩ := along_real P _ a (narrow_real M hp)
  exact ⟨ht,hg.trans ((mul_le_mul_of_nonneg_left he (by positivity)).trans_eq (by ring))⟩

lemma step_three (S : Schedule) (i d : ℕ) :
    3 * (↑(S.steps i d).val:ℝ) ≤ (S.steps i (d+1)).val := by
  have he : (3:ℝ) ≤ (S.block (i+d)).val := by exact_mod_cast S.block_large _
  rw [Schedule.steps,mul_side_real,mul_comm (3:ℝ)]
  gcongr

lemma index_mass (i d : ℕ) :
    A.clock.J (i+d+1) ≤ ((A.clock.J i:ℝ)+2)*Real.sqrt (A.S.steps i d).val := by
  have he (d : ℕ) : ((d+2:ℕ):ℝ) ≤ 2*Real.sqrt (A.S.steps i d).val := by
    induction d with
    | zero => simp [Schedule.steps]
    | succ d ih =>
      have h := step_three A.S i d
      let t := (A.S.steps i d).val
      let u := (A.S.steps i (d+1)).val
      have h₁ := Real.sq_sqrt (show 0≤(t:ℝ) by positivity)
      have h₂ := Real.sq_sqrt (show 0≤(u:ℝ) by positivity)
      have h₃ := Real.sqrt_nonneg (u:ℝ)
      change _ ≤ (u:ℝ) at h
      change 3*(t:ℝ)≤_ at h
      have hh : 3*Real.sqrt (t:ℝ) ≤ 2*Real.sqrt (u:ℝ) := by nlinarith only [h,h₁,h₂,h₃, show 0≤(t:ℝ) by positivity]
      change _ ≤ 2*Real.sqrt (t:ℝ) at ih; push_cast at ih
      change _ ≤ 2*Real.sqrt (u:ℝ); push_cast; have : 0≤(d:ℝ):=Nat.cast_nonneg _; linarith
  have h : A.clock.J (i+d+1) ≤ A.clock.J i+(d+1) := index_limit A i (d+1)
  have hh : ((A.clock.J (i+d+1)):ℝ) ≤ (A.clock.J i:ℕ)+(d+1:ℝ) := by exact_mod_cast h
  have hy := he d; push_cast at hy
  have hM := Nat.cast_nonneg (α:=ℝ) d
  nlinarith [Nat.cast_nonneg (α:=ℝ) (A.clock.J i)]

lemma drive_unit (a : Axis) (i d : ℕ) (p : Momentum) (hp : physical p) :
    ‖(flying A d i).drive a (narrow (A.S.steps i d) p)‖ ≤ 1 := by
  induction d with
  | zero => simp [flying,Train.drive,Train.mass]
  | succ d ih => rw [drive_factor,norm_mul]; exact mul_le_one₀ ih (norm_nonneg _) (installment_real A i d a p hp).1

lemma sqrt_gain (S : Schedule) (i d : ℕ) :
    (Real.sqrt ((S.steps i (d+1)).val:ℝ))⁻¹ ≤ (2/3:ℝ) * (Real.sqrt (S.steps i d).val)⁻¹ := by
  let m:=(S.steps i d).val; let n:=(S.steps i (d+1)).val
  have hm : 0 < (m:ℝ) := side_pos _; have hn : 0 < (n:ℝ):= side_pos _
  have h : 3*(m:ℝ)≤n := step_three S i d
  have hz := Real.sqrt_pos.mpr hn
  change (Real.sqrt (n:ℝ))⁻¹ ≤ (2/3:ℝ) * (Real.sqrt (m:ℝ))⁻¹
  rw [← div_eq_mul_inv, ← one_div, div_le_div_iff₀ hz (Real.sqrt_pos.mpr hm)]
  nlinarith only [h,hm,hz, Real.sq_sqrt hm.le,Real.sq_sqrt hn.le]

def driveCost (j : ℕ) : ℝ := 4*((j:ℝ)+2)+1
lemma driveCost_pos (j : ℕ) : 0<driveCost j := by unfold driveCost; positivity

lemma drive_move (a : Axis) (i d : ℕ) (p : Momentum) (hp : physical p) :
    let X (k : ℕ) := (flying A k i).drive a (narrow (A.S.steps i k) p)
    ‖X d-X (d+1)‖ ≤ driveCost (A.clock.J i)*‖p‖*(Real.sqrt (A.S.steps i d).val)⁻¹ := by
  intro X
  let M := (A.S.steps i d).val; let w:=Real.sqrt (M:ℝ)
  have hw : 0 < w := Real.sqrt_pos.mpr (side_pos _)
  have hw' : 1 ≤ w := Real.one_le_sqrt.mpr (by exact_mod_cast (A.S.steps i d).property)
  have he := index_mass A i d
  have ht : 4*((A.clock.J (i+d+1)):ℝ)+1 ≤ driveCost (A.clock.J i)*w := by
    unfold driveCost; change _ ≤ _ * w at he; linarith
  let Y := pullLine (A.clock.op (i+d) 0).patch a (narrow (A.S.steps i (d+1)) p)
  rw [show X (d+1) = X d*Y from drive_factor ..,norm_sub_rev,← mul_sub_one,norm_mul]
  calc
    _ ≤ ‖Y-1‖ := mul_le_of_le_one_left (norm_nonneg _) (drive_unit A a i d p hp)
    _ ≤ (4*((A.clock.J (i+d+1)):ℝ)+1)*‖p‖/M := (installment_real A i d a p hp).2
    _ ≤ driveCost (A.clock.J i)*w*‖p‖/M := by gcongr
    _ = driveCost (A.clock.J i)*‖p‖*w⁻¹ := by
      rw [← (show w^2=(M:ℝ) from Real.sq_sqrt (by positivity))]; field_simp

theorem drive_rate (a : Axis) (i d D : ℕ) (p : Momentum) (hp : physical p) (hd : d≤D) :
    ‖(flying A d i).drive a (narrow (A.S.steps i d) p)-(flying A D i).drive a (narrow (A.S.steps i D) p)‖ ≤
      (3*driveCost (A.clock.J i))*‖p‖*(Real.sqrt (A.S.steps i d).val)⁻¹ := by
  induction hd using Nat.decreasingInduction with
  | self => rw [sub_self,norm_zero]; have := driveCost_pos (A.clock.J i); positivity
  | of_succ d hd ih =>
    let X (k : ℕ) := (flying A k i).drive a (narrow (A.S.steps i k) p)
    change ‖X d-X D‖≤_
    refine (norm_sub_le_norm_sub_add_norm_sub (X d) (X (d+1)) (X D)).trans ?_
    apply (add_le_add (drive_move A a i d p hp) ih).trans
    have h := mul_le_mul_of_nonneg_left (sqrt_gain A.S i d) (show 0≤ (3*driveCost (A.clock.J i))*‖p‖ by have := driveCost_pos (A.clock.J i); positivity)
    linarith only [h]
end YM.FormalBulk08.Flat
