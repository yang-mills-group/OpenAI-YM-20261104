import YM.Integration.WilsonOriginalFiledClearHearing

/-! Ordinary faces of a single microscopic joint Wilson trial at one retained
field. The full upper discrepancy and the freshly planted defects at every
date use the same original Haar continuation and quiet denominator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalJointTrialHearing
open Function Filter Finset Lattice RG Wilson Marker MeasureTheory
open Extra.Histories Extra.Histories.Relay MergeProof MergeProof.Accent Extra.Trajectories Extra.Multi
open PhysicalNext PhysicalNext.Repeat Legato
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) (N per : ℕ)
variable {V : Type} [DecidableEq V] {J : Census V}
local notation "H" => R.family.path
local notation "X" j:max => Config G (R.family.side j per)

def read {v j : ℕ} (W : X v) (vj : v ≤ j) (Z : X j → Poly J) (S : J.Mode) : ℂ :=
  (((H).rep N per v).eval W : ℂ)⁻¹ * (gust H N per j Z v vj W).part S

private theorem tower {v i j : ℕ} (Z : X j → Poly J) (vi : v ≤ i) (ij : i ≤ j) :
    gust H N per j Z v (vi.trans ij) = gust H N per i (gust H N per j Z i ij) v vi := by
  induction vi using Nat.decreasingInduction with
  | self => rw [gust_base]
  | of_succ u hu ih => rw [gust_step H N per j Z (hu.trans_le ij),gust_step H N per i _ hu,ih]

private theorem plus {v j : ℕ} (vj : v ≤ j) (Z Y : X j → Poly J)
    (hz : Integrable Z (prior G _)) (hy : Integrable Y (prior G _)) :
    gust H N per j (Z+Y) v vj = gust H N per j Z v vj + gust H N per j Y v vj := by
  induction vj using Nat.decreasingInduction with
  | self => rw [gust_base,gust_base,gust_base]
  | of_succ t h ih =>
    rw [gust_step H N per j _ h,ih,StepData.push_add ((H).levels.transition_mass ..) _ _
      (gust_live H N per j Z hz h) (gust_live H N per j Y hy h),
      ←gust_step H N per j Z h,←gust_step H N per j Y h]

theorem difference {v j : ℕ} (W : X v) (vj : v ≤ j) (Z Y : X j → Poly J)
    (hz : Integrable Z (prior G _)) (hy : Integrable Y (prior G _)) (S : J.Mode) :
    read R N per W vj (Z-Y) S = read R N per W vj Z S - read R N per W vj Y S := by
  have add := plus R N per vj (Z-Y) Y (hz.sub hy) hy
  rw [sub_add_cancel] at add
  have eq := congrArg (fun f : X v → Poly J => (f W).part S) add
  change (gust H N per j Z v vj W).part S =
    (gust H N per j (Z-Y) v vj W).part S + (gust H N per j Y v vj W).part S at eq
  unfold read
  rw [eq,mul_add,add_sub_cancel_right]

/-- One ordinary, unnormalized numerical defect at the date of its own
fresh print. The first term is the actual Wilson push of the whole table. -/
def defect (rows : ∀ j, X j → Poly J) (j : ℕ) : X j → Poly J :=
  gust H N per (j+1) (rows (j+1)) j (Nat.le_succ j) - rows j

def fee {v : ℕ} (W : X v) (rows : ∀ j, X j → Poly J) (j : ℕ) (S : J.Mode) : ℂ :=
  if h : v ≤ j then read R N per W h (defect R N per rows j) S else 0

/-- The measured joint density is planted at the original cutoff N. The
same statement applies to every ordinary face, prior to any logarithm. -/
theorem original {v K : ℕ} (W : X v) (vK : v ≤ K) (KN : K ≤ N)
    (physical : X N → Poly J) (hP : Integrable physical (prior G _))
    (rows : ∀ j, X j → Poly J)
    (hQ : ∀ j, v ≤ j → j ≤ K → Integrable (rows j) (prior G _)) (S : J.Mode) :
    read R N per W (vK.trans KN) physical S -
        (((H).rep N per v).eval W : ℂ)⁻¹ * (rows v W).part S =
      read R N per W vK (gust H N per N physical K KN - rows K) S +
        ∑ j ∈ Ico v K, fee R N per W rows j S := by
  let f (j : ℕ) := if h : v ≤ j then read R N per W h (rows j) S else 0
  have changes : (∑ j ∈ Ico v K, fee R N per W rows j S) = f K-f v := by
    calc
      _ = ∑ j ∈ Ico v K, (f (j+1)-f j) := by
        apply sum_congr rfl
        intro j hj
        obtain ⟨left,right⟩ := mem_Ico.mp hj
        have left' := left.trans (Nat.le_succ j)
        simp only [fee,defect,f,dif_pos left,dif_pos left']
        rw [difference R N per W left _ _ (gust_live H N per (j+1) _ (hQ _ left' right) _)
          (hQ _ left right.le)]
        unfold read
        rw [← tower R N per (rows (j+1)) left (Nat.le_succ j)]
      _ = _ := by rw [sum_Ico_eq_sub _ vK]; simp_rw [sum_range_sub]; abel
  have last : f K = read R N per W vK (rows K) S := dif_pos vK
  have first : f v = (((H).rep N per v).eval W : ℂ)⁻¹ * (rows v W).part S := by
    simp only [f,dif_pos le_rfl,read,gust_base]
  rw [changes,last,first,difference R N per W vK _ _ (gust_live H N per N _ hP KN) (hQ K vK le_rfl)]
  unfold read
  rw [← tower R N per physical vK KN]
  ring

/-- Both the upper physical error and the signed dated charges are heard at
the fixed decoder before applying the triangle inequality. -/
theorem priced {v K : ℕ} (W : X v) (vK : v ≤ K) (KN : K ≤ N)
    (physical : X N → Poly J) (hP : Integrable physical (prior G _))
    (rows : ∀ j, X j → Poly J)
    (hQ : ∀ j, v ≤ j → j ≤ K → Integrable (rows j) (prior G _)) (S : J.Mode)
    {upper : ℝ} {cash : ℕ → ℝ}
    (entrance : ‖read R N per W vK (gust H N per N physical K KN - rows K) S‖ ≤ upper)
    (dated : ∀ j ∈ Ico v K, ‖fee R N per W rows j S‖ ≤ cash j) :
    ‖read R N per W (vK.trans KN) physical S -
      (((H).rep N per v).eval W : ℂ)⁻¹ * (rows v W).part S‖ ≤ upper + ∑ j ∈ Ico v K, cash j := by
  rw [original R N per W vK KN physical hP rows hQ S]
  exact (norm_add_le _ _).trans (add_le_add entrance ((norm_sum_le _ _).trans (sum_le_sum dated)))

end YM.Integration.WilsonOriginalJointTrialHearing
end

