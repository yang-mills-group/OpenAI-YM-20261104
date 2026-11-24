import YM.Integration.WilsonGraphCenteredFarBilinearBook

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.FVA2.GradedFar.AppointedSignedInsertion

open PowerSeries Finset Continuation Growth
open Register MS MS.Native MS.Land MS.Book MS.Book.Program
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Enh O.Score O.Canon Scale Dframe Reg.Point
open AppointedScalarOverflow AppointedBilinearPrice
open scoped BigOperators Classical

variable {G : Gauge} (N : Register.WilsonPrescription G)

def value (h p : ℕ) (x : Scale.Stage 2) (t : ℝ) (u v : Sec G h) : ℂ :=
  crop p t (Reg.Point.story (book N h 2 x) ![u,v])

def budget (h p : ℕ) (x : Scale.Stage 2) : ℝ :=
  ∑ c : Fin 2 → Dime G h, (‖readCoordinate h (c 0)‖ * ‖readCoordinate h (c 1)‖) *
    mass p (Reg.Point.story (book N h 2 x) (fun i => dime G h (c i)))

theorem budgetNonneg (h p : ℕ) (x : Scale.Stage 2) : 0 ≤ budget N h p x :=
  sum_nonneg fun _ _ => mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (sum_nonneg fun _ _ => norm_nonneg _)

theorem table (h p : ℕ) (x : Scale.Stage 2) (t : ℝ) (u v : Sec G h) :
    value N h p x t u v =
      ∑ c : Fin 2 → Dime G h, (dime G h).repr u (c 0) * (dime G h).repr v (c 1) *
        crop p t (Reg.Point.story (book N h 2 x) (fun i => dime G h (c i))) := by
  have finite {I : Type} [Fintype I] (F : I → PowerSeries ℂ) : crop p t (∑ i,F i) = ∑ i,crop p t (F i) := by
    exact YM.FVA2.GradedFar.crop_sum p t Finset.univ F
  have fixed (a b : ℂ) (F : PowerSeries ℂ) : crop p t (C a*C b*F) = a*b*crop p t F := by
    rw [←map_mul, YM.FVA2.GradedFar.crop_C_mul]
  rw [value,AppointedBilinearBook.basis N,finite]
  exact sum_congr rfl fun c _ => fixed _ _ _

private theorem coordinate (h : ℕ) (b : Dime G h) (w : Sec G h) :
    ‖(dime G h).repr w b‖ ≤ ‖readCoordinate h b‖*‖chair G h w‖ := by
  have paid := (readCoordinate h b).le_opNorm (chair G h w)
  change ‖(dime G h).repr ((chair G h).symm (chair G h w)) b‖ ≤ _ at paid
  rwa [LinearEquiv.symm_apply_apply] at paid

theorem price (h p : ℕ) (x : Scale.Stage 2) (t : ℝ) (ht : |t| ≤ 1) (u v : Sec G h) :
    ‖value N h p x t u v‖ ≤ budget N h p x * ‖chair G h u‖ * ‖chair G h v‖ := by
  rw [table N]
  unfold budget
  rw [Finset.sum_mul,Finset.sum_mul]
  refine (norm_sum_le _ _).trans (sum_le_sum fun c _ => ?_)
  simp only [norm_mul]
  let F := Reg.Point.story (book N h 2 x) (fun i => dime G h (c i))
  have xy := mul_le_mul (coordinate h (c 0) u) (coordinate h (c 1) v) (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have xyz := mul_le_mul xy (normCrop p t F ht) (norm_nonneg _)
    (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
  exact xyz.trans_eq (by dsimp only [F]; ring)

theorem difference (h p : ℕ) (x : Scale.Stage 2) (t : ℝ) (u v a b : Sec G h) :
    value N h p x t u v - value N h p x t a b =
      value N h p x t (u-a) v + value N h p x t a (v-b) := by
  simp only [table N]
  rw [←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
  refine sum_congr rfl fun c _ => ?_
  simp only [map_sub,Finsupp.sub_apply]
  ring

theorem compare (h p : ℕ) (x : Scale.Stage 2) (t : ℝ) (ht : |t| ≤ 1) (u v a b : Sec G h) :
    ‖value N h p x t u v - value N h p x t a b‖ ≤
      budget N h p x * (‖chair G h (u-a)‖ * ‖chair G h v‖ + ‖chair G h a‖ * ‖chair G h (v-b)‖) := by
  rw [difference N]
  exact (norm_add_le ..).trans ((add_le_add (price N h p x t ht _ _) (price N h p x t ht _ _)).trans_eq (by ring))

private theorem mapPrice (h : ℕ) (A : Module.End ℂ (Sec G h)) (u : Sec G h) :
    ‖chair G h (A u)‖ ≤ ‖chairs G h A‖ * ‖chair G h u‖ := by
  rw [←appointed]
  exact (chairs G h A).le_opNorm _

private theorem signed (h : ℕ) (L A : Module.End ℂ (Sec G h)) (u : Sec G h) :
    ‖chair G h (L u-A u)‖ ≤ ‖chairs G h L-chairs G h A‖ * ‖chair G h u‖ := by
  rw [map_sub,←appointed,←appointed,←sub_apply]
  exact (chairs G h L-chairs G h A).le_opNorm _

/-- The two genuine signed insertions use the same independent kernel and its original
positions. The second layout keeps the far-born input unchanged. -/
theorem bothAndOnce (h p : ℕ) (x : Scale.Stage 2) (t : ℝ) (ht : |t| ≤ 1) (u v : Sec G h)
    (L A : Module.End ℂ (Sec G h)) (δ : ℝ) (hδ : 0 ≤ δ) (hL : ‖chairs G h L‖ ≤ 2)
    (hA : ‖chairs G h A‖ ≤ 3) (hd : ‖chairs G h L-chairs G h A‖ ≤ δ) :
    ‖value N h p x t (L u) (L v) - value N h p x t (A u) (A v)‖ ≤
      5*budget N h p x*‖chair G h u‖*‖chair G h v‖*δ ∧
    ‖value N h p x t (L u) v - value N h p x t (A u) v‖ ≤
      5*budget N h p x*‖chair G h u‖*‖chair G h v‖*δ := by
  have b := budgetNonneg N h p x
  have du (w : Sec G h) := (signed h L A w).trans (mul_le_mul_of_nonneg_right hd (norm_nonneg _))
  have av := (mapPrice h A u).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  have lv := (mapPrice h L v).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
  have e1 := mul_le_mul (du u) lv (norm_nonneg _) (mul_nonneg hδ (norm_nonneg _))
  have e2 := mul_le_mul av (du v) (norm_nonneg _) (mul_nonneg (by norm_num) (norm_nonneg _))
  constructor
  · exact (compare N h p x t ht (L u) (L v) (A u) (A v)).trans
      ((mul_le_mul_of_nonneg_left (add_le_add e1 e2) b).trans_eq (by ring))
  · have first := compare N h p x t ht (L u) v (A u) v
    simp only [sub_self,map_zero,norm_zero,mul_zero,add_zero] at first
    have e := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (du u) (norm_nonneg (chair G h v))) b
    refine first.trans (e.trans ?_)
    have nonneg := mul_nonneg (mul_nonneg (mul_nonneg b (norm_nonneg (chair G h u))) (norm_nonneg (chair G h v))) hδ
    nlinarith only [nonneg]

end YM.FVA2.GradedFar.AppointedSignedInsertion
