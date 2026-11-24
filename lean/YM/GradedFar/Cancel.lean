import YM.GradedFar.Operands

/-!
# Homogeneous price meets the Far columns
-/
namespace YM.FVA2.GradedFar
noncomputable section
open Filter Function Real PowerSeries Set
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Scale Dframe
open scoped Topology BigOperators Classical

variable {G : Gauge} {n m h : ℕ} {d : Fin n → ℕ} {e : Fin m → ℕ} {N : WilsonPrescription G}
  {T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}

/-- The multiplier of the `q`-th OPE-component series: unchanged exterior. -/
def DX (N : WilsonPrescription G)
    (T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    (q : Toon G h) (y : Points m) (v : Inputs G e) (s : ℝ) : PowerSeries ℂ :=
  center (ordinary N) (squeeze (-s) y) (exterior N T (-s) v) q

lemma DX_eq (q : Toon G h) (y : Points m) (v : Inputs G e) (s : ℝ) :
    Dx N T y v s (theory q) = DX N T q y v s := by
  unfold Dx responses DX
  simp_rw [pivotδ]
  simp

/-- Regroup all basis expansions, *subtracting at the same Exterior*.
Use exactly the product of `c`'s uncropped formal series with the corresponding
center's formal response. -/
theorem regroup (x : Points n) (u : Inputs G d) (y : Points m) (v : Inputs G e) (s : ℝ) (h : ℕ) :
    let X := exterior N T (-s) v; let Y := squeeze (-s) y
    Yx N T x y u v s - ∑ q : Toon G h, seriesComponent N x u (flash q) * DX N T q y v s =
      ∑ a : Choices G d, C (combo u a) * ∑ c : Choices G e, factors c X *
        Basket (ordinary N) (roll a) (roll c) (FarCoefficients (book N) (roll a) x) h x Y := by
  intro X Y
  have lamp (p : Q G → PowerSeries ℂ) (c : Choices G e) : Lamp (ordinary N) h Y (roll c) p =
      ∑ q : Toon G h, p (flash q) * lonelyG (ordinary N) Y (flash q) (roll c) :=
    (LampT (ordinary N) h Y (roll c) p).symm
  simp_rw [Basket, lamp, mul_sub, Finset.sum_sub_distrib, mul_sub, Finset.sum_sub_distrib]
  unfold Yx applyFar
  refine congrArg₂ (·-·) rfl ?_
  simp_rw [seriesComponent,DX,center,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun q _ => ?_
  dsimp only [X,Y]
  ring

lemma combo_ball {L : ℝ} (u : Inputs G d) (c : Choices G d) (hu : Within L u) :
    ‖combo u c‖ ≤ L^n := by
  calc
    _ = ∏ i, ‖coord (c i) (u i)‖ := norm_prod ..
    _ ≤ ∏ _ : Fin n, L := Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => hu i _
    _ = _ := by simp
variable {I : Type}
lemma combo_price (u : I → Inputs G d) (c : Choices G d) (p : ℕ) {L : ℝ} (hu : ∀ i, Within L (u i)) :
    ChargeP p 0 (fun i _ => C (combo (u i) c)) :=
  ChargeP.constants (Rain.cash ⟨_,fun i => combo_ball (u i) c (hu i)⟩)

section estimate
-- state uniformly over the clearance sets and balls, arbitrary families helpful
variable {K : Set (Points n)} {S : Set (Points m)}
  {simple : G.Simple} {A : Prescription (Press.portDeck G)} (H : Main.Match N simple T A true)
  (hK : IsCompact K) (hx : K ⊆ conf n) (hS : IsCompact S) (hy : S ⊆ O.Enh.Outside m)
  (u : I → Inputs G d) (v : I → Inputs G e) (x : I → K) (y : I → S) (p : ℕ)
  {L R : ℝ} (hu : ∀ i, Within L (u i)) (hv : ∀ i, Within R (v i))
include H

include hS hy hv
/-- Cancellation with the homogeneous singleton bound (F.1). Done for *each* term. -/
lemma center_per_term (q : Toon G h) (c : Choices G e) :
    ChargeP (p+1) (heft (flash q)) (fun i s => factors c (exterior N T (-s) (v i)) *
        lonelyG (ordinary N) (squeeze (-s) (y i).val) (flash q) (roll c)) := by
  convert (charge_columns H c v (p+1) hv).joint ((F1 H (flash q) (roll c) hS hy p).pull y) using 1
  linarith
  rfl
lemma charge_center (q : Toon G h) : ChargeP (p+1) (heft (flash q))
    (fun i s => DX N T q (y i).val (v i) s) :=
  ChargeP.sum _ fun j _ => center_per_term H hS hy v y p hv q j

include hK hx
lemma full_per_term (a : Choices G d) (c : Choices G e) (h : ℕ) :
    ChargeP (p+1) 0 (fun i s => factors c (exterior N T (-s) (v i)) *
      party (ordinary N) (x i).val (squeeze (-s) (y i).val) (roll a) (roll c)) := by
  convert (charge_columns H c v (p+1) hv).joint
    ((full_fare H (roll a) (roll c) hK hx hS hy p h).pull (fun i => (x i,y i))) using 1
  rw [neg_add_cancel]
  rfl
lemma basket_per_term (a : Choices G d) (c : Choices G e) (h : ℕ) :
    ChargeP (p+1) ((h:ℝ)+1) (fun i s => factors c (exterior N T (-s) (v i)) *
      Basket (ordinary N) (roll a) (roll c) (FarCoefficients (book N) (roll a) (x i).val) h
        (x i).val (squeeze (-s) (y i).val)) := by
  convert (charge_columns H c v (p+1) hv).joint
    ((FO H (roll a) (roll c) hK hx hS hy p h).pull (fun i => (x i,y i))) using 1
  linarith
  rfl

include hu
theorem charge_Y (h : ℕ) :
    ChargeP (p+1) 0 (fun i s => Yx N T (x i).val (y i).val (u i) (v i) s) :=
  ChargeP.sum _ fun a _ => ChargeP.times (combo_price u a (p+1) hu)
    (ChargeP.sum _ fun c _ => full_per_term H hK hx hS hy v x y p hv a c h)

/-- Even on the actual formal full-minus-all-centers row, T^(-h-1) orderwise at the
moving exterior. -/
theorem charge_basket (h : ℕ) :
    ChargeP (p+1) ((h:ℝ)+1) (fun i s => Yx N T (x i).val (y i).val (u i) (v i) s -
      ∑ q : Toon G h, seriesComponent N (x i).val (u i) (flash q) * DX N T q (y i).val (v i) s) := by
  simp_rw [regroup]
  exact ChargeP.sum _ fun a _ => ChargeP.times (combo_price u a (p+1) hu)
    (ChargeP.sum _ fun c _ => basket_per_term H hK hx hS hy v x y p hv a c h)

omit hS hy hv
/-- No log cost on orderwise components of c. -/
lemma price_components (q : Q G) :
    ∃ C : ℝ, ∀ i, ‖coeff p (seriesComponent N (x i).val (u i) q)‖ ≤ C := by
  choose C hC using fun a : Choices G d => compact_fare H (roll a) q hK hx p
  refine ⟨∑ a, (max 0 L)^n * max 0 (C a),fun i => ?_⟩
  simp_rw [seriesComponent,map_sum,coeff_C_mul]
  refine norm_sum_le_of_le _ fun a _ => ?_
  rw [norm_mul]
  exact mul_le_mul
    (combo_ball (u i) a (fun j b => le_trans (hu i j b) (le_max_right ..)))
    ((hC a _ (x i).property).trans (le_max_right ..)) (norm_nonneg _) (pow_nonneg (le_max_left ..) _)
end estimate
end
end YM.FVA2.GradedFar
