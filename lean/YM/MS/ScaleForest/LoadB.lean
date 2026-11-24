import YM.MS.ScaleForest.TracedCubic

/-!
# Lowest two-point bulk loop bubble, carry the kernel all the way to Taylor

After integration over orders of the two edges. Keep a general test in the
four-plane; the pole will also extend, by tensor symmetry. Includes two
summing choices which will be shown zero. Use the actual internal-index
orientation convention as exposed in TracedCubic.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest.TwoPoint
open Function Filter Set Finset MeasureTheory Metric
open MS Plane Koszul Heat Flux Landau Tone Momentum Real Frame Wire Color Detect Native
open Book Convolve Logarithm Signal Landau.Detect.Mark Arts Motif Halo
open Rock Path Oceans Plum Alps Garment Arc Spin Train Pearl Dock Shine GraphSum
open City WilsonMS.BetaValue
open Complex (I)
open scoped Topology ContDiff BigOperators
variable {G : Gauge} (r : ℝ) (p q : QP) (mu x y : Axis)


def tireG := ∑ u:Axis,∑ v:Axis,precision u v q * ∑ i:Axis,∑ j:Axis, precision i j (q+p) *
    tridentMu mu p q i u * tridentMu mu p q j v

def gaugeTensor (r : ℝ) (p q : QP) (mu : Axis) : ℂ := ((Pill r p q * 2 * tireG p q mu :ℝ):ℂ)
def ghostTensor (r : ℝ) (p q : QP) (mu : Axis) : ℂ := -4 * SquareShift.twin p mu mu r q

def bothTensor (r : ℝ) (p q : QP) (mu : Axis) (ξ σ : Bool) := if ξ ≠ σ then (0:ℂ)
    else if σ then ghostTensor r p q mu else gaugeTensor r p q mu

theorem flipG : twoG r (-p) q mu x y = twoG r p (-q) mu x y := by
  have he : (-q)+p= -(q+ -p):= by abel
  have hV (a b:Axis) : tridentMu mu (-p) q a b= -tridentMu mu p (-q) a b := by
    unfold tridentMu; rw [he]; obtain ht:= trident_flip (-(q + -p)) q a b mu (-p); rw [neg_neg p] at ht; rw [ht,neg_neg]
  unfold twoG; simp_rw [hV,he,Lace_neg]; simp_rw [Complex.ofReal_neg,mul_neg,neg_mul,neg_neg]

lemma ghost_half : 4 * SpanH 1 q mu * SpanH r (q+p) mu= ghostTensor r p q mu := by
  unfold ghostTensor SpanH SquareShift.twin SquareShift.tensorPol Pill; push_cast; ring_nf; rw [Complex.I_sq]; ring

theorem gauge_half : 2 * (∑ x:Axis,∑ y:Axis, Lace 1 q x y * twoG r p q mu x y) = gaugeTensor r p q mu := by
  unfold gaugeTensor Pill tireG twoG; push_cast; simp_rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _
  refine Finset.sum_congr rfl fun y _=> Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> ?_
  ring

variable (ξ σ : Bool) (a b c : CI G)

-- Rolls at all radius even if 0. Then use genuine trace integration.
def connective (r : ℝ) (σ : Bool) (G : Gauge) := (factor true:ℂ) • bridgeG (Km r σ) (interaction G 1).symbol (interaction G 1).symbol

theorem written : connective r σ G 0 = (2:ℂ)⁻¹ • Exchange (Km r σ 0):= by
   unfold connective; rw [bridgeG_eq (selected_rev r σ)]; unfold factor; rw [if_pos rfl]; push_cast; rfl

local notation "C_U" => connective r σ G 0
local notation "Z" => word (m:=0) mu mu a b p

private theorem ghost_flip (x : Axis) :
    SpanH 1 q x * C_U (U x c q :: C c (-q)::Z)= SpanH 1 (-q) x * C_U (C c (-q)::U x c q:: Z) := by
   have he : C_U (U x c q :: C c (-q):: Z)= -(C_U (C c (-q):: U x c q :: Z)) := by
     rw [written]; simp_rw [Pi.smul_apply, smul_eq_mul]; rw [exchangeSym,show (cross (parity (U x c q).1) (parity (C c (-q)).1):ℂ)=-1 from rfl]; ring
   rw [he, Span_neg]; ring

private theorem charge_r (x:Axis) : C_U (C c q :: U x c (-q) :: Z) =
    if σ=true ∧ x=mu then 2*angle c a b* (SpanH r (q+p) mu + SpanH r (q+ -p) mu) else 0 := by
   rw [written]; exact exchangeC ..

private lemma ghost_sum : ∑ x:Axis,(SpanH 1 q x * C_U (C c q:: U x c (-q):: Z)+SpanH 1 q x * C_U (U x c q:: C c (-q):: Z))=
     if σ then angle c a b * (ghostTensor r p q mu + ghostTensor r p (-q) mu) else 0:= by
   have hp (x:Axis) : C_U (C c (-q):: U x c q :: Z)= _ := neg_neg q ▸ charge_r r p (-q) mu σ a b c x
   simp_rw [ghost_flip r p q mu σ a b c, charge_r,hp]
   by_cases hS : σ=true
   · rw [Finset.sum_eq_single mu];
     · simp only [hS,if_true,and_self]; rw [ ← ghost_half r p q mu, ← ghost_half r p (-q) mu,
         show (-q)+ (-p)= -(q+p) from (by abel), Span_neg r, show q+(-p)= -((-q)+p) from (by abel),
         Span_neg r, Span_neg]; ring
     · intro i _ hi; simp [hi]
     simp
   simp [hS]

private lemma gaugeSum : (∑ x:Axis,∑ y:Axis, Lace 1 q x y * C_U (W x c q :: W y c (-q) :: Z)) =
    if σ then 0 else angle c a b*(gaugeTensor r p q mu + gaugeTensor r p (-q) mu) := by
  have he (x y : Axis) : C_U (W x c q::W y c (-q):: Z)= (if σ then 0 else 2*angle c a b * (twoG r p q mu x y+twoG r (-p) q mu x y)) := (by rw [written]; exact exchangeW r σ p q mu x y c a b)
  simp_rw [he]; split; simp; next h=>
    rw [ ← gauge_half, ← gauge_half]; simp_rw [Lace_neg,flipG r p q,mul_add,Finset.mul_sum,
      Finset.sum_add_distrib];
    exact congr_arg₂ (·+·) (Finset.sum_congr rfl fun _ _=>Finset.sum_congr rfl fun _ _=>by ring)
        (Finset.sum_congr rfl fun _ _=>Finset.sum_congr rfl fun _ _=>by ring)

theorem trace_value : trc (Km 1 ξ 0) q C_U Z = (∑ i:G.ColorIndex,angle i a b)*
    (bothTensor r p q mu ξ σ+ bothTensor r p (-q) mu ξ σ) := by
  let Y (i j : BH G) : ℂ:= if parity i=ξ then C_U ((i,q)::(j,-q)::Z) else 0
  have he (x y : BH G) : Km 1 ξ 0 x y q * C_U ((x,q)::(y,-q)::Z) = HeatLine G 1 x y q*Y x y := by
    -- expose correct expression
    unfold Km Y pickLine; split; rfl; simp
  rw [at_trc]; simp_rw [he]; rw [sprint, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro i _; simp_rw [atAA, atUC, atCU]; unfold Y
  simp only [show ∀ (x:Axis), parity (Aℓ x i)= false from fun _=>rfl,show ∀ (x:Axis), parity (Uℓ x i) = true from fun _ => rfl,
    show parity (Cℓ i)=true from rfl]
  change (∑ a1:Axis,∑ b1:Axis, Lace 1 q a1 b1 * (if false=ξ then C_U (W a1 i q:: W b1 i (-q)::Z) else 0))+
    (∑ a1:Axis,( SpanH 1 q a1 * (if true=ξ then C_U (U a1 i q:: C i (-q):: Z) else 0) +
        SpanH 1 q a1 * (if true=ξ then C_U (C i q :: U a1 i (-q)::Z) else 0) ))=_
  cases ξ
  · simp only [if_true,Bool.true_eq_false,if_false,mul_zero,add_zero,sum_const_zero]; rw [gaugeSum]; cases σ <;> simp [bothTensor]
  simp only [if_true,Bool.false_eq_true,if_false,mul_zero,sum_const_zero,zero_add]; conv_lhs=> arg 2; ext; rw [add_comm];
  rw [ghost_sum]; cases σ <;> simp [bothTensor]
end YM.MS.ScaleForest.TwoPoint
