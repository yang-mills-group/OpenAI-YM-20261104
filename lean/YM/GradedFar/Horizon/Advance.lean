import YM.GradedFar.Books.Balance
/-!
# A planned hypothesis expenditure toward G.6: need G.2 powers.
Can already derive them from the step G.1 receipts. Degree budgets
are prescribed by `H`, not guessed.
-/
namespace YM.FVA2.GradedFar.Horizon
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus XSpace.Rose
open O O.Score O.Enh O.Canon Scale Dframe Jury Facets Growth Pose Moving
open MS.Book.Program
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n d e : ℕ} {I J : Type} {p : ℕ} (T : Filter I) (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G
local notation "ν"=> Teller.logNu 1
open Reg.Point (stepV)
local notation "xρ"=>Books.rootPoints
variable {simple : G.Simple} {A : Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)

include H
lemma origin (s : ℝ) (d : ℕ) : coeff 0 (Kseries N M d s)=Level.Dial d s ∧ coeff 1 (Kseries N M d s)=0 := by
    let h:= H.details.toServed.toPosted.toQuoted.toContract.toMission.born
    rw [coeff_K,coeff_K,(H.dilation ν).check.paid s d|>.zero,mul_one,
      Generator.Q.lifted ν N.scheme N.criterion M A s simple h.Taylor h.still h.base,mul_zero]
    exact ⟨rfl,rfl⟩
lemma first_pay (s : ℝ) (d : ℕ) (x : ℂ) : crank N M d s 1 x=engine G d s := by
    unfold crank blend; simp only [Finset.sum_range_succ, names, (origin N M H ..).1,(origin N M H ..).2, pow_zero, one_smul]; simp; ext; simp
-- frame cost orientation both ways PFrame Z exact. ensure Y's projections.
variable (θ:ℝ→ℝ) (Z:Rolled G d) (h : PFrame N M (Zenith Z) θ 1)
include h
lemma step_fee : ∃ C : ℝ,0<C ∧ ∀ᶠ r in τ,∀ s∈Growth.Small,
    ‖Zenith Z r s-engine G d s‖≤ C*g r^2 ∧ ‖downward Z r s-engine G d (-s)‖ ≤ C*g r^2 := by
    obtain ⟨C,hC,hc⟩:= h
    refine ⟨2*C,by positivity,?_⟩
    have hu : Tendsto (fun r : ℝ=> C*g r^2) τ (𝓝 0):= by simpa using ((shrink simple).pow 2).const_mul C
    filter_upwards [hc,positive_g simple, hu.eventually_lt_const (by norm_num : (0:ℝ)<1/2)] with r hr hs he s h
    have hD:=hr s h; rw [frame_err, first_pay N M H] at hD;
    let X:=engine G d s; let Y:= engine G d (-s); let L:=Zenith Z r s; let P:=downward Z r s
    have hY: ‖Y‖≤1:= engine_neg_bound _ (neg_nonpos.mpr h.1) d
    have hx : Y*X=1:= by unfold X Y; rw [← engine_sum, neg_add_cancel, engine_zero]
    have hl : L*P=1:= (inverse_ok ..).1
    have hh : ‖P-Y‖ ≤ ‖Y‖ * (C*g r^2)*‖P‖ := by
      rw [show P-Y=Y*(X-L)*P from (by rw [mul_sub,sub_mul,hx,one_mul,mul_assoc,hl,mul_one])]
      refine (norm_mul_le ..).trans (mul_le_mul_of_nonneg_right ((norm_mul_le ..).trans ?_) (norm_nonneg _))
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); rw [norm_sub_rev]; exact hD
    constructor
    · calc
         ‖_‖ ≤ _ := hD
         _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [hC]) (show 0 ≤ g r^2 by positivity)
    apply hh.trans
    let D:= ‖P‖
    have h' : ‖P‖ ≤ 2 := by
      have he' : ‖Y‖*(C*g r^2) ≤ 1/2:= (mul_le_mul hY he.le (by positivity) zero_le_one).trans_eq (one_mul _)
      have he'' := hh.trans (mul_le_mul_of_nonneg_right he' (norm_nonneg _))
      have hk := norm_add_le (P-Y) Y; rw [sub_add_cancel] at hk; linarith
    exact (mul_le_mul (mul_le_mul_of_nonneg_right hY (show 0 ≤ C*g r^2 by positivity)) h' (norm_nonneg _) (by positivity)).trans_eq (by ring)
end
end YM.FVA2.GradedFar.Horizon
