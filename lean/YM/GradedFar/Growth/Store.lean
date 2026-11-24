import YM.GradedFar.Growth.Local

/-!
# Iterating the error estimates on the chain

Use a simple coarser exponent: the iteration may pay a power of T even on clocks.
But payable by raising precision since exponent isn't m-dependent. Need that raising
before getting sharp matrix norm information down the whole line.
-/
namespace YM.FVA2.GradedFar.Growth
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Scale Dframe Jury
open Continuation
open scoped Topology BigOperators Classical ContDiff
open MS.Book.Program
variable {G : Gauge} {n d : ℕ} {I J E : Type} (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G
lemma bill_norm {E : Type} [NormedAddCommGroup E] {Q : Board I} {p : ℕ} {C : ℝ} {F : I → E} : Bill Q p C (fun i=> ‖F i‖) ↔ Bill Q p C F := by simp only [Bill,Real.norm_of_nonneg (norm_nonneg _)]
lemma bill_save {Q : Board I} {F T : I → ℝ} {p : ℕ} {C : ℝ} (h : Bill Q p C F) (ht : ∀ᶠ i in Q.l,T i ≤ F i) :
    Bill Q p C (fun i=> max (T i) 0) := by
    refine h.of_le ?_; filter_upwards [ht] with i hi
    rw [ Real.norm_of_nonneg (show 0 ≤ max (T i) 0 from le_max_right ..),Real.norm_eq_abs]
    exact max_le (hi.trans (le_abs_self _)) (abs_nonneg _)

variable {simple : G.Simple} {A : Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
variable (Z : Coven G d) (θ : ℝ→ℝ) (ht : Tendsto (fun r=>θ r/gYM G r) τ (𝓝 1))
    (Q : Loft G I) (s z : I → ℝ) (hs : Q.Mid s) (hz : ∀ᶠ i in Q.path, z i∈Small)
local notation "W"=> Q.board simple
include H ht hs hz

variable (p : ℕ)
local notation "theta"=> theta_err N M θ p
local notation "era"=> frame_err N M Z θ p

def leap_t (r s z : ℝ) := theta_err N M θ p r (s+z) - 2*theta_err N M θ p r s

theorem clock_iter (hp : 1≤p) (h : PTheta N M θ p) : Bill W (p+1) 0 (fun i=> max (leap_t N M θ p (Q.r i) (s i) (z i)) 0) := by
    have he:=relay_clock N M H Q s hs _ (start_theta N M H θ ht Q) z (mid_case N M H Q s z hs hz) p
    apply bill_save ((through_theta N M H θ Q s z hs hz _ h).plus (bill_norm.mpr he)); filter_upwards [
      (partial_nears N M H θ ht Q s hs p).eventually (bends_price N M H p hp), hz] with i hi hk
    let q := Q.r i; let v:=θ q; let r:=q * exp (s i); let w:=r*exp (z i)
    let X := bend N M (z i) p (bend N M (s i) p v)
    let A' := bend N M (z i) p (θ r:ℂ)
    let Y := bend N M (s i+z i) p (v:ℂ)
    let Z' : ℂ := θ w
    have hq :‖A'-X‖≤ 2 * theta q (s i) := hi (z i) hk
    have hw : q*exp (s i+z i)=w:= by unfold w r; rw [exp_add,mul_assoc]
    have hy : ‖Z'-Y‖≤ ‖Z'-A'‖+2*theta q (s i)+‖X-Y‖ := by
      rw [show Z'-Y=(Z'-A')+(A'-X)+(X-Y) by abel]; exact (norm_add_le ..).trans (add_le_add_left ((norm_add_le ..).trans (add_le_add_right hq _)) _)
    unfold leap_t; conv_lhs => left; unfold theta_err
    change ‖(θ (q*exp (s i+z i)):ℂ)-Y‖ - 2*_ ≤ ‖Z'-A'‖+‖X-Y‖
    rw [hw]; change ‖Z'-Y‖ - 2*theta q (s i) ≤ _; linarith only [hy]

def leap_f (Y A : ℝ) (r s z : ℝ) := frame_err N M Z θ p r (s+z) - Y* frame_err N M Z θ p r s - A * ‖crank N M d s p (θ r:ℂ)‖ * theta_err N M θ p r s
-- need constant bounds once after p (Y alone even before!)
theorem frame_iter (Y A : ℝ)
    (he : ∀ᶠ z:ℂ × ℂ in 𝓝 0,∀ i∈Small, ‖crank N M d i p z.1-crank N M d i p z.2‖ ≤ A * ‖z.1-z.2‖)
    (hq : Kind Z Y) (hv : travels Z) (h : PFrame N M Z θ p) :
    Bill W (p+1) (-(d:ℝ) + -(d:ℝ)) (fun i=> max (leap_f N M Z θ p Y A (Q.r i) (s i) (z i)) 0) := by
    have hi:=crank_paid N M H Q s hs _ (start_theta N M H θ ht Q) p d
    have hh:=through_frame N M H Z θ Q s z hs hz p h
    have hp:=relay_frame N M H Q s hs _ (start_theta N M H θ ht Q) z (mid_case N M H Q s z hs hz) p d
    have hs':=(product_fe W (bill_norm.mpr hi) hh).mono_fee (a:=-(d:ℝ)+0) (v:=-(d:ℝ) + -(d:ℝ)) (by have : 0 ≤ (d:ℝ) := Nat.cast_nonneg d; linarith) (show p+1 ≤ 0+(p+1) by omega)
    apply bill_save (hs'.plus (bill_norm.mpr hp)); filter_upwards [
      (partial_nears N M H θ ht Q s hs p).eventually he,(Q.soon simple hs).eventually hq,hz] with i hE hA hi
    let q := Q.r i; let r:=q*exp (s i); let v:=θ q; let w:= r*exp (z i)
    let L := crank N M d (s i) p (v:ℂ); let D:= Z q (s i)
    let R := crank N M d (z i) p (θ r:ℂ); let J:= Z r (z i)
    let H := crank N M d (z i) p (bend N M (s i) p (v:ℂ)); let P:= crank N M d (s i+z i) p (v:ℂ)
    have hZ := hv.2 q (s i) (z i)
    have hf : ‖R-H‖ ≤ A * theta q (s i):= hE (z i) hi
    have hh : ‖J‖ ≤ Y:= hA (z i) hi
    have hL : ‖D-L‖= era q (s i):= rfl
    have hR : ‖J-R‖=era r (z i):= rfl
    have hl : ‖(D-L)*J‖ ≤ Y*‖D-L‖ := (norm_mul_le ..).trans ((mul_le_mul_of_nonneg_left hh (norm_nonneg _)).trans_eq (mul_comm ..))
    have hr : ‖L*(J-H)‖ ≤ ‖L‖*(‖J-R‖ + A * theta q (s i)) := by
      apply le_trans (norm_mul_le ..); apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); rw [show J-H=J-R+(R-H) by abel]; exact (norm_add_le ..).trans (add_le_add_right hf _)
    have hw := (norm_add_le ((D-L)*J + L*(J-H)) (L*H-P))
    have hw' := norm_add_le ((D-L)*J) (L*(J-H))
    unfold leap_f; conv_lhs => left; left; unfold frame_err
    rw [hZ]; change ‖D*J-P‖-Y*‖D-L‖-A*‖L‖ * theta q (s i) ≤ ‖L‖*‖J-R‖+‖L*H-P‖
    rw [show D*J-P=(D-L)*J+L*(J-H)+(L*H-P) by rw [mul_sub,sub_mul]; abel]
    nlinarith only [hr,hl,hw',hw]
end
end YM.FVA2.GradedFar.Growth
