import YM.FVA2.Rank.Pins
import YM.FVA2.Scale.System
import Mathlib.RingTheory.PowerSeries.Expand
/-!
# κ with honest MS parameter convention at *every* order

Hence `Book` parity at the actual prescription as well, not some choice of witness. Pol log costs exact.
These two compressed series are in the squared variable. We specify inverse-square-root by the two
unit relationships at all orders including leading normalization. This is formal scaling, not a gauge G
change. Use `Change.literal_clock` for its effect on lattice actions. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Hue.Agent.Kappa
open Function Filter Set Finset MeasureTheory
open MS MS.Plane MS.Arts MS.Koszul MS.Book MS.Book.Convolve MS.Book.Program MS.High MS.Tone MS.Local.Physical MS.Puff MS.Menus MS.Wind
open MS.Land MS.Outlook
open PowerSeries
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{p:Team}{B:Deck G}{J: Booked B}{Y:LitBook B}{M:MS_Data G J}{U:FullBook B}{F:Land.Prescription B}
noncomputable def root (p:Team)(t:ℝ) : Cn := PowerSeries.mk fun n=> coeff (2*n+1) (shift p t)
noncomputable def tuning (p:Team)(t:ℝ): Cn := PowerSeries.invOfUnit ( root p t ^ 2 ) 1
lemma grows (p:Team): Ren (root p):= fun i=> by simp_rw [root, coeff_mk]; exact shiftR p _
lemma scaleK (p:Team): Ren (tuning p):= Ren.inv (Ren.pow (grows p) _)
lemma lead (p:Team)(t:ℝ): Low (root p t):= by simp [Low,root,ann]
lemma origin (p:Team)(t:ℝ): Low (tuning p t):= by simp [Low, tuning, coeff_zero_eq_constantCoeff]
lemma sq (p: Team)(t:ℝ): root p t ^ 2 * tuning p t=1:= by apply PowerSeries.mul_invOfUnit; have hp:= lead p t; rw [Low,coeff_zero_eq_constantCoeff_apply] at hp; simp [hp]
lemma long (H:∀ i,Spare i (p i)) (t:ℝ): shift p t=expand 2 (by decide) (root p t)*X := by
    apply PowerSeries.ext; intro i; cases i with
    | zero=> rw [share, coeff_zero_eq_constantCoeff_apply]; simp
    | succ i=> rw [ coeff_succ_mul_X, coeff_expand ]; split
               next ht => rw [ root,coeff_mk,show 2*(i/2)=i from Nat.mul_div_cancel' ht]
               next ht=> exact shift_b t ( show Wage (i+1) p from fun i _=> H i) (i+1) (le_refl _) (by omega)
-- `shift^2 * κ(g²)`.
lemma square (H:∀ i,Spare i (p i))(t:ℝ): shift p t ^2 * ( tuning p t ).subst (X^2:Cn) = X^2 := by
    rw [ ← expand_apply 2 (by decide), long H,mul_pow,mul_right_comm,← map_pow,← map_mul,sq,map_one,one_mul ]
structure Correct (p:Team): Prop where
    tone (i:ℕ): Spare i (p i)
    rise : Ren (tuning p) ∧ Ren (root p)
    pays t: Low (root p t) ∧ Low (tuning p t) ∧ (root p t)^2 * tuning p t=1
    arrives t: shift p t=(root p t).subst (X^2:Cn)*X ∧ shift p t ^2 * (tuning p t).subst (X^2:Cn)=X^2
lemma sits (h:∀ i,Spare i (p i)): Correct p:= ⟨h,⟨scaleK _, grows _⟩, fun _=> ⟨lead ..,origin ..,sq ..⟩,fun x=>⟨by rw [long h,expand_apply], square h x⟩⟩
theorem standard (h:G.Simple)(hF:TaylorOK M Y F): Correct F.team := sits (Signal.all h M.bulkOK hF.bulk)
theorem standardF (h:G.Simple)(hF:TaylorOKF M U F): Correct F.team := sits (Signal.all h M.bulkOK hF.bulk)
theorem any (h:G.Simple)(dial:Bool) (P:Continuum.Continuation G): Correct ( P.proofStart h dial ).team:= standard h (P.plan h dial).taylor -- check
open XSpace XSpace.Normalize XSpace.Structure1
variable (h:G.Simple)(Y:Initialize G){V: Store G}(K:Rose.Pick V)
variable (T: MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
local notation "£"=> ( Reg.supplies Y T )
include h
lemma solves {K:Rose.Pick V} (S:Land.Prescription (Press.portDeck G)) (H:_root_.YM.FVA2.Scale.System.Contract Y K T S): Correct S.team:= standardF h H.toMission.born.1
/-- Includes κ check -/
theorem converter (dial:Bool): ∃ S:Land.Prescription (Press.portDeck G), S.team=( Continuum.Continuation.proofStart h ( Reg.supplies Y T ) dial).team ∧ _root_.YM.FVA2.Scale.System.Contract Y K T S ∧ Correct S.team := by
 obtain ⟨S,hX,hT⟩:= _root_.YM.FVA2.Scale.System.converter Y K T h dial; exact ⟨S,hX,hT, solves h Y T S hT⟩
end YM.FVA2.Hue.Agent.Kappa
