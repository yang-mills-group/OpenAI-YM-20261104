import YM.Contacts.Epochs.Dazzle
/-! # Timely openness and stitches. Does not solve global beta uniqueness; proves enough for
 real comparison journeys at every fixed polynomial tail.
 -/
noncomputable section
set_option autoImplicit false
namespace YM.PhysicalNext.Repeat.Legato.Euro
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open Concert ThroughLaunch Pressure Testing Contacts.Allium Contacts.Allium.Grant
open Contacts.Bounty.Trophy.Lore Contacts.Bounty.Trophy Contacts.Revest Contacts.Revest.Outlay
open Push.SectorMeasure Terrain ConnectedActivityE6 Blaze Contacts.Milling Sequin
variable {X:Gauge} (u: Passage G){m n i j x k N r:ℕ}{t z a:ℝ}
local notation "C" => u.A.B.a
local notation "S" => u.A.B.a.S
local notation "W" => u.A.B.a.clock
local notation "T" => u.T
local notation "U" => (u.T.history N n)
local notation "H" => u.A.B.a.clock.hatBeta
abbrev window (u:Passage G)(s j:ℕ): Prop:= 16*(j-s:ℕ) ≤ (u.A.B.a.clock.hatBeta s)
def jump (a:Levels G)(i:ℕ):= G.slopeConstant * Real.log (a.S.block i).val
lemma next : H (i+1) = H i+ jump C i := by unfold jump Calendar.hatBeta Levels.S; rw [Schedule.scale_succ]; ring -- import check
variable (h:G.Simple)
local notation "d" => G.slopeConstant
local notation "L" => u.A.B.a.S.block
lemma log_height (u:Passage G)(i:ℕ) : Real.log 3 ≤ Real.log ((u.A.B.a.S.block i).val:ℝ):= Real.log_le_log (by norm_num) (by exact_mod_cast u.A.B.a.S.block_large i)
lemma log_pos (u: Passage G)(i:ℕ): 0 <Real.log ((u.A.B.a.S.block i).val:ℝ) := (Real.log_pos (by norm_num : (1:ℝ)<3)).trans_le (log_height u i)
include h
lemma peak (hp:i ≤ N): |(u.T.history N n i).beta-H i| ≤ (H i)/4:= by
   let H₀(j):= H j; have hh(t): 1 < H t := (C).fits.delayed _; -- notation ( )
   suffices hg: |(U i).beta-H₀ i| ≤ (d/4)*(u.A.B.a.S.scale i) by exact hg.trans ( (by unfold Calendar.hatBeta; change _ ≤ (u.A.B.a.clock.bar+_)/4; linarith only [u.A.B.a.clock.bar_pos]))
   induction i with
   | zero=> have hx:(U 0).beta= (W).bar:= (T).choice.reaches N n; rw [hx]; simp [H₀,Calendar.hatBeta]
   | succ i ih=>
      have he:= ((u.T.sticks N n).persists i (Nat.zero_le _) hp).drift; let a:=G.slopeConstant / 4; rw [Schedule.scale_succ]; change _ ≤ a * _; have hc:=Drifting.pay u.A.B.valid i; have hv:= (div_le_iff₀ (log_pos u i)).mp hc; rw [show (U (i+1)).beta-H₀ (i+1)= (U i).beta-H₀ i+ ((U (i+1)).beta- (U i).beta-jump C i) from (by rw [show H₀ (i+1)= _ from Euro.next (u:=u) (i:=i)]; ring)]; apply (abs_add_le ..).trans; rw [mul_add]; exact add_le_add (ih (by omega)) (he.trans hv)

lemma monotone_hat : Monotone H:= monotone_nat_of_le_succ fun i=> by rw [Euro.next]; exact le_add_of_nonneg_right (mul_nonneg (Gauge.slopeConstant_pos h).le (log_pos u i).le)
lemma opens (hi:i≤j) (hW:window u i x): window u j x:= ((mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (by omega : x-j ≤ x-i)) (by norm_num: (0:ℝ)≤16))).trans (monotone_hat u h hi |>.trans' hW)
include h
lemma passport (hi:i≤N)(hb:window u i j)(h':|t-(U i).beta| ≤ 2* ((j-i:ℕ):ℝ)): t∈ band C i:= by
   have hv:=peak u h (n:=n) hi; obtain ⟨hx,he⟩:= abs_le.mp hv; obtain ⟨hy,hH⟩:= abs_le.mp h'; have hP:=(C).fits.delayed i; unfold window at hb; constructor <;> linarith only [hx,he,hy,hH,hb,hP] -- numeral casts?

omit h
set_option quotPrecheck false
-- budget iteration.PReq
variable (i j k l :ℕ) (a:ℝ)
local notation "u₀"=> (fun i=>(L i).val)
local notation "θ"=> (u.A.B.a.clock.allowance)
abbrev spend (u: Passage G)(i k:ℕ)(a t:ℝ):= retreat u.A i a t -- k not used
-- erase fields out of range
def grow (u:Passage G)(a:ℝ)(i j:ℕ): ℝ := if h:i<j then min (u.A.B.a.clock.allowance i) (Sequin.retreat u.A i a (grow u a (i+1) j)) else u.A.B.a.clock.allowance i
termination_by j-i
decreasing_by omega
-- actual heat positivity.Sector.
lemma cash (i:ℕ) : 0<θ i∧ θ i≤1:= by
    let x:=H i; have ht:1≤x:= ((C).fits.delayed _).le; have hh: 1≤ x^ (1/2:ℝ):= Real.one_le_rpow ht (by norm_num); have hv : 0< x^ (1/2:ℝ) := zero_lt_one.trans_le hh; have he: θ i = ((x^(1/2:ℝ))⁻¹)^((11:ℝ)/5):= by unfold Calendar.allowance Calendar.hatCoupling; rw [Real.sqrt_eq_rpow]
    rw [he]; have h':= inv_pos.mpr hv; exact ⟨Real.rpow_pos_of_pos h' _,Real.rpow_le_one h'.le (inv_le_one_of_one_le₀ hh) (by norm_num)⟩
lemma marchD : let v:= Real.log (u₀ i:ℝ); march (u.L.L ((C).clock.J (i+1)))= Real.exp (-v/2):= by
   rw [← Push.PriceCompiler.block_eq u.A.B.valid i]; intro v; unfold march; rw [Real.rpow_def_of_pos (by positivity)]; congr 1; unfold v; ring
lemma base (i:ℕ)(ht:i< j) : grow u a i j = min (θ i) (retreat u.A i a (grow u a (i+1) j)):= by rw [grow,dif_pos ht]
@[simp] lemma self (i:ℕ): grow u a i i= θ i:= by rw [grow,dif_neg (by omega)]
lemma rents (i): 0<grow u a i j∧ grow u a i j ≤ θ i:= by
   by_cases h:i≤ j
   swap; · rw [grow,dif_neg (by omega)]; exact ⟨(cash u i).1,le_rfl⟩
   induction h using Nat.decreasingInduction with
   | self=> rw [self]; exact ⟨(cash u _).1,le_rfl⟩
   | of_succ i h ih=>
       rw [base u j a i h]; refine ⟨lt_min (cash u i).1 ?_,min_le_left ..⟩; unfold retreat; rw [show march _= _ from marchD u i]; exact add_pos (Real.rpow_pos_of_pos (zero_lt_one.trans (u.A.B.a.fits.delayed i)) _) (mul_pos (Real.exp_pos _) ih.1)
end YM.PhysicalNext.Repeat.Legato.Euro
