import YM.RegulatorIR.Momentum.Crucible

/-!
# Meter-age recurrence

Λ can be offset by a sufficiently large constant at each fixed order to
absorb adjacent-age growth. Thus a pre-block damping needn't meet unbounded
log powers. Smoothing & rank demands still explicit. This module separates
`ℓ-budget` from the final uniform in geometric families. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
namespace YM.RegulatorIR.Epoch
open Function Finset Filter Set YM.RegulatorIR.Ledger Uniform
open ENNReal
open scoped Topology ENNReal NNReal BigOperators Classical
variable {X:Type}{M:X→ℕ}{k p:ℕ}{γ θ A v:ℝ}
lemma renewed {L T:Meter X}{f:X→ℝ≥0∞}(he:Poly L f)(hp:Poly T L.val) : Poly T f:=by obtain ⟨c,p,hc,H⟩:=he; exact ((Poly.standard _ hc).mul (hp.powQ p)).mono H
lemma refreshed {L T:Meter X}{v f:X→ℝ≥0∞}(he:Carry L v f)(hp:Poly T L.val) : Carry T v f:=by obtain ⟨c,H,h⟩:=he; exact ⟨c,renewed H hp,h⟩
lemma scalar_buy {L:Meter X}{M:X→ℝ≥0∞}{x:ℝ}(hx:0≤x)(H: Uniform.Poly L M) : Uniform.Poly L fun w=> M w ^x:=by
 let s:=⌈x⌉₊; have h:x ≤ s:=Nat.le_ceil _
 apply Poly.mono ((Poly.oneQ L).add (H.powQ s));intro w;change M w^x ≤ 1+ M w^s;rcases le_total (M w) 1 with h₁|h₁
 · exact (ENNReal.rpow_le_one h₁ hx).trans le_self_add
 exact (ENNReal.rpow_le_rpow_of_exponent_le h₁ h |>.trans_eq (by rw [ENNReal.rpow_natCast])).trans le_add_self

-- circumference prices. Parameter is common length; holds post affordability
structure Marked (M:X→ℕ) where
 l : Page M→ℝ
 gap : Flap M→ℝ
 Z : X → ℝ
 cap :∀ w,0 ≤ Z w
 live :∀ i,0<l i
 steps i : l i.next=l i.prev * gap i
 distant i : 2≤ gap i
namespace Marked
variable (S : Marked M)
def peak (i:Page M):ℝ:= Real.log (S.l i)
def slope (i:Flap M): ℝ:= Real.log (S.gap i)
def credit (i:Page M):=1+S.Z i.bindW+|S.peak i|
lemma ahead i : 1≤ S.credit i:=le_trans (le_add_of_nonneg_right (S.cap i.bindW)) (le_add_of_nonneg_right (abs_nonneg _))
def age_t : Meter (Page M) := ⟨fun i=> ENNReal.ofReal (S.credit i),fun i=>by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (S.ahead i),fun _=>ENNReal.ofReal_ne_top⟩
def age_f : Meter (Flap M) := S.age_t.us Flap.prev
def age_c : Meter (Flap M):=S.age_t.us Flap.next
lemma min_gap i : 0< S.gap i:= lt_of_lt_of_le (by norm_num) (S.distant i)
lemma mark_P (i:Flap M): S.peak i.next=S.peak i.prev+S.slope i:=by rw [peak,S.steps, Real.log_mul (S.live _).ne' (S.min_gap _).ne'];rfl
lemma incline (i): Real.log 2≤ S.slope i:= Real.log_le_log (by norm_num) (S.distant i)
lemma rise (i) :0 < S.slope i:= (Real.log_pos (by norm_num : (1:ℝ)<2)).trans_le (S.incline i)
lemma goes_c (i:Flap M): S.credit i.next ≤ S.credit i.prev+S.slope i:=by unfold credit;rw [S.mark_P]; have he:= abs_add_le (S.peak i.prev) (S.slope i); rw [abs_of_nonneg (S.rise i).le] at he; rw [add_assoc (1+ S.Z i.prev.bindW)];exact add_le_add_right he _
lemma goes_f (i:Flap M): S.credit i.prev≤S.credit i.next+S.slope i:=by
 unfold credit
 have he:= abs_sub (S.peak i.next) (S.slope i)
 rw [S.mark_P,add_sub_cancel_right,← S.mark_P,abs_of_nonneg (S.rise i).le] at he; rw [add_assoc (1+S.Z i.next.bindW)];exact add_le_add_right he _

def day (i:Flap M):ℝ≥0∞:= ENNReal.ofReal (S.gap i)
lemma exp_day (i:Flap M)(θ:ℝ): ENNReal.ofReal (Real.exp (S.slope i*θ))=S.day i^θ:=by rw [day,slope,← Real.rpow_def_of_pos (S.min_gap i), ENNReal.ofReal_rpow_of_pos (S.min_gap _)] -- unfolded? fix
lemma day_v (i): 2 ≤ S.day i:= by change (2:ℝ≥0∞)≤ ENNReal.ofReal _;rw [← show ENNReal.ofReal 2=2 from by simp]; exact ENNReal.ofReal_le_ofReal (S.distant i)
lemma dp (i): S.day i ≠ ⊤:=ENNReal.ofReal_ne_top
lemma hp(i): S.day i≠0:= (lt_of_lt_of_le (by norm_num) (S.day_v i)).ne'
-- bounding at next.W: age_plus ≤ Ly(wait)>? gap assumed polynomial both directions? by comparing to Ly uses log but atTop smoothing patch may grow exponentially beyond y.Plol. impose obligations.
structure Structural : Prop where
 fromF : Poly S.age_f S.day
 fromC : Poly S.age_c S.day
lemma utilizes (h:S.Structural):Poly S.age_f S.age_c.val:=by
 refine ((Poly.roof S.age_f).add h.fromF).mono ?_
 intro w; have ht:= S.goes_c w; have hx:S.slope w≤S.gap w:= by unfold slope; linarith [Real.log_le_sub_one_of_pos (S.min_gap w)]
 exact (ENNReal.ofReal_le_ofReal (ht.trans (add_le_add_right hx _))).trans ENNReal.ofReal_add_le
lemma advertises (h:S.Structural):Poly S.age_c S.age_f.val:=by
 refine ((Poly.roof S.age_c).add h.fromC).mono ?_
 intro w; have ht:= S.goes_f w; have hx:S.slope w≤S.gap w:=by unfold slope;linarith [Real.log_le_sub_one_of_pos (S.min_gap w)]
 exact (ENNReal.ofReal_le_ofReal (ht.trans (add_le_add_right hx _))).trans ENNReal.ofReal_add_le
end Marked
end YM.RegulatorIR.Epoch
