import YM.GradedFar.Purchase
import YM.GradedFar.Center
/-!
# Housing for HorizonFork: both evolving zones of the actual measurement
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Fork
open Filter Finset Function Set Spec Table Extraction OPE OPE.Orbits OPE.Log
open Trace.Pilot PhysMS XSpace XSpace.Normalize FVA2.GradedFar
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}{F:Final C f S}
    {A B:Type*} {α:Filter A} {U:A→B→Prop} {L W r s:A→B→ℝ} {I J:Type}[Fintype I][Fintype J]{d:I→ℕ}{e:J→ℕ} {M δ:ℝ}
    {P:A→B→Purchase F I J}
def smallLength (P:A→B→ Purchase F I J) (a:A)(z:B):=(P a z).logFrom
namespace Purchase
def head (p:Purchase F I J) := move p.center p.logFrom p.x
def tail (p:Purchase F I J) (t:ℝ) := move p.center t p.y
end Purchase
structure Labor (M δ:ℝ) (α:Filter A)(U:A→B→Prop)(L:A→B→ℝ)(s:A→B→ℝ)(P:A→B→Purchase F I J) : Prop where
    tiny : Bedroom α U L (smallLength P)
    large : Bedroom α U L s
    trailbound : ∀ᶠ a in α,∀ z,U a z→ duo (s a z) (P a z) ≤ L a z
    setting : ∀ᶠ a in α,∀ z,U a z→ Ready M δ (s a z) (P a z)
    nonneg : 0≤M
    clearance : 0<δ
namespace Labor
variable (l:Labor M δ α U L s P)
include l
-- transfers to Launch, with actual physical coordinates centered at o
omit [Fintype I] [Fintype J] in
lemma near : ∀ᶠ a in α,∀ z,U a z→ Tiny M δ (smallLength P a z) ⟨(P a z).head,(P a z).center⟩ := by
  apply l.setting.mono; intro a ha z he; let r:=(P a z).logFrom
  obtain ⟨hr,hs,hx,hg⟩:=ha z he; constructor
  · intro i; change ‖_+ r • _ -_‖≤ _; rw [add_sub_cancel_left,norm_smul,Real.norm_of_nonneg hr.le]; rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hx.xhome i) hr.le
  intro i j hi; unfold Purchase.head move; rw [add_sub_add_left_eq_sub,← smul_sub, norm_smul,Real.norm_of_nonneg hr.le]
  rw [mul_comm]; exact mul_le_mul_of_nonneg_left (hx.xclear i j hi) hr.le

omit [Fintype I] [Fintype J] in
lemma inserted : ∀ᶠ a in α,∀ z,U a z→ WithinRoom (s a z) M δ
    (beside (sole (P a z).center) ((P a z).tail (s a z))) (P a z).center := by
  refine l.setting.mono ?_; intro a ha z he; let t:=s a z; let y:=(P a z).y; obtain ⟨hr,ht,hx,hg⟩:= ha z he
  have hp:=hr.trans_le ht; let o:=(P a z).center
  have h(j:J):δ*t≤‖o+t • y j-o‖:= by
    rw [add_sub_cancel_left,norm_smul,Real.norm_of_nonneg hp.le,mul_comm]
    exact mul_le_mul_of_nonneg_left (show δ≤‖y j‖ from by linarith [hx.away j,l.clearance]) hp.le
  constructor
  · rintro (i|j)
    · change ‖o-o‖ ≤ _; exact (by rw [sub_self,norm_zero]; exact mul_nonneg l.nonneg hp.le)
    change ‖o+t • y j-o‖ ≤ _; rw [add_sub_cancel_left,norm_smul,Real.norm_of_nonneg hp.le,mul_comm]; exact mul_le_mul_of_nonneg_right (hx.zhome j) hp.le
  rintro (⟨⟩|i) (⟨⟩|j) ne
  · exact (ne rfl).elim
  · rw [norm_sub_rev]; exact h j
  · exact h i
  change _ ≤ ‖o+t • y i-(o+t • y j)‖; rw [add_sub_add_left_eq_sub,←smul_sub,norm_smul,Real.norm_of_nonneg hp.le,mul_comm]
  exact mul_le_mul_of_nonneg_left (hx.zclear i j (fun h=>ne (congrArg Sum.inr h))) hp.le
lemma common : ∀ᶠ a in α,∀ z,U a z → Injective (beside (P a z).head ((P a z).tail (s a z))) ∧
    Injective (beside (sole (P a z).center) ((P a z).tail (s a z))) := by
  refine l.setting.mono ?_; intro a ha z hz; obtain ⟨hr,ht,hx,hg⟩:= ha z hz; exact
    ⟨full_layout _ hx l.clearance hr ht hg, center_layout _ (hr.trans_le ht) l.clearance hx.away hx.zclear⟩
end Labor

-- General cost transfer from joint homogeneous prices. Allows even `s = s(t)` & partner
-- radius specified by a profile/subquery; preserve the exponent independent of their variation.
lemma pull {G E : Type*}[Norm E] {w R:ℝ→G→ℝ} {H:ℝ→G→Prop}{g:ℝ→G→E}
    (ht:Sold trail H R w g) (hL:Bedroom α U L s) {z:A→B→G}
    (hQ:Safe trail H R w)(h:∀ᶠ a in α,∀ x, U a x → H (s a x) (z a x))
    (hv:∀ᶠ a in α,∀ x,U a x→ R (s a x) (z a x) ≤ L a x):
    Sold α U L (fun a x=> w (s a x) (z a x)) (fun a x=>g (s a x) (z a x)):=by
  obtain ⟨k,b,hb,hq⟩:= ht; refine ⟨k,b,hb,?_⟩; filter_upwards [hL.1 _ (hq.and hQ),h,hv] with a hr ha hv x hx
  obtain ⟨h₁,h₂⟩:= hr x hx; specialize hv x hx; obtain ha:=ha x hx; obtain ⟨hl,hw⟩:= h₂ _ ha
  exact (h₁ _ ha).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans hl) hv _) hb) hw)
omit [Fintype I] [Fintype J] in
lemma pullLabor {w:ℝ→Purchase F I J→ℝ}{E:Type*}[Norm E] {g:ℝ→Purchase F I J→E}
    (l:Labor M δ α U L s P) (H:Sold trail (Ready M δ) duo w g)(hW:Safe trail (Ready M δ) duo w) :
    Sold α U L (fun a z=> w (s a z) (P a z)) (fun a z=>g (s a z) (P a z)):= pull H l.large hW l.setting l.trailbound
omit [Fintype I] [Fintype J] in
lemma pullNear {w:ℝ→Launch I→ℝ}{E:Type*}[Norm E] {g:ℝ→Launch I→E}
    (l:Labor M δ α U L s P) (H:Sold trail (Tiny M δ) TagCost w g)(hW:Safe trail (Tiny M δ) TagCost w) :
    Sold α U L (fun a z=> w (smallLength P a z) ⟨(P a z).head,(P a z).center⟩)
    (fun a z=> g (smallLength P a z) ⟨(P a z).head,(P a z).center⟩):=
  pull H l.tiny hW l.near (l.tiny.2.mono fun _ h a ha=> (h a ha).2)
end YM.Integration.GradedFar.Fork
