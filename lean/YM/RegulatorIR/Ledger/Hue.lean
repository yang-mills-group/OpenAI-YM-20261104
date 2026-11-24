import YM.RegulatorIR.Ledger.Turn

/-! Finite-top qualitative decay expressed with two chosen powers: `γ` for
propagated charge and arbitrary image exponent b. No scalar Faddeev-Popov
integral estimate yet involved. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Ledger.Sky
open Budget Budget.Packet Budget.Tariff Budget.Layer Budget.Tuple Budget.Deck Uniform Uniform.Post Function Step Diagram Gradient ENNReal Spatial
open scoped Topology ENNReal NNReal BigOperators Classical
variable {W:Type}{M: W→ℕ}{X Y:Page M→Type} (S:Sky X Y)
variable {k j:Choice M} {γ K:ℝ}{p α h b u:ℕ}{L:Meter W} {c:Flap M→ℝ≥0∞}

def ε (w) := S.l (Page.opening M w)
def shift (t:Flap M) : ℝ := S.l t.next / S.l t.prev
lemma one_le_shift (t):1≤ S.shift t:=(one_le_div (S.hl _)).mpr (S.climb _)
lemma shift_pos (t):0<S.shift t:=lt_of_lt_of_le zero_lt_one (S.one_le_shift t)
lemma shift_up (t): S.l t.next=S.shift t* S.l t.prev:= (div_mul_cancel₀ _ (S.hl _).ne').symm

def softnessWeight (γ:ℝ)(w: Page M) := ENNReal.ofReal (S.l w^γ)
def priceStep (b:ℕ) (γ:ℝ) (k:Choice M) (t:Flap M) := if k.age t.volW≤ t.offset then ENNReal.ofReal ((S.l t.prev^γ)⁻¹) else ENNReal.ofReal ((S.l t.prev^b)⁻¹)

/-- period exponent may take any 0<γ≤1 on which propagation is paid. -/
structure Radiants (L:Meter W) (γ:ℝ)(u α:ℕ)(c:Flap M→ℝ≥0∞) (k:Choice M): Prop where
 ref_mesh : ∀ w,S.l (k.choose w)=1
 gleams : 0<γ
 small : γ ≤ 1
 scale : Poly (flapL M L) (fun w=>ENNReal.ofReal (S.shift w))
 lead : S.Lead u c
 cold : ∀ w,c w ^ α ≤ ENNReal.ofReal ((S.shift w ^ γ)⁻¹)
 side : ∀ w,1 ≤ S.P w

lemma warmer (g:S.Radiants L γ u α c k) : S.Softness u L c (S.softnessWeight γ) α:= by
 have hS w:= S.hl w; have hP w:0<S.l w^γ:= Real.rpow_pos_of_pos (hS w) _
 refine ⟨g.lead,fun w=> (ENNReal.ofReal_pos.mpr (hP w)).ne', fun _=> ENNReal.ofReal_ne_top, ?_, ?_, fun w=> ofReal_le_ofReal (Real.rpow_le_rpow (hS _).le (S.climb w) g.gleams.le)⟩
 · intro w
   have h:= g.cold w; have hQ:= S.shift_pos w; have hx:= hP w.next
   apply (mul_le_mul_left h _).trans_eq _; unfold softnessWeight
   rw [← ENNReal.ofReal_mul (by positivity), shift_up S,Real.mul_rpow hQ.le (hS _).le,← mul_assoc,inv_mul_cancel₀ (by positivity),one_mul]
 apply g.scale.mono
 intro w; have he:= S.shift_pos w
 apply le_trans _ (ofReal_le_ofReal (Real.rpow_le_self_of_one_le (S.one_le_shift w) g.small))
 change (S.softnessWeight γ w.prev)⁻¹*S.softnessWeight γ w.next ≤ ENNReal.ofReal (S.shift w ^ γ)
 unfold softnessWeight; rw [mul_comm,← div_eq_mul_inv,← ENNReal.ofReal_div_of_pos (hP _),shift, Real.div_rpow (hS _).le (hS _).le]

lemma soften (g: S.Radiants L γ b α c k) (he: u≤b): S.Radiants L γ u α c k:=
 { g with lead:={ g.lead with down:=fun w=> Layer.row_mono (A:=S.ceilingRoom.cone b w) (fun _ _=> Tariff.moment_mono (S.high w) he dist_nonneg) (g.lead.down w) } }

namespace Radiants
variable {S} (g:S.Radiants L γ u α c k)
include g
lemma crest (i:Page k.before.spans) : S.l (k.before.page i) ≤ 1:= by
 have h:= (k.before.expanse S).tails i
 change S.l (k.before.page i) ≤ S.l (k.before.page (k.lastPage i.bindW)) at h
 rw [k.meet,g.ref_mesh] at h; exact h
lemma crested (i:Page k.after.spans) : 1 ≤ S.l (k.after.page i):= by
 have h:= (k.after.expanse S).heads i
 change S.l (k.choose i.bindW) ≤ _ at h; rw [g.ref_mesh] at h; exact h
omit g in
lemma rearward (t:Flap M)(he: k.age t.volW ≤ t.offset): ∃ i:Flap k.after.spans,k.after.wing i=t:=by
 rcases t with ⟨w,n,H⟩
 change k.age w≤n at he
 refine ⟨⟨w,n-k.age w,by change n-k.age w<M w-k.age w; omega⟩, by simp [Choice.after,Era.wing,Nat.add_sub_of_le he]⟩
omit g in
lemma front (t:Flap M)(he:t.offset < k.age t.volW) :∃ i: Flap k.before.spans, k.before.wing i=t:=by rcases t with ⟨w,n,H⟩;exact ⟨⟨w,n,he⟩,by simp [Choice.before,Era.wing]⟩
end Radiants

end YM.RegulatorIR.Ledger.Sky
