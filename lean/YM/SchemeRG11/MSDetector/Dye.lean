import YM.SchemeRG11.MSDetector.Corner
/-!
Throughout use the EXACT physical trace-normalized color basis of the baseline
G, not negative Killing normalization without specified conversion. δcontractions
algebra and Lorentz projection. -/
set_option autoImplicit false
set_option maxHeartbeats 220000
noncomputable section
namespace YM.SchemeRG11.MSDetector
open Hot Maxwell Analysis Set MeasureTheory Metric Function Filter TopologicalSpace Cluster Steam MSbar Pert Triangle Storm Flare Asymptotics
open scoped Topology ContDiff BigOperators Real RealInnerProductSpace Matrix.Norms.Frobenius

namespace Chroma
variable {G : Gauge}
lemma flip (a b c : G.ColorIndex) : colorF b a c= -colorF a b c := by
  unfold colorF; rw [show ∀ x y : G.Color,G.ad y x=-(G.ad x y) by
                      intro x y; apply G.colorMat_injective; rw [map_neg,G.colorMat_ad,G.colorMat_ad,neg_sub]]; rw [inner_neg_left]
lemma swing (a b c : G.ColorIndex) : colorF a b c=colorF b c a := by
  unfold colorF; apply mul_left_cancel₀ (show (G.repDim:ℝ)≠0 by have ht:=G.dimPos; positivity); rw [←G.trace_color, ←G.trace_color,G.colorMat_ad, G.colorMat_ad]
  let A:=G.colorMat (unitColor G a); let B:=G.colorMat (unitColor G b); let C:=G.colorMat (unitColor G c)
  change - (Matrix.trace ((A*B-B*A)*C)).re= -(Matrix.trace ((B*C-C*B)*A)).re
  rw [sub_mul,sub_mul,Matrix.trace_sub,Matrix.trace_sub,mul_assoc A,Matrix.trace_mul_comm A,mul_assoc C B A,Matrix.trace_mul_comm C,mul_assoc B]
lemma flip' (a b c:G.ColorIndex): colorF a c b= -colorF a b c:= by rw [swing a c b,flip b c a,swing a b c]
@[simp] lemma aa (a b : G.ColorIndex):colorF a a b=0:=by have h:=flip a a b; linarith
@[simp] lemma bb (a b : G.ColorIndex):colorF a b a=0:=by rw [swing a b a,swing b a a,aa]
@[simp] lemma cc (a b : G.ColorIndex):colorF a b b=0:=by rw [swing,aa]

-- orbit-code b under relabel. tested Fan after *projection*.
def tag (v x y : Eye × G.ColorIndex): ℝ := eps3 v.1 x.1 y.1 * colorF v.2 x.2 y.2
lemma tag12 (v x y:Eye × G.ColorIndex) : tag v x y= tag x v y:= by unfold tag; rw [eps_swap12 x.1 v.1 y.1, flip x.2 v.2 y.2]; simp only [Int.cast_neg,neg_mul_neg]
lemma tag23 (v x y:Eye × G.ColorIndex) : tag v x y= tag v y x:= by unfold tag; rw [eps_swap23 v.1 y.1 x.1, flip' v.2 y.2 x.2]; simp only [Int.cast_neg,neg_mul_neg]
lemma tag_any (p : Eye→Eye × G.ColorIndex) (σ : Eye≃Eye) : tag (p 0) (p 1) (p 2)=tag (p (σ 0)) (p (σ 1)) (p (σ 2)):= by
  let a:=σ 0; let b:=σ 1; let c:=σ 2
  have ha:a≠b:=σ.injective.ne (by decide)
  have hb:b≠c:=σ.injective.ne (by decide)
  have hc:a≠c:=σ.injective.ne (by decide)
  change _=tag (p a) (p b) (p c)
  have he (a:Eye): a=0∨a=1∨a=2 := by fin_cases a <;> decide
  rcases he a with H|H|H <;> rcases he b with I|I|I <;> rcases he c with J|J|J <;>
    first | exact False.elim (ha (H.trans I.symm)) | exact False.elim (hb (I.trans J.symm)) | exact False.elim (hc (H.trans J.symm)) | (rw [H,I,J] <;> (first | exact tag12 .. | exact tag23 .. | exact ((tag12 ..).trans (tag23 ..)) | exact ((tag23 ..).trans (tag12 ..)) | exact ((tag12 ..).trans ((tag23 ..).trans (tag12 ..)))))
-- swap A factors of a fan nonlinear completion.
lemma both (i:Gem)(a b : Axis)(x y z : G.ColorIndex) : coin i a b*colorF x y z=coin i b a*colorF x z y:=by unfold coin; rw [fan_flip _ _ b a, flip' x z y]; ring
end Chroma
section mark
variable {n : ℕ}
/-- momentum-index Landau numerator stripped only of h and radial, pure gauge; for p≠0. -/
def divvy (p : Hot.Space n) (a b:Fin n):= (if a=b then 1 else 0 : ℝ)-p a * p b / ‖p‖^2
lemma curled (p : Hot.Space n) (_h : p≠0) (a b d:Fin n) : p a * divvy p b d-p b * divvy p a d=(p a * (if b=d then 1 else 0) - p b * (if a=d then 1 else 0)) := by unfold divvy; ring
-- elementary tangent identity for projecting each pinning curl p_a A_b-p_b A_a, equally for CT propagation when the leg is at opposite momentum.
lemma route_pin {X : Type} [AddCommGroup X] [Module ℝ X] (F : Axis→X)(K:Gem)(c : Axis) :
    (2:ℝ)⁻¹ • (∑ a:Axis,∑ b:Axis,coin K a b • ((if b=c then F a else 0)-(if a=c then F b else 0))) =∑ a:Axis,coin K a c • F a := by
  simp only [smul_sub,Finset.sum_sub_distrib]
  rw [show (∑ a:Axis,∑ b:Axis,coin K a b • if b=c then F a else 0) = ∑ a:Axis,coin K a c • F a by simp]
  rw [show (∑ a:Axis,∑ b:Axis,coin K a b • if a=c then F b else 0) =∑ b,coin K c b • F b by rw [Finset.sum_comm]; simp]
  have he b : coin K c b= -coin K b c := fan_flip ..
  simp_rw [he,neg_smul,Finset.sum_neg_distrib]; rw [← smul_sub,sub_neg_eq_add,← two_smul ℝ]; exact inv_smul_smul₀ (by norm_num) _
end mark
end YM.SchemeRG11.MSDetector
