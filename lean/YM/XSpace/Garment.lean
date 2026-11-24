import YM.XSpace.Leather

/-!
# First-order vertices and local gauge transformations

Ordinary monomial coefficients here. For Σ₁ and Ward rule: on invariant fields;
for Q0 Σ₂ and Q1 at density insertion: no Hessian quotient.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Chart2
open CubicMatch Function Lattice RG Next.Rank.Normal
open scoped Topology BigOperators InnerProductSpace
variable {G : Gauge} {R : Type*} [AddCommGroup R] [One R]
abbrev St (R : Type*) (G : Gauge) := Kit (Edges2 R) G

lemma touch_polynomial (G : Gauge) (s : Four R) (d:Step): Record G (fun A=> touch s d A):=by
  rcases d with ⟨i,h|h⟩
  · simp only [show ∀ A:LogLinks R G, touch s ⟨i,false⟩ A=_ from fun A=>touch_pos s i A]; exact Record.entry _
  simp only [show ∀ A:LogLinks R G, touch s ⟨i,true⟩ A=_ from fun A=>(touch_neg s i A).trans (neg_one_smul ℝ _).symm]; exact (Record.entry _).smul (-1)
lemma trip_polynomial (G : Gauge) (s : Four R) (w:Walk): Record G (fun A=> tallyPath s w A):= by
  induction w generalizing s with
  | nil => exact Record.const _
  | cons a w ih => exact (touch_polynomial G s a).add (ih _)
lemma second_polynomial (G : Gauge) (s : Four R) (w:Walk): Record G (fun A=> (travel (native A) s w).c):= by
  induction w generalizing s with
  | nil => exact Record.const _
  | cons a w ih => simp only [travel,Drift.c_mul,native,touch_c,map_zero,zero_add,touch_a,trip_a]; exact (ih (s+a.vec)).add ((Record.pairing G.ad (touch_polynomial G s a) (trip_polynomial G (s+a.vec) w)).smul _)
lemma acc_polynomial (G : Gauge) (p : Face R): Record G (fun A=> acc p A):= second_polynomial G p.1 (square p.2.val.1 p.2.val.2)
lemma slope_polynomial (G : Gauge) (p : Face R): Record G (fun A=> linearFace p A):= trip_polynomial G p.1 (square p.2.val.1 p.2.val.2)
lemma v3_polynomial (G : Gauge) (p : Face R): Reads G (Z:=Edges2 R) (diagnostic p):= Record.pairing (innerₗ G.Color) (slope_polynomial G p) (acc_polynomial G p) LinearMap.id

def V3 (G : Gauge) (p : Face R): St R G:= (v3_polynomial G p).pol
lemma price_at (p : Face R) (A : LogLinks R G): pit A (V3 G p)=↑(diagnostic p A):= Reads.value ..
lemma price_ward (p : Face R) (A : LogLinks R G) (v : Four R→ G.Color) : pit A (D (grad v) (V3 G p)) = -↑(inner ℝ (linearFace p A) (linearFace p (rLink v A))):=by
  have he:= directional A (grad v) (V3 G p); simp_rw [price_at,gauge_cubic] at he
  refine he.unique (Complex.ofReal_neg _ ▸ Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 ?_)
  simp only [map_add,map_smul, inner_add_right,real_inner_smul_right]
  convert! (hasDerivAt_const _ _).sub (((hasDerivAt_id' _).mul_const (inner ℝ (linearFace p A) (linearFace p (rLink v A)))).add (((hasDerivAt_id' _).pow 2).mul_const (inner ℝ (linearFace p A) (linearFace p (extra v))))) using 1; norm_num; rfl

abbrev slotPoint (x:Four R) (s:Slot) : Face R:=(stop x s.walk,s.plaq)

def roundTrip {K :Type*} [Group K] (s:Slot) (x:Four R) (A:Links R K):= travel A x s.walk * faceValue A (slotPoint x s) * (travel A x s.walk)⁻¹
@[simp] lemma round_gauge {K :Type*} [Group K] (s:Slot) (x:Four R) (v:Four R → K) (A:Links R K): roundTrip s x (Lattice.gauge v A)=v x*roundTrip s x A*(v x)⁻¹:=by simp [roundTrip,slotPoint,travel_gauge,mul_assoc]
lemma carries_round (s:Slot) (u : ℝ → Links R G.El) (A : Links R (Drift G)) (h : ∀ e, Fits (fun t=> u t e) (A e)) (x : Four R) : Fits (fun t=> roundTrip s x (u t)) (roundTrip s x A):=((carries u A h s.walk x).product (carries_face u A h _)).product (carries u A h s.walk x).inverse

abbrev take1 (s:Slot) (x:Four R):=linearFace (G:=G) (slotPoint x s)
def take2 (s:Slot) (x:Four R) (A:LogLinks R G):= (roundTrip s x (native A)).c
lemma round_a (s:Slot) (x:Four R) (A Y:LogLinks R G): (roundTrip s x (duo A Y)).a=take1 s x A:=by rw [roundTrip,Drift.conjugate]; exact face_a ..
lemma round_c (s:Slot) (x:Four R) (A Y:LogLinks R G): (roundTrip s x (duo A Y)).c=take2 s x A+take1 s x Y:=by
  simp only [take2,roundTrip,Drift.conjugate,native,face_c,trip_a,face_a,map_zero,take1]; abel
lemma second_slot (G : Gauge) (s : Slot) (x:Four R) : Record G (fun A=>take2 s x A):= by
  simp only [take2,roundTrip,Drift.conjugate,native,face_c,map_zero, add_zero,face_a,trip_a]; exact (acc_polynomial G (slotPoint x s)).add (Record.pairing G.ad (trip_polynomial G x s.walk) (slope_polynomial G (slotPoint x s)))
lemma second_gauge (v:Four R→G.Color) (A:LogLinks R G) (t:ℝ) (s:Slot) (x: Four R):
    take2 s x (A+t • grad v) = take2 s x A-(take1 s x) (t • rLink v A+t^2 • extra v)+G.ad (-(t • v x)) (take1 s x A):=by
  apply add_right_cancel (b:= (take1 s x) (t • rLink v A+t^2 • extra v))
  rw [← round_c,← gauge_paths]; simp only [round_gauge,native,Drift.conjugate,round_c,map_zero,add_zero,round_a]; abel

section
variable {n : Side}
lemma slot_wrap (x : Site n) (s:Slot): slotPoint x s=Work.F03.slotFace s x:=by
  have h (x:Cover) (a: Site n) (w:Walk): wrap n (stop x w)+a=stop (wrap n x+a) w:=by
    induction w generalizing x with
    | nil => rfl
    | cons d w ih => simp only [stop,ih,map_add,wrap_vec,add_right_comm (wrap n x) d.vec]
  refine Prod.ext ?_ rfl; simpa [slotPoint,Work.F03.slotFace,Slot.offset] using (h 0 x s.walk).symm
lemma slots (s:Slot) (x: Site n) (A:Links (Per n) G.El): s.atSite A x= G.curvature (roundTrip s x A):=by rw [roundTrip,slot_wrap,G.curvature_conjugate]; exact Work.F03.atSite_path ..
lemma round_wrap {K:Type*} [Group K] (s:Slot) (x : Cover) (a:Site n) (A:Links (Per n) K): roundTrip s 0 (expandAt (wrap n x+a) A)=roundTrip s (wrap n x+a) A:=by unfold roundTrip; rw [slot_wrap (wrap n x+a)]; simp [faceValue,travel_at, Work.F03.slotFace,Slot.offset]
end
end YM.XSpace.Chart2
