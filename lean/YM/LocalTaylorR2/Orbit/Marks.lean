import YM.LocalTaylorR2.Orbit.Applied
/-!
 # After inverting the mark radii and plugging any finite power gap.

 This proof also works for countably-summed Towing.I. At the indicated
 mark scale only -- future distortion estimates are not coming from this local result.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Orbit
open Function Filter Finset MeasureTheory Matrix Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell Channel SliceRows Coat Control Window Pulse Footprint Raw Matter Mask
open PhysicalNext.Repeat Lotus Packets Greenbelt Daisy Port RG01.Survive Candle
open MeasureTheory Gas Ursell
open _root_.YM.Marker Merge Switch Palette MergeProof Accent GridRenewal.Rain GridApprox.Nil
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side}
variable {V ι Y:Type} [DecidableEq V] [Fintype V] {p:BudgetPoint} {B:_root_.YM.Marker.Census V}
    {X:Poly B}{o:V→Site c}{E:ι→Y→Poly B}{A:ι→Support c} {v:V→ℝ} {t a x e:ℝ}
open Tail
variable (K n: ℕ)
lemma duty (x:ℝ)(hx:1≤x)(C:ℕ) (hc:Fintype.card V≤ C) (i:B.Mode) : Poly.toll (1:V→ℝ) i≤ x^(K*C)*Poly.toll (fun _=> (x^K)⁻¹) i:=by
   unfold Poly.toll; rw [prod_const]
   have h : i.1.card≤ C:= Finset.card_le_card (subset_univ i.1)|>.trans_eq (Finset.card_univ)|>.trans hc
   have hh:1 ≤ x^K:= one_le_pow₀ hx; have hb:(x^K)^i.val.card ≤ x^(K*C):= by rw [pow_mul]; exact pow_le_pow_right₀ hh h
   rw [Finset.prod_eq_one (f:=(1:V→ℝ)) (fun _ _=>rfl), inv_pow]; exact le_trans (show 1 = (x^K)^i.val.card*((x^K)^i.val.card)⁻¹ from (mul_inv_cancel₀ (by positivity)).symm).le (mul_le_mul_of_nonneg_right hb (by positivity))


-- use explicit forall regardless of orientation powers/supported mark caps
omit [Fintype V] in
lemma unprice {w:ℝ}(h:∀ i:B.Mode, Poly.toll (1:V→ℝ) i ≤ w* Poly.toll v i) (a: GridApprox.Nil.Sheet B)(ha:0≤a) : GridApprox.Nil.wordsPrice (1:V→ℝ) a ≤ w* GridApprox.Nil.wordsPrice v a :=by
   unfold wordsPrice; rw [Finset.mul_sum]; exact Finset.sum_le_sum fun i _=> (mul_le_mul_of_nonneg_right (h i) (ha i)).trans_eq (mul_assoc ..)

omit [Fintype V] in -- avoid if needed
lemma billUpT {w:ℝ} (hw:0≤w) (h:∀ i:B.Mode, Poly.toll (1:V→ℝ) i ≤ w* Poly.toll v i) (ht: Towed v A E n a e): Towed (1:V→ℝ) A E n a (w*e):=by
   obtain ⟨f,hf,hA,hM⟩:=ht
   refine ⟨fun x=>w*f x,hf.mul_left w,AnalyticBridge.VerifiedReset.Quotes.hit_scale hw hA,fun i=>?_⟩
   obtain ⟨c,hc,h,hX⟩:=hM i; exact ⟨_,hc,h,(unprice (by assumption) _ hc).trans (mul_le_mul_of_nonneg_left hX hw)⟩

variable {S : StepData c f} {P:Teller G} {T: Tube G S} {R : Rep G f}
    {W r μ s C : ℝ} {Q: YM.ConnectedActivityE6.Target G P} {q: ConnectedActivityE6.Target.Order G W}
variable {H:Cash W s μ L Q q C T R} {Z:H.fragrances→ Config G c→Poly B}
omit [Fintype V] in
lemma billUpS {w:ℝ} (hw:0≤w) (h:∀ i:B.Mode, Poly.toll (1:V→ℝ) i ≤ w* Poly.toll v i) (ht: shop H B v o p Z e): shop H B (1:V→ℝ) o p Z (w*e):=by
   obtain ⟨f,hf,hA,hM⟩:=ht; refine ⟨fun x=> w*f x,hf.mul_left w,AnalyticBridge.VerifiedReset.Quotes.hit_scale hw hA,fun i=> ?_⟩
   obtain ⟨u,hu,he,h,hP⟩:=hM i; exact ⟨_,hu,(unprice (by assumption) _ hu).trans (mul_le_mul_of_nonneg_left he hw),h,hP⟩

abbrev escalate (K qC pD:ℕ):= pD+2*((K+2)*qC)
lemma powers (qC pD:ℕ)(h:1≤x)(hd:0 ≤ e): let m:=(K+2)*qC; let l:= escalate K qC pD; x^m*x^requested (l+1) e=x^requested (pD+1) e ∧ x^m*x^(-((l:ℝ)+1)) ≤ x^requested (pD+1) e:= by
   intro m l; have ht : requested (pD+1) e= requested (l+1) e+m:=by unfold requested l escalate m; push_cast; ring
   have he: -((l:ℝ)+1)≤ requested (l+1) e:=by unfold requested; push_cast; linarith [Nat.cast_nonneg (α:=ℝ) l];
   rw [ht,Real.rpow_add (zero_lt_one.trans_le h) (requested (l+1) e) m, Real.rpow_natCast,mul_comm (x ^ requested (l+1) e)]; exact ⟨rfl,mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h he) (pow_nonneg (zero_le_one.trans h) _)⟩
end YM.LocalTaylorR2.Orbit
