import YM.AllOrder.Catch.Tape
import YM.AllOrder.Laplace.Tilt
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Catch
open Function Filter Finset Topology Metric MeasureTheory
open PhysicalNext Repeat Lantern ConnectedActivityE6 Blaze Brush PositionX.Jet Laplace Laplace.SigmaP Tensor
open PertExtension.Series Radial
open scoped Topology Classical BigOperators ContDiff
variable {X Y ι:Type*}{V U W:X → Type}
variable [∀ i,NormedAddCommGroup (V i)][∀ i,NormedSpace ℝ (V i)] [∀ i,NormedAddCommGroup (U i)][∀ i,NormedSpace ℝ (U i)]
variable {T:Clock X} {p a b c W₀:X→ℝ} {k j n:ℕ}{s v d B C:ℝ}{f:X→Word ℝ}{g:∀ i:X,V i→ℝ}
local notation "H"=> T.Meter
namespace Cover
variable {G: Type} [NormedAddCommGroup G][NormedSpace ℝ G]{F:G→ℝ}{v:G}{K:X→G}{b: X→ℝ}
variable {L:∀ i,V i→L[ℝ] U i}{x:∀ i,V i}
lemma loc (h: ContDiffAt ℝ ω F v)(hk:Tendsto K T.rail (𝓝 v)) : Cover T j 0 (fun _=>1) (fun _=> F) K := by
 obtain ⟨C,hC,H'⟩:= Brush.neighborhood v (k:=j) (h.of_le le_top); exact Cover.has (Clock.Meter.const T C) (hk.eventually H')
lemma linear (ht:H (fun i=> ‖L i (x i)‖) s) (hD:H (fun i=> ‖L i‖) s): Cover T j s (fun _=>1) (fun i=> ⇑(L i)) x:= by
 intro e he; filter_upwards [ht e he,hD e he] with i hi hx; rw [abs_of_nonneg (norm_nonneg _)] at hi hx; exact linearB (L i) hi (hx.trans_eq (mul_one _).symm) zero_le_one
lemma comp_lin (ht:H (fun i=> ‖x i‖) C)(he:0≤C)(h:H (fun i=> ‖L i‖) s): Cover T j (s+C) (fun _=>1) (fun i=> ⇑(L i)) x:= linear ((h.mul ht).smaller (Eventually.of_forall fun i=> by rw [abs_of_nonneg (norm_nonneg _)]; exact ((L i).le_opNorm _).trans (le_abs_self _))) (h.weak (by linarith))
lemma exponent (ht:0≤C) (hx: H (fun i=> ‖x i‖) C) : Cover T j C (fun _=>1) (fun (i:X)=> (id: V i→ V i)) x:= linear (L:=fun i=>ContinuousLinearMap.id _ _) hx (((Clock.Meter.const T 1).weak ht).smaller (Eventually.of_forall fun i=> by rw [abs_of_nonneg (norm_nonneg _)]; exact ContinuousLinearMap.norm_id_le.trans (le_abs_self _)))
lemma powerC (h:Cover T k s (fun _=>1) g x)(j:ℕ): Cover (V:=V) (U:=fun _=>ℝ) T k (s*j) (fun _=>1) (fun i=>g i^j) x:=by induction j with
 | zero=> simp only [pow_zero, Nat.cast_zero,mul_zero]; exact Cover.fixed (fun _=>(1:ℝ)) (Eventually.of_forall fun i=> zero_le_one) (Clock.Meter.const T ‖(1:ℝ)‖)
 | succ j ih=> simpa only [pow_succ,Nat.cast_add_one,mul_add,mul_one] using ih.mul h -- names
lemma from_book (s:∀ i,Set (V i)) (F:∀i, V i→U i) (he:Cover (V:=fun i=>V i.1) (U:=fun i=>U i.1) (T.book s) k C (fun _=>1) (fun i=>F i.1) (fun i=> i.2.1))(ht:∀ᶠ i in T.rail,x i∈ s i): Cover T k C (fun _=>1) F x:= by
 intro e hv; have hh:= T.booked s (fun i x=>Brush k (T.cost i^e) 1 (F i) x)|>.1 (he e hv); exact (ht.and hh).mono fun _ h=>h.2 _ h.1
end Cover
local notation "T₁"=> T.book (fun i:X => Metric.closedBall (0:ℝ) (b i))
lemma bbook {γ:Y→X}{Q:Clock Y}(hc:T.Fare (U:=Q) γ)(h:H b v)(he:∀ᶠ i in Q.rail, |p (γ i)|≤ b (γ i)):Q.Meter (p∘γ) v:= ((h.pays γ hc)).smaller (he.mono fun i hi=> hi.trans (le_abs_self _))
lemma cost_r (h:H b v): (T₁).Meter (fun i=>i.2.1) v:= ((h.pays Sigma.fst (T.liftF _))).smaller (Eventually.of_forall fun i=> (mem_closedBall_zero_iff.mp i.2.2).trans (le_abs_self _))
namespace TaylorCap
lemma paintT {f':X→ℝ→ℝ}(h:H b (-(1/2)))(he:∀ᶠ i in T.rail,0<b i)(ht: k<j)(hc:Cover (V:=fun _=>ℝ) (U:=fun _=>ℝ) (T₁) j 0 (fun _=>1) (fun i=> f' i.1) (fun i=> i.2.1)):
    TaylorCap T k b (fun i=> f' i (b i)) (fun i=> someJ (f' i)):= by
 refine ⟨fun t hx=> cover_j (tips he hc) (by omega),fun t hx=> ?_⟩; exact (prices_tape h (by norm_num) he hc (by omega : t<j)).weak (by unfold graded; simp only [zero_add]; linarith)
lemma scrub {f:ℝ→ℝ}(h:ContDiffAt ℝ ω f 0)(hh:f 0=0)(n:ℕ)(c:ℝ): delay (someJ f) (n+1) c=c*delay (someJ (Laplace.SigmaP.shift f)) n c:= by
 unfold delay; rw [shift_down hh h, sum_range_succ',someJ_zero,hh,smul_zero,add_zero,Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi; simp [add_comm,pow_succ',mul_assoc]; -- test
lemma shiftT {g:X→ ℝ→ℝ} (hp:H (fun i=> (b i)⁻¹) (1/2))(he:∀ᶠ i in T.rail,0< b i)(hG:∀ᶠ i in T.rail,g i 0=0 ∧ ContDiffAt ℝ ω (g i) 0)
    (h:TaylorCap T (k+1) b (fun i=>g i (b i)) (fun i=> someJ (g i))): TaylorCap T k b (fun i=> Laplace.SigmaP.shift (g i) (b i)) (fun i=> someJ (Laplace.SigmaP.shift (g i))):= by
 constructor
 · intro j hj; exact (h.steps (1+j) (by omega)).eq_mem (hG.mono fun i hi=> by dsimp only; rw [shift_down hi.1 hi.2]) -- DSIMP?
 intro j hj; refine ((hp.mul (h.stamps (j+1) (by omega))).weak (by unfold graded; push_cast; linarith)).eq_mem ?_; filter_upwards [he,hG] with i hi hg; rw [scrub hg.2 hg.1]; nth_rw 1 [shift_start hg.1 (b i)] ; change (b i)⁻¹*(b i * _ -_)=_; field_simp
lemma alteration (h:TaylorCap T k b a f)(hh:H (c-a) (graded (k+1))) : TaylorCap T k b c f:= by
 refine ⟨h.steps,fun i hi=> Clock.Meter.eq_mem (?_) (Eventually.of_forall (fun j=> (show c j -a j+(a j-delay (f j) i (b j))= c j-delay (f j) i (b j) from (by ring))))⟩; refine (hh.weak ?_).add (h.stamps i hi); unfold graded; push_cast; nlinarith [ Nat.cast_le (α:=ℝ)|>.mpr hi]
end TaylorCap
end YM.AllOrder.Catch
