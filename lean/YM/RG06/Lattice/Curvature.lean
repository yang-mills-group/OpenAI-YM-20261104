import YM.RG06.Lattice.Words
 import YM.Pert.First.Completion
import YM.Push.STRESS_FLUX.Force -- exact normalized trace/color projection

/-!
# Transported Wilson curvature stencils

Per-slot rule on any RG.Slot: take the ordered loop series (walk, square and walk
back), then the skew part in physical color coordinates. Compute the latter by the trace in
the faithful representation with its prescribed normalization. Equivalently use the
fundamental and reversed loop, not treating a complex coefficient as a group point.
Use only as germ, not a path or address re-expression of a represented density.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG06.WilsonRules
open Lattice Wilson MvPolynomial NormedSpace RG Pert.First
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius InnerProductSpace ComplexConjugate

variable (G : Gauge) {X : Type*} [AddCommGroup X] [One X]

def loopOf (s : Slot) : Walk := s.walk ++ square s.plaq.val.1 s.plaq.val.2 ++ reverse s.walk

theorem loop_length (s : Slot) : (loopOf s).length = s.length + s.walk.length := by
  simp [loopOf, square, reverse, Slot.length]; omega

theorem loop_stop (s : Slot) (x : Four X) : stop x (loopOf s) = x := by
  simp only [loopOf,stop_append,square_stop, reverse_stop]

lemma loop_eval (s : Slot) (U : CoverConfig G) :
    G.curvature (travel U 0 (loopOf s)) = s.eval U := by
  simp only [loopOf,travel_append,stop_append,square_stop,travel_reverse,Slot.eval,Slot.offset,
    faceValue,G.curvature_conjugate]

/-- The complex version of reading the real skew projection on a physical group element;
only this scalar extraction is complex-linear, not `projectColor` on arbitrary matrices. -/
def traceSlot (c : G.ColorIndex) (M N : G.Mat) : ℂ :=
  - ((2 * G.repDim:ℂ)⁻¹ * ((G.colorMat (baseColor G c)*M).trace - (G.colorMat (baseColor G c)*N).trace))

theorem traceSlot_group (g : G.El) (c : G.ColorIndex) :
    traceSlot G c (G.mat g) (G.mat g⁻¹) = (↑(G.curvature g c):ℂ) := by
  let X:= G.colorMat (baseColor G c)
  have h := StressFlux.price_direction g (baseColor G c)
  rw [base_inner] at h
  have hi : (starRingEnd ℂ) (X * G.mat g).trace = - (X * G.mat g⁻¹).trace := by
    change star (_) = _
    rw [← Matrix.trace_conjTranspose,← Matrix.star_eq_conjTranspose, star_mul,
      show star X = -X from G.colorMat_skew _, ← G.mat_inv, Matrix.mul_neg, Matrix.trace_neg, Matrix.trace_mul_comm]
  change - (_ * ((X*_).trace-(X*_).trace)) = _
  rw [← h]
  push_cast
  rw [show (G.colorMat _ * _).trace = (X*G.mat g).trace from rfl, Complex.re_eq_add_conj,hi]
  have hz : (G.repDim : ℂ) ≠ 0 := by exact_mod_cast G.dimPos.ne'
  field_simp; ring

/-- Complex trace formula on the coefficient ring, using positive & reversed walk. -/
def colorTrace {X : Type*} (c : G.ColorIndex) (M : PMat G X) : Feynman G X :=
  (((MvPolynomial.C (R:=ℂ)).mapMatrix (G.colorMat (baseColor G c))) * M).trace

def slotCoeff (s : Slot) (c : G.ColorIndex) (k : ℕ) : Feynman G ℤ :=
  - MvPolynomial.C ((2 * G.repDim : ℂ)⁻¹) *
    (colorTrace G c (PowerSeries.coeff k (ordered G (0:Cover) (loopOf s))) -
     colorTrace G c (PowerSeries.coeff k (ordered G (0:Cover) (reverse (loopOf s)))))

def slotSeries (s : Slot) (c : G.ColorIndex) : PowerSeries (Feynman G ℤ) := PowerSeries.mk (slotCoeff G s c)

omit [AddCommGroup X] [One X] in
lemma colorTrace_read {X : Type*} (c : G.ColorIndex) (v : LogField G X) (M : PMat G X) :
    read v (colorTrace G c M) = (G.colorMat (baseColor G c) * readMat v M).trace := by
  simp [colorTrace,Matrix.trace,Matrix.mul_apply, readMat_apply, RingHom.mapMatrix_apply]

lemma word_jet (v : LogField G X) (k : ℕ) (x : Four X) (s : Walk) :
    readMat v (PowerSeries.coeff k (ordered G x s)) = Germ.jet (fun t=> G.mat (travel (rise v t) x s)) k := by
  rw [← PowerSeries.coeff_map,word_eval,Germ.series_coeff]

/-- Complex-linear trace evaluated on real charts as a real-linear functional on Mat so
we can take real jets. -/
def traced (c : G.ColorIndex) : G.Mat →L[ℝ] ℂ :=
 (Matrix.traceLinearMap (Fin G.repDim) ℝ ℂ).toContinuousLinearMap ∘L
   ((ContinuousLinearMap.mul ℝ G.Mat) (G.colorMat (baseColor G c)))

@[simp] lemma traced_apply (c : G.ColorIndex) (M : G.Mat) :
    traced G c M = (G.colorMat (baseColor G c) * M).trace := rfl

lemma jet_trace (c : G.ColorIndex) (F : ℝ → G.Mat) (k : ℕ) (hf : ContDiff ℝ ω F) :
    Germ.jet (fun t=> traced G c (F t)) k = traced G c (Germ.jet F k) := by
  simp only [Germ.jet,map_smul]; exact congrArg (fun z:ℂ=> ((k.factorial:ℝ)⁻¹) • z) (iterated_clm (traced G c) 0 (hf.of_le (show ∞ ≤ ω from le_top)))

lemma slot_smooth (v : LogField G ℤ) (s : Slot) (c : G.ColorIndex) :
    ContDiff ℝ ω (fun t=> (↑(s.eval (rise v t) c):ℂ)) := by
  let r := loopOf s
  have he (t : ℝ) : travel (rise v t) (0:Cover) (reverse r) =
      (travel (rise v t) (0:Cover) r)⁻¹ := by
    have h:= travel_reverse (loopOf s) (rise v t) (0:Cover); rwa [loop_stop] at h
  let Q (a:Walk) (t:ℝ):=traced G c (G.mat (travel (rise v t) (0:Cover) a))
  have hx (t:ℝ) : (↑(s.eval (rise v t) c):ℂ) = - ((2*G.repDim:ℂ)⁻¹ * (Q r t - Q (reverse r) t)) := by
    rw [← loop_eval, ← traceSlot_group]; simp only [Q,he,traceSlot,traced_apply,r]
  simp_rw [hx]
  have hc (a:Walk) : ContDiff ℝ ω (Q a):= (traced G c).contDiff.comp (word_smooth v _ a)
  exact (contDiff_const.mul ((hc r).sub (hc (reverse r)))).neg

lemma slot_jet (v : LogField G ℤ) (s : Slot) (c : G.ColorIndex) (k : ℕ) :
    read v (slotCoeff G s c k) = Germ.jet (fun t=> (↑(s.eval (rise v t) c):ℂ)) k := by
  let r := loopOf s
  have he (t : ℝ) : travel (rise v t) (0:Cover) (reverse r) =
      (travel (rise v t) (0:Cover) r)⁻¹ := by
    have h:= travel_reverse (loopOf s) (rise v t) (0:Cover); rwa [loop_stop] at h
  let Q (a:Walk) (t:ℝ):= traced G c (G.mat (travel (rise v t) (0:Cover) a))
  have hx (t:ℝ) : (↑(s.eval (rise v t) c):ℂ) = (- (2*G.repDim:ℂ)⁻¹) * (Q r t - Q (reverse r) t) := by
    rw [← loop_eval, ← traceSlot_group]; simp only [Q,he,traceSlot,traced_apply,r,neg_mul]
  simp_rw [hx]
  have hc (a:Walk) : ContDiffAt ℝ k (Q a) 0 := ((traced G c).contDiff.comp (word_smooth v _ a)).contDiffAt.of_le le_top
  have hz (a:Walk) : Germ.jet (Q a) k = (G.colorMat (baseColor G c) * readMat v (PowerSeries.coeff k (ordered G (0:Cover) a))).trace := by rw [word_jet,←traced_apply,←jet_trace]; exact word_smooth v (0:Cover) a
  simp only [slotCoeff, _root_.map_mul, _root_.map_sub, map_neg, read_C, colorTrace_read]
  rw [Germ.jet, iteratedDeriv_const_mul_field,iteratedDeriv_fun_sub (hc r) (hc (reverse r)),← mul_smul_comm, smul_sub]
  exact congrArg ((- (2*G.repDim:ℂ)⁻¹) * ·) ((congrArg₂ (·-·) (hz r) (hz (reverse r))).symm)

end YM.RG06.WilsonRules
