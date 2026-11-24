import YM.Integration.WilsonPhysicalHistoryRetainedSpringJet
import YM.Integration.WilsonPhysicalHistoryRetainedSpringGram

/-! The direct Wilson plaquette is read by the normalized real matrix trace
on the original four visits. Its constant and first real Taylor terms cancel. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Function Filter Lattice RG Wilson Work.F02 WilsonMeasuredPathTaylor
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G : Gauge} {n : Side}

def normalizedTrace (G : Gauge) : G.Mat→L[ℝ]ℝ :=
  (G.repDim:ℝ)⁻¹ • Complex.reCLM.comp (Matrix.traceLinearMap (Fin G.repDim) ℝ ℂ).toContinuousLinearMap

def tracePrice (G : Gauge) : ℝ:=‖(1:G.Mat)‖/(G.repDim:ℝ)

theorem trace_bound (G : Gauge) (M : G.Mat) : |normalizedTrace G M|≤tracePrice G*‖M‖ := by
  have realTrace : inner ℝ M (1:G.Mat)=M.trace.re:=by
    change (M*star (1:G.Mat)).trace.re=M.trace.re
    simp
  have scalar : normalizedTrace G M=M.trace.re/G.repDim:=by
    simp [normalizedTrace,div_eq_inv_mul]
  rw [scalar,abs_div,abs_of_nonneg (show 0≤(G.repDim:ℝ) from Nat.cast_nonneg _),←realTrace,tracePrice]
  calc
    _ ≤ ‖M‖*‖(1:G.Mat)‖/(G.repDim:ℝ):=div_le_div_of_nonneg_right
      (abs_real_inner_le_norm M 1) (Nat.cast_nonneg _)
    _ = _:=by ring

theorem trace_price (U : Config G n) (x : Site n) (a : PlaqAxes) :
    G.price (faceValue U (x,a))=1-normalizedTrace G (G.mat (travel U x (square a.val.1 a.val.2))) := by
  simp [normalizedTrace,Gauge.price,faceValue,div_eq_inv_mul]

def faceRay (v : Directions G n) (x : Site n) (a : PlaqAxes) (q : ℕ) (t : ℝ) : ℝ:=
  1-normalizedTrace G (jet (curve v x (square a.val.1 a.val.2)) q t)

theorem face_ray_error (v : Directions G n) (x : Site n) (a : PlaqAxes) (q : ℕ) (t : ℝ) :
    |G.price (faceValue (field v t) (x,a))-faceRay v x a q t|≤
      tracePrice G*((fare v x (square a.val.1 a.val.2)^(q+1)*‖(1:G.Mat)‖)*|t|^(q+1)/(q+1).factorial) := by
  let w:=square a.val.1 a.val.2
  let f:=curve v x w
  let L:=normalizedTrace G
  rw [trace_price]
  change |(1-L (f t))-(1-L (jet f q t))|≤_
  rw [show (1-L (f t))-(1-L (jet f q t))=L (jet f q t-f t) by rw [map_sub]; ring]
  refine (trace_bound G _).trans ?_
  rw [norm_sub_rev]
  exact mul_le_mul_of_nonneg_left (matrix v x w q t) (by unfold tracePrice; positivity)

theorem face_ray_continuous (x : Site n) (a : PlaqAxes) (q : ℕ) (t : ℝ) :
    Continuous (fun v : Directions G n=>faceRay v x a q t) := by
  let w:=square a.val.1 a.val.2
  let M : Directions G n→ G.Mat:=fun v=>G.mat (travel (field v 1) x w)
  have localG : ContDiffAt ℝ ω M 0:=by
    have eq : M=fun v=>stringMat (physical (field v 1)) w x:=funext fun v=>(stringMat_physical ..).symm
    rw [eq]
    exact ((stringMat_contDiff w x).restrict_scalars ℝ).contDiffAt.comp _ (physical_contDiffAt (fun e=>by
      simp only [field,one_smul]
      exact G.exp_jet.contDiffAt.comp _ (by fun_prop)))
  have radial (v : Directions G n) : curve v x w=fun u : ℝ=>M (u • v):=by
    funext u
    have eq : field (u • v) 1=field v u:=by funext e; simp [field]
    exact congrArg (fun U=>G.mat (travel U x w)) eq.symm
  have printed (v : Directions G n) : jet (curve v x w) q t=
      ∑ j∈Finset.range (q+1),t^j • CubicMatch.term j (fun u : ℝ=>M (u • v)):=by
    rw [radial,jet]
    apply Finset.sum_congr rfl
    intro j _
    simp only [CubicMatch.term,smul_smul,mul_comm]
  change Continuous (fun v : Directions G n=>1-normalizedTrace G (jet (curve v x w) q t))
  simp_rw [printed]
  apply continuous_const.sub ((normalizedTrace G).continuous.comp ?_)
  apply continuous_finsetSum
  intro j _
  simp_rw [CubicMatch.term_ray (localG.of_le (show (j:WithTop ℕ∞)≤ω from le_top))]
  exact ((Tensor.coeff M j 0).cont.comp (continuous_pi fun _=>(continuous_id (X:=Directions G n)))).const_smul (t^j)

private theorem first_min {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (L : E→L[ℝ]ℝ)
    (f : ℝ→E) (hf : ContDiff ℝ ω f) (at0 : 1-L (f 0)=0) (pos : ∀ u,0≤1-L (f u)) (t : ℝ) :
    1-L (jet f 1 t)=0:=by
  have minimum : IsLocalMin (fun u : ℝ=>1-L (f u)) 0:=by
    apply Filter.Eventually.of_forall
    intro u
    change 1-L (f 0)≤1-L (f u)
    exact at0.le.trans (pos u)
  have h:=minimum.hasDerivAt_eq_zero ((hasDerivAt_const 0 (1:ℝ)).sub
    (L.hasFDerivAt.comp_hasDerivAt 0 ((hf.differentiable (by simp) 0).hasDerivAt)))
  have z : L (deriv f 0)=0:=by simpa only [zero_sub,neg_eq_zero] using h
  simpa [jet,Finset.sum_range_succ,z] using at0

theorem face_ray_first (v : Directions G n) (x : Site n) (a : PlaqAxes) (t : ℝ) :
    faceRay v x a 1 t=0 := by
  apply first_min _ _ (smooth ..)
  · have flat : field v 0=1:=by funext e; simp [field]
    calc
      _ = G.price (faceValue (field v 0) (x,a)) := (trace_price _ x a).symm
      _ = 0:=by rw [flat]; simp [faceValue,square]
  · intro u
    exact (G.price_range _).1.trans_eq (trace_price (field v u) x a)

end YM.Integration.OriginalMarkedRunAction
