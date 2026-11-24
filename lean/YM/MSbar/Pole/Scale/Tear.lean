import YM.MSbar.Pole.Scale.Regular

/-! # Consistently divide out a dimensional zero. No four-dimensional projection before division. -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole
open Function Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators Classical Interval
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {f g : ℂ→E→ℂ} {R : ℝ}
/-- Keep germs on balls. -/
def zone (R : ℝ) := Metric.ball (0:ℂ) R
@[simp] lemma zone_mem (x : ℂ) (R) : x ∈ zone R ↔ ‖x‖ < R := by rw [zone,Metric.mem_ball, dist_zero_right]

private def breeze (r : ℝ) : (ℂ×E)→L[ℝ]ℂ×E :=
  ((r:ℂ) • ContinuousLinearMap.fst ℝ ℂ E).prod (ContinuousLinearMap.snd ..)
omit [FiniteDimensional ℝ E] in
@[simp] private lemma glides (p : ℂ×E) (r : ℝ) : breeze r p = ((r:ℂ)*p.1,p.2) := rfl
local notation "w" => volume.restrict (Ioc (0:ℝ) 1)
variable {p q : Price E} (hc : Continuous p.val)
private def Dot (f : ℂ→E→ℂ) := fieldD (1,(0:E)) (fun x : ℂ × E=> f x.1 x.2)
/-- Divided difference, respects real probes also at exact zero. -/
def tear (f : ℂ→E→ℂ) (z : ℂ) (x : E) := ∫ t, Dot f (breeze t (z,x)) ∂w

namespace Wall
variable (h : Wall (zone R) p q f) (hR : 0<R)
omit [FiniteDimensional ℝ E] in
private lemma passage {x : E} {z : ℂ} (hz : z∈zone R) (r : ℝ) (hr : r∈Icc (0:ℝ) 1) :
    breeze r (z,x) ∈ strip E (zone R) := by
  have hu : ‖z‖<R:= (zone_mem ..).mp hz
  refine mem_prod.mpr ⟨?_,mem_univ _⟩; rw [zone_mem]; change ‖(r:ℂ)*z‖<R
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hr.1]
  exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) hr.2) hu
include hc h
private lemma barrel : Barrel w (strip E (zone R)) (stretch p) (stretch q) (fun r x => Dot f (breeze r x)) := by
  have o : IsOpen (strip E (zone R)):=Metric.isOpen_ball.prod isOpen_univ
  have hs : Packet (strip E (zone R)) (stretch p) (stretch q) (Dot f) := h.stream.fderiv.apply (X:=ContinuousLinearMap.apply ℝ ℂ _)
  have ht := pullBarrel breeze (T:=fun _ : ℝ => 0) (μ:=w) (p:=stretch p) (q:=stretch q) hs o (hc.comp continuous_snd).continuousOn
    (C:=1) zero_le_one ?_ ?_ ?_
  · simpa only [zero_add] using ht
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro v
    rw [one_mul]; change max ‖(r:ℂ)*v.1‖ ‖v.2‖ ≤ ‖v‖; refine max_le ?_ (norm_snd_le _)
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hr.1.le]; exact le_trans (mul_le_of_le_one_left (norm_nonneg _) hr.2) (norm_fst_le _)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr x hx
    simp only [zero_add,one_mul]; obtain ⟨z,y⟩:= x
    exact ⟨passage hx.1 r ⟨hr.1.le,hr.2⟩,le_rfl,le_rfl⟩
  rintro ⟨z,x⟩ hx; simp only [zero_add,glides]
  refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc; intro i hi
  exact ((hs.smooth _ (passage (x:=x) hx.1 i ⟨hi.1.le,hi.2⟩)).continuousAt.comp
    (f:=fun r:ℝ=>((r:ℂ)*z,x)) (x:=i) (by fun_prop)).continuousWithinAt

lemma torn : Wall (zone R) p q (tear f) := by
  have he := barrel hc h
  refine ⟨?_,fun z hz x=>?_⟩
  · exact he.integrates
  let k : ℂ × E:=(z,x); have hh : k∈strip E (zone R):=⟨hz,mem_univ x⟩
  apply (coordinates (U:=fun y=> tear f y.1 y.2) ((he.exchange hh).differentiableAt)).mp
  change CR (1,0) (Complex.I,0) (fun z=>∫ t,Dot f (breeze t z) ∂w) k
  apply integral_cr he hh; filter_upwards [ae_restrict_mem measurableSet_Ioc] with i hi
  have hv := passage (x:=x) hz i ⟨hi.1.le,hi.2⟩
  rw [show CR (1,0) (Complex.I,0) (fun z=> Dot f (breeze i z)) k = CR (1,0) (Complex.I,0) (Dot f ∘ breeze i) k from rfl]
  refine CR.pull _ ((breeze (E:=E) i).hasFDerivAt) ?_ ?_
  · exact ((h.stream.fderiv.apply (X:=ContinuousLinearMap.apply ℝ ℂ (1,(0:E)))).smooth _ hv).differentiableAt (by simp)
  have hb : CR (1,(0:E)) (Complex.I,0) (Dot f) (breeze i k):=field_cr (Metric.isOpen_ball.prod isOpen_univ) h.stream h.cr _ hv
  unfold CR at hb ⊢
  rw [show breeze i ((1:ℂ),(0:E))=i • ((1:ℂ),(0:E)) by ext1<;>simp [Complex.real_smul], show breeze i (Complex.I,(0:E)) = i • (Complex.I,(0:E)) by ext1<;>simp [Complex.real_smul],map_smul,map_smul,hb,mul_smul_comm]
omit hc
lemma unfold_tear {z : ℂ} (hz : z∈zone R) (x:E) :
    f z x= f 0 x + z*tear f z x:= by
  let K(r:ℝ) := f ((r:ℂ)*z) x
  have ht r (hr:r∈Icc (0:ℝ) 1) := passage (x:=x) hz r hr
  have hb i (hi : i ∈ Icc (0:ℝ) 1) : HasDerivAt K (z* Dot f (breeze i (z,x))) i := by
    let a : ℂ := (i:ℂ)*z
    have hf := (h.region a (ht i hi).1 x); let g(m : ℂ):= f m x
    have hD : Dot f (breeze i (z,x))=deriv g a := by
      let D := fderiv ℝ (fun x:ℂ × E=>f x.1 x.2) (a,x)
      have hP : DifferentiableAt ℝ (fun x:ℂ × E=>f x.1 x.2) (a,x) := (h.stream.smooth _ (ht i hi)).differentiableAt (by simp)
      have ht : HasFDerivAt (fun i:ℂ => (i,x)) (ContinuousLinearMap.inl ℝ ℂ E) a := ((hasFDerivAt_id (𝕜:=ℝ) a).prodMk (hasFDerivAt_const ..))
      have hQ : fderiv ℝ g a = D.comp (ContinuousLinearMap.inl ..) := ((hP.hasFDerivAt.comp (f:=fun i:ℂ => (i,x)) a ht).fderiv)
      have hs := congr_arg (fun H:ℂ→L[ℝ]ℂ=>H 1) hQ
      rw [(show DifferentiableAt ℂ g a from hf).fderiv_restrictScalars ℝ] at hs
      exact hs.symm
    rw [hD]
    have hz : HasDerivAt (fun i:ℝ=> (i:ℂ)*z) z i := by simpa using (Complex.ofRealCLM.hasDerivAt (x:=i)).mul_const z
    have hp := ((show DifferentiableAt ℂ g a from hf).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt i hz
    have he := map_smul (fderiv ℂ g a) z (1:ℂ)
    change fderiv ℂ g a (z*1)=z*deriv g a at he; rw [mul_one] at he; exact hp.congr_deriv he
  have hu : IntervalIntegrable (fun i=>z*Dot f (breeze i (z,x))) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable ?_; rw [uIcc_of_le zero_le_one]; intro i hi
    refine ContinuousAt.continuousWithinAt ((show ContinuousAt (fun t : ℝ=> Dot f (breeze t (z,x))) i from ?_).const_mul z)
    have hf:(ContinuousAt (Dot f) (breeze i (z,x))):=((h.stream.fderiv.apply (X:=ContinuousLinearMap.apply ℝ ℂ (1,(0:E)))).smooth _ (ht i hi)).continuousAt
    exact hf.comp (f:=fun t:ℝ=> breeze t (z,x)) (x:=i) (by simp only [glides]; fun_prop)
  have hv:= intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=1) (f:=K) (by rw [uIcc_of_le zero_le_one]; exact hb) hu
  rw [intervalIntegral.integral_of_le zero_le_one,integral_const_mul] at hv
  simp only [K,Complex.ofReal_zero,Complex.ofReal_one,one_mul,zero_mul] at hv
  unfold tear; rw [hv]; ring
end Wall
end YM.MSbar.Pole
