import YM.Integration.WilsonThermometerPositionFilmSocketJet

/-! The angular jet at a later chronological page retains the measured two leading coefficients of each original group-field socket. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerPositionFilmReceivedSocket
open Function Filter Finset RG Lattice Exterior Tree Marker Multi
open Comparison.RG02 Comparison.RG02.Assembly Comparison.RG02.Adjacent
open Comparison.RG02.Moving.Path RegulatorIR RegulatorIR.FVAAlt2.Booth RegulatorIR.FVAAlt2.Pipeline
open QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise
open scoped Classical BigOperators Topology ContDiff
open private starts from YM.Integration.WilsonThermometerPositionFilmSocketJet

variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (clock:UnitCost)
    (flat:HasDerivAt clock.rating 0 0) (x:E)

include flat

private theorem firstTwo (n:ℕ) (low:n≤2) :
    let f:=fun t:ℝ=>(clock.enter t,t • x)
    let g:=ContinuousLinearMap.toSpanSingleton ℝ ((1,x):ℝ×E)
    iteratedFDeriv ℝ n f 0=iteratedFDeriv ℝ n g 0 := by
  intro f g
  have smooth:ContDiffAt ℝ ω f 0:=
    (contDiffAt_id.mul clock.smooth).prodMk (contDiffAt_id.smul contDiffAt_const)
  have rate:GradeAt 2 (fun t=>clock.rating t-1):=starts _ (clock.smooth.sub contDiffAt_const)
    (by simp [clock.origin]) (by simpa using flat.sub_const 1)
  have id₁:GradeAt 1 (fun t:ℝ=>t):=GradeAt.anchored contDiffAt_id rfl
  have both:=GradeAt.linear_contact (ContinuousLinearMap.inl ℝ ℝ E) (id₁.mul rate)
  have difference : f-g=(ContinuousLinearMap.inl ℝ ℝ E) ∘ (fun t=>t*(clock.rating t-1)) := by
    funext t
    apply Prod.ext
    · change t*clock.rating t-t*1=t*(clock.rating t-1)
      ring
    · change t•x-t•x=0
      exact sub_self _
  change GradeAt 3 ((ContinuousLinearMap.inl ℝ ℝ E) ∘ (fun t=>t*(clock.rating t-1))) at both
  rw [←difference] at both
  have hands:=both.vanish n (by omega)
  rw [iteratedFDeriv_sub_apply (smooth.of_le le_top) (g.contDiff.contDiffAt.of_le le_top)] at hands
  exact sub_eq_zero.mp hands

private theorem prefactor (d:ℕ) : GradeAt 2 (fun t=>(clock.rating t^d)⁻¹-1) := by
  have ok:clock.rating 0^d≠0:=by simp [clock.origin]
  have hd:HasDerivAt (fun t=>clock.rating t^d) 0 0:=by simpa using! flat.pow d
  have rate:HasDerivAt (fun t=>(clock.rating t^d)⁻¹) 0 0:=by simpa using! hd.inv ok
  exact starts _ (((clock.smooth.pow d).inv ok).sub contDiffAt_const) (by simp [clock.origin]) (by simpa using rate.sub_const 1)

private theorem entered (d k:ℕ) (good:k≤d+1) (letter:ℝ×E→ℂ) (graded:GradeAt d letter) :
    motion (fun t=>(clock.rating t^d)⁻¹ • letter (clock.enter t,t•x)) k=jet letter k (1,x) := by
  let f:=fun t:ℝ=>(clock.enter t,t•x)
  let g:=ContinuousLinearMap.toSpanSingleton ℝ ((1,x):ℝ×E)
  have hf:ContDiffAt ℝ ω f 0:=(contDiffAt_id.mul clock.smooth).prodMk (contDiffAt_id.smul contDiffAt_const)
  have f0:f 0=0:=by simp [f,UnitCost.enter]
  have here:ContDiffAt ℝ ω letter (f 0):=f0.symm ▸ graded.smooth
  have nested:ContDiffAt ℝ ω (letter∘f) 0:=here.comp 0 hf
  have money:=GradeAt.scale (prefactor clock flat d) (GradeAt.coarse graded hf f0)
  have contact:=WilsonThermometerPositionFilmSocketJet.curve letter graded good f g hf g.contDiff.contDiffAt f0
    (map_zero g) (firstTwo clock flat x)
  let extra:=fun t=>(clock.rating t^d)⁻¹ • letter (f t)
  have paid:ContDiffAt ℝ ω extra 0:=((clock.smooth.pow d).inv (by simp [clock.origin])).smul
    nested
  have diff:extra-(letter∘f)=(fun t=>( (clock.rating t^d)⁻¹-1) • letter (f t)):=by
    funext t
    change (clock.rating t^d)⁻¹ • letter (f t)-letter (f t)=((clock.rating t^d)⁻¹-1) • letter (f t)
    rw [sub_smul,one_smul]
  have high:=money.vanish k (by omega)
  change iteratedFDeriv ℝ k (fun t=>((clock.rating t^d)⁻¹-1) • letter (f t)) 0=0 at high
  rw [←diff,iteratedFDeriv_sub_apply (paid.of_le le_top) (nested.of_le le_top)] at high
  have exact₁:= (sub_eq_zero.mp high).trans contact
  have path:jet extra k 1=jet (letter∘g) k 1:= by unfold Assembly.jet; rw [exact₁]
  exact path.trans (by rw [jet_continuous_right g (graded.smooth.of_le le_top),
    show g 1=(1,x) from one_smul ℝ _])

theorem original {G:Gauge} {s:Side} {V:Type} [DecidableEq V] (R:Census V) (v:V) (C:Bulk.Colors R G s)
    (legal:Bulk.Well C) (e:Fin 2) (y:fieldDir G s 1) :
    See.noseC R v clock C e.val y=
        jet (Bulk.projected (C.mark (Arm.pub v))) (C.power (Arm.pub v)+e.val) (1,y) := by
  apply entered clock flat y (C.power (Arm.pub v)) _ (by have := e.isLt; omega) _ (legal.suppose_mark _)

end YM.Integration.WilsonThermometerPositionFilmReceivedSocket
