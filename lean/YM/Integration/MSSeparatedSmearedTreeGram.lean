import YM.Integration.MSDeckProbeGram
import YM.Integration.OPETreeTests
import YM.MS.Dial.Loom
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Topology.Instances.Matrix

/-! # A normalized, positive exterior test detects the entire booked physical deck -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.MSSeparatedTestGram
open Set Filter Function Finset Metric MeasureTheory Real Matrix MS MS.Land MS.Menus MS.Rake MS.Tone
open FVA2 FVA2.ColorCode Pert.Position
open scoped Classical Topology BigOperators

variable {G : Gauge} {B : Local.Physical.Deck G} {O : Booked B}
variable (M : MS_Data G O)

def matrix (H : ℕ) (v : ℝ) (k : ℕ) (g : Test 2) : Matrix (Glyph B H) (Glyph B H) ℂ :=
  fun a b=>g.applyTo (fun z:Points 2=>MSDeckProbeGram.raw M ![a,b] z v k)

private theorem entry {H : ℕ} (a b : Glyph B H) (v : ℝ) (k : ℕ) (z : Points 2) (hz : z∈conf 2) :
    ContinuousAt (fun u=>MSDeckProbeGram.raw M ![a,b] u v k) z:=by
  have chart:Continuous (Fountain.metric (m:=2)):=by
    apply continuous_pi
    intro i
    exact Theater.out.toLinearMap.continuous_of_finiteDimensional.comp
      ((continuous_apply i).comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2=>E4)).continuous)
  have legal:Injective (Fountain.metric z):=Theater.out.injective.comp hz
  exact (Dial.contin M (labelAt B ∘ ![a,b]) (Fountain.metric z) legal univ k v).1.comp chart.continuousAt

/-- A finite matrix of genuine separated continuous kernels with an invertible
point matrix has an invertible measurement by one nonnegative unit-mass test. -/
theorem matrix_test {ι : Type} [Fintype ι] [DecidableEq ι] (row : ι→ι→Points 2→ℂ)
    (continuous : ∀ a b z,z∈conf 2 → ContinuousAt (row a b) z) {x₀ : Points 2}
    (legal : x₀∈conf 2) (unit : IsUnit (Matrix.of fun a b=>row a b x₀))
    (U : Set (Points 2)) (near : U∈𝓝 x₀) :
    ∃ g : Test 2,tsupport g⊆U ∧ (∀ z,(g z).im=0 ∧ 0≤(g z).re) ∧
      0<(g x₀).re ∧ (∫z,g z)=1 ∧ IsUnit (Matrix.of fun a b=>g.applyTo (row a b)) := by
  classical
  let J:=ι × ι
  let values (z:Points 2) (j:J):=row j.1 j.2 z
  let assemble (s:J→ℂ):Matrix ι ι ℂ:=fun a b=>s (a,b)
  let stable:= {s:J→ℂ | (assemble s).det≠0}
  have regular : Continuous assemble:=continuous_matrix fun a b=>continuous_apply (a,b)
  have openSet:IsOpen stable:=isOpen_ne_fun regular.matrix_det continuous_const
  have locked:values x₀∈stable:=
    ((Matrix.isUnit_iff_isUnit_det _).mp unit).ne_zero
  obtain ⟨ε,hε,safe⟩:=Metric.isOpen_iff.mp openSet (values x₀) locked
  have hval:ContinuousAt values x₀:=continuousAt_pi.mpr fun j=>continuous j.1 j.2 x₀ legal
  have nearValues:values ⁻¹' closedBall (values x₀) (ε/2)∈𝓝 x₀:=
    hval (Metric.closedBall_mem_nhds _ (half_pos hε))
  obtain ⟨δ,hδ,area⟩:=Metric.nhds_basis_closedBall.mem_iff.mp
    (inter_mem (inter_mem near ((conf_open 2).mem_nhds legal)) nearValues)
  let b:ContDiffBump x₀:=⟨δ/2,δ,half_pos hδ,half_lt_self hδ⟩
  let N:=b.normed volume
  let ψ (z:Points 2):ℂ:=N z
  have compact:HasCompactSupport ψ:=(b.hasCompactSupport_normed (μ:=volume)).comp_left (g:=fun c:ℝ=>(c:ℂ)) Complex.ofReal_zero
  have support:tsupport ψ⊆closedBall x₀ δ:=by
    change tsupport ψ ⊆ closedBall x₀ b.rOut
    rw [←b.tsupport_normed_eq (μ:=volume)]
    apply closure_mono
    intro z hz
    exact fun eq=>hz (by change ((b.normed volume z:ℝ):ℂ)=0;rw [eq,Complex.ofReal_zero])
  let g:Test 2:=⟨ψ,Complex.ofRealCLM.contDiff.comp (b.contDiff_normed (μ:=volume)),compact,
    fun z hz=>(area (support hz)).1.2⟩
  have stamp (z:Points 2): (g z).im=0 ∧ 0≤(g z).re:=⟨rfl,b.nonneg_normed z⟩
  have positive:0<(g x₀).re:=by
    change 0<b x₀/(∫z,b z)
    rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)]
    exact one_div_pos.mpr (b.integral_pos (μ:=volume))
  have normalized:(∫ z,g z)=1:=by
    change (∫ z,((b.normed volume z:ℝ):ℂ))=1
    rw [integral_complex_ofReal,b.integral_normed,Complex.ofReal_one]
  have mass:(∫ z,‖g z‖)=1:=by
    calc
      _=∫z,b.normed volume z:=integral_congr_ae (ae_of_all _ fun z=>by
        change ‖((b.normed volume z:ℝ):ℂ)‖=b.normed volume z
        rw [Complex.norm_real,Real.norm_of_nonneg (b.nonneg_normed z)])
      _=1:=b.integral_normed
  have base (c:ℂ):g.applyTo (fun _=>c)=c:=by
    change (∫ z,g z*c)=c
    rw [integral_mul_const,normalized,one_mul]
  let avg:J→ℂ:=fun j=>g.applyTo (fun z=>values z j)
  have err(j:J):‖avg j-values x₀ j‖≤ε/2:=by
    have hpz(z:Points 2)(hz:z∈tsupport g) : ‖values z j-values x₀ j‖≤ε/2:=by
      have ball:= (area (support hz)).2
      have joint:‖values z-values x₀‖≤ε/2:=by
        rw [←dist_eq_norm]
        exact ball
      exact (pi_norm_le_iff_of_nonneg (half_pos hε).le).mp joint j
    have estimate:=OPETreeTests.bound g (fun z=>values z j-values x₀ j) (ε/2) hpz
    have read:=OPETreeTests.difference g (fun z=>values z j) (fun _=>values x₀ j)
      (fun z hz=>continuous j.1 j.2 z (g.tsupport_subset hz)) (fun _ _=>continuousAt_const)
    rw [read,base,mass,one_mul] at estimate
    exact estimate
  have close:avg∈Metric.ball (values x₀) ε:=by
    rw [mem_ball,dist_eq_norm]
    exact lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg (half_pos hε).le).mpr err) (half_lt_self hε)
  have usable:(assemble avg).det≠0:=safe close
  exact ⟨g,fun z hz=>(area (support hz)).1.1,stamp,positive,normalized,
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr usable)⟩

/-- A bump with mass one and support inside any prescribed neighborhood of the
actual separated pair. One choice detects every pair of booked labels at once. -/
theorem localized (V : Warehouse G) (M : MS_Data G O) (H : ℕ) (v : ℝ) {p : E4} (hp : (0:E4)≠p)
    (U : Set (Points 2)) (near : U∈𝓝 (Extra.FD.couple 0 p)) :
    ∃g:Test 2,tsupport g⊆U ∧ (∀z,(g z).im=0 ∧ 0≤(g z).re) ∧
      0<(g (Extra.FD.couple 0 p)).re ∧ (∫z,g z)=1 ∧ IsUnit (matrix M H v 0 g):=by
  exact matrix_test (fun (a b:Glyph B H) z=>MSDeckProbeGram.raw M ![a,b] z v 0)
    (fun a b=>entry M a b v 0) (Extra.FD.couple_ok hp) (MSDeckProbeGram.invertible V M v hp H) U near

theorem invertible (V : Warehouse G) (M : MS_Data G O) (H : ℕ) (v : ℝ) {p : E4} (hp : (0:E4)≠p) :
    ∃g:Test 2,(∀z,(g z).im=0 ∧ 0≤(g z).re) ∧ (∫z,g z)=1 ∧ IsUnit (matrix M H v 0 g):=by
  obtain ⟨g,_,nonnegative,_,normalized,unit⟩:=localized V M H v hp univ Filter.univ_mem
  exact ⟨g,nonnegative,normalized,unit⟩


/-- The free MS matrix has the same measured entries at all scale parameters. -/
theorem scale (V : Warehouse G) (M : MS_Data G O) (H : ℕ) (u v : ℝ) (g : Test 2) :
    matrix M H u 0 g=matrix M H v 0 g:=by
  apply Matrix.ext
  intro a b
  apply OPETreeTests.on_support g
  intro z hz
  exact (MSDeckProbeGram.free V M ![a,b] z (g.tsupport_subset hz) u).trans
    (MSDeckProbeGram.free V M ![a,b] z (g.tsupport_subset hz) v).symm

/-- The choice in a prescribed neighborhood can be made before all real scale
parameters, for the complete finite collection of genuine two-point rows. -/
theorem simultaneous (V : Warehouse G) (M : MS_Data G O) (H : ℕ) {p : E4} (hp : (0:E4)≠p)
    (U : Set (Points 2)) (near : U∈𝓝 (Extra.FD.couple 0 p)) :
    ∃g:Test 2,tsupport g⊆U ∧ (∀z,(g z).im=0 ∧ 0≤(g z).re) ∧
      0<(g (Extra.FD.couple 0 p)).re ∧ (∫z,g z)=1 ∧ ∀v:ℝ,IsUnit (matrix M H v 0 g):=by
  obtain ⟨g,hs,hr,hp',hn,hu⟩:=localized V M H 0 hp U near
  exact ⟨g,hs,hr,hp',hn,fun v=>scale V M H 0 v g ▸ hu⟩

end YM.Integration.MSSeparatedTestGram
