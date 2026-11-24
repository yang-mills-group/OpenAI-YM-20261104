import YM.Integration.WilsonCoherentFrozenTaylor
import YM.Integration.WilsonOriginalWardContraction

/-! The four-link Wilson price at arbitrary compact left and right
pivots. The true radial coefficients and the Taylor constant are fixed
before all finite tori, plaquette positions, and frozen links. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalPlaquetteTaylor
open Set Function Finset Lattice Wilson RG
open scoped Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge}

abbrev Pivots (G : Gauge) := (Fin 4→G.El) × (Fin 4→G.El)
abbrev Angles (G : Gauge) := Fin 4→G.Color
abbrev Ambient (G : Gauge) := (Fin 4→G.Mat) × (Fin 4→G.Mat) × Angles G

def placed (b : Pivots G) (z : Angles G) (i : Fin 4) := b.1 i*G.lieExp (z i)*b.2 i
def loop (u : Fin 4→G.El) := u 0*u 1*(u 2)⁻¹*(u 3)⁻¹
def value (b : Pivots G) (z : Angles G) : ℂ := G.price (loop (placed b z))
def row (b : Pivots G) (z : Angles G) (i : ℕ) : ℝ :=
  (SignedChartTaylor.jet (value b) z i).re

def frame (b : Pivots G) : Ambient G := (G.mat ∘ b.1,G.mat ∘ b.2,0)
def direction (z : Angles G) : Ambient G := (0,0,z)
def entries (v : Ambient G) (i : Fin 4) := v.1 i * G.mat (G.lieExp (v.2.2 i)) * v.2.1 i
def extension (G : Gauge) (v : Ambient G) : ℂ :=
  ((1-(entries v 0 * entries v 1 * star (entries v 2) * star (entries v 3)).trace.re/(G.repDim:ℝ)):ℝ)

theorem analytic : ContDiff ℝ ω (extension G) := by
  have e (i:Fin 4) : ContDiff ℝ ω (fun v:Ambient G=>entries v i) := by
    apply ContDiff.mul
    · exact ((contDiff_apply ℝ G.Mat i).comp contDiff_fst).mul
        (G.exp_jet.comp ((contDiff_apply ℝ G.Color i).comp (contDiff_snd.comp contDiff_snd)))
    · exact (contDiff_apply ℝ G.Mat i).comp (contDiff_fst.comp contDiff_snd)
  have conjugate (i:Fin 4) := (starL ℝ : G.Mat≃L[ℝ]G.Mat).contDiff.comp (e i)
  let trace : G.Mat→L[ℝ]ℝ := Complex.reCLM.comp
    ((Matrix.traceLinearMap (Fin G.repDim) ℝ ℂ).toContinuousLinearMap)
  exact Complex.ofRealCLM.contDiff.comp (contDiff_const.sub
    ((trace.contDiff.comp ((((e 0).mul (e 1)).mul (conjugate 2)).mul (conjugate 3))).div_const _))

theorem base : Continuous (frame (G:=G)) := by
  exact (continuous_pi (fun i=>G.continuous_mat.comp ((continuous_apply i).comp continuous_fst))).prodMk
    ((continuous_pi (fun i=>G.continuous_mat.comp ((continuous_apply i).comp continuous_snd))).prodMk continuous_const)

theorem observed (b:Pivots G) (z:Angles G) : extension G (frame b+direction z)=value b z := by
  simp [extension,value,loop,placed,Gauge.price,entries,direction,frame,G.mat_mul,G.mat_inv]

theorem scaled (z:Angles G) (t:ℝ) : t • direction z=direction (t•z) := by simp [direction]

theorem words (b:Pivots G) (z:Angles G) (j:ℕ) :
    SignedChartTaylor.jet (fun h=>extension G (frame b+h)) (direction z) j=SignedChartTaylor.jet (value b) z j := by
  have physical : (fun r:ℝ=>extension G (frame b+r•direction z))=(fun r:ℝ=>value b (r•z)) :=
    funext fun r=>by rw [scaled,observed]
  unfold SignedChartTaylor.jet
  rw [physical]

theorem complexBill (G:Gauge) (p:ℕ) : ∃ C:ℝ,0≤C ∧ ∀b:Pivots G,∀z:Angles G,∀t:ℝ,0<t→t*‖z‖<1→
    ‖value b (t•z)-∑i∈range (p+1),t^i • SignedChartTaylor.jet (value b) z i‖≤C*(t*‖z‖)^(p+1) := by
  letI : FiniteDimensional ℝ G.Mat := by
    change Module.Finite ℝ (Fin G.repDim→Fin G.repDim→ℂ);infer_instance
  letI : FiniteDimensional ℝ (Fin 4→G.Mat) := inferInstance
  letI : FiniteDimensional ℝ (Angles G) := inferInstance
  letI : FiniteDimensional ℝ ((Fin 4→G.Mat) × Angles G) := inferInstance
  letI : FiniteDimensional ℝ (Ambient G) := inferInstance
  obtain ⟨C,hC,bill⟩:=WilsonCoherentFrozenTaylor.purchased (extension G) analytic (frame (G:=G)) base p
  refine ⟨C,hC,?_⟩;intro b z t ht room
  have mag : ‖direction z‖=‖z‖ := by simp [direction,Prod.norm_def]
  have inner : t*‖direction z‖<1 := mag ▸ room
  have raw := bill b (direction z) t ht inner
  simpa only [mag,scaled,observed,words] using raw

theorem purchased (G:Gauge) (p:ℕ) : ∃ C:ℝ,0≤C ∧ ∀b:Pivots G,∀z:Angles G,∀t:ℝ,0<t→t*‖z‖<1→
    |G.price (loop (placed b (t•z)))-∑i∈range (p+1),t^i*row b z i|≤C*(t*‖z‖)^(p+1) := by
  obtain ⟨C,hC,bill⟩:=complexBill G p
  refine ⟨C,hC,?_⟩;intro b z t ht room
  refine (le_trans ?_ (bill b z t ht room))
  simpa only [row,Complex.sub_re,Complex.re_sum,Complex.smul_re,smul_eq_mul,value,Complex.ofReal_re] using
    (Complex.abs_re_le_norm (value b (t•z)-∑i∈range (p+1),t^i • SignedChartTaylor.jet (value b) z i))

end YM.Integration.WilsonLocalPlaquetteTaylor
