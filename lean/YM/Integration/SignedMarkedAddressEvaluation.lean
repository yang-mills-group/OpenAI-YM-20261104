import YM.Integration.NativeMarkedAddressTokens
import YM.Integration.SignedMarkedChartGerm

/-! Exact pre-integration reconstruction of an arbitrary independently marked path current from the same address measures and coupled finite Wilson field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SignedMarkedAddressEvaluation
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Marker Precision Tree Laurent Exterior Bloch Matrix PowerSeries
open ComparisonDensity.Address Comparison.Density.RenderM LocalComparison Comparison.RG02 WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Embroider WilsonCoeffUV.Embroider.Canvas
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Soil Stationary
open FreeResolvent WilsonCoeffUV.Mer
open scoped BigOperators Classical Topology ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {ι : Type} [DecidableEq ι] [Fintype ι] {G : Gauge} (O : ι→ Orbit) (J : Finset ι) (Y : ι→ Dip)
local notation "D" => NativeMarkedAddressTokens.axes O

def axis (b : Bool) : ℂ→L[ℝ]ℝ := if b then Complex.imCLM else Complex.reCLM
def scalar (b : Bool) : ℂ := if b then Complex.I else 1
private theorem resolution (z : ℂ) : (∑b:Bool,scalar b*(axis b z:ℝ))=z := by
  simp [scalar,axis]
  simpa only [add_comm,mul_comm] using Complex.re_add_im z

def scroll (x : TestSpace O) (a : ι) (b : Bool) : Scroll (D a) :=
  ⟨axis b ∘ (Y a).plant (x a).val,(axis b).contDiff.comp ((Dip.smooth (Y:=Y a) (U:=O a)) ((O a).admits (x a)).choose_spec.orders)⟩

def family (x : TestSpace O) (s : J→ Bool) : Case D := fun a=>page _ (scroll O Y x a (if h:a∈J then s ⟨a,h⟩ else false))

def phase (s : J→ Bool) : ℂ := ∏a:J,scalar (s a)

def projector (x : TestSpace O) (L : ℂ→L[ℝ]ℝ) : Pen D J→L[ℝ]ℝ := ∑s:J→ Bool,L (phase J s) • touch (family O J Y x s) J

omit [DecidableEq ι] [Fintype ι] in
private theorem jet_value (x : TestSpace O) (a : ι) (b : Bool) (k : Knob (D a)) (u : Chamber) :
    crease (scroll O Y x a b) k.2 u.val=axis b (NativeMarkedAddressTokens.slot O Y x a k u) := by
  change iteratedFDeriv ℝ k.1.val ((axis b) ∘ (Y a).plant (x a).val) u.val _ = _
  rw [ContinuousLinearMap.iteratedFDeriv_comp_left _ (Dip.smooth (Y:=Y a) (U:=O a) ((O a).admits (x a)).choose_spec.orders).contDiffAt (Nat.cast_le.mpr (Nat.le_of_lt_succ k.1.isLt))]
  rfl

private theorem compose_axes {A : Type} [Fintype A] (v : A→ℂ) (w : ℝ) :
    (w:ℂ)*(∏ a,v a)=∑ σ:A→Bool,(∏ a,scalar (σ a))*((w*(∏ a,axis (σ a) (v a)):ℝ):ℂ) := by
  calc
    _=(w:ℂ)*∏ a,∑ b:Bool,scalar b*(axis b (v a):ℝ) := by
      apply congrArg ((w:ℂ)*·)
      exact prod_congr rfl (fun a _ => (resolution (v a)).symm)
    _=_ := by
      rw [Fintype.prod_sum,mul_sum]
      apply sum_congr rfl
      intro σ _
      rw [prod_mul_distrib,Complex.ofReal_mul,Complex.ofReal_prod]
      ring

omit [Fintype ι] in
/-- Each incoming complex slot has its original affine pullback and independent derivative label. The full signed coefficient in the address is retained. -/
theorem resolve (x : TestSpace O) (q : Sky D) : NativeMarkedAddressTokens.addressValue O J Y x q=
    ∑s:J→ Bool,phase J s*(mica (family O J Y x s) J q:ℝ) := by
  let u (a : J) := NativeMarkedAddressTokens.slot O Y x a.val (q.2 a).1 (q.2 a).2
  have ht (s : J→ Bool) : mica (family O J Y x s) J q=positiveP q.1*(∏a:J,axis (s a) (u a)) := by
    rw [show mica (family O J Y x s) J q=positiveP q.1*∏a∈J,crease (scroll O Y x a (if h:a∈J then s ⟨a,h⟩ else false)) (q.2 a).1.2 (q.2 a).2.val from slippery _ J q,←prod_coe_sort]
    congr 1
    exact prod_congr rfl fun a _=>by simpa [u,a.property] using jet_value O Y x a.val (s a) (q.2 a).1 (q.2 a).2
  have address : NativeMarkedAddressTokens.addressValue O J Y x q=(positiveP q.1:ℂ)*(∏ a:J,u a) := by
    unfold NativeMarkedAddressTokens.addressValue
    rw [←prod_coe_sort]
  rw [address,compose_axes]
  apply Finset.sum_congr
  · exact congrArg (@Finset.univ (J→Bool)) (Subsingleton.elim _ _)
  · intro σ _
    rw [ht σ]
    rfl

omit [DecidableEq ι] in
private theorem integrable_mica (a : Case D) (μ : Measure (Sky D)) [IsFiniteMeasure μ] : Integrable (fun q=>mica a J q) μ := by
  have hc : Continuous (fun q:Sky D=>mica a J q) := ((continuous_of_discreteTopology : Continuous positiveP).comp continuous_fst).mul ((folio a J).continuous.comp continuous_snd)
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- All genuine rows reuse the same physical Riesz measures before choosing any test or any real/imaginary component. -/
theorem weight {r : ℕ} (P : Comet G (Pen D J) r) (μ : Stationary.Ink G r→ Measure (Sky D)) (h : Barn P μ)
    (x : TestSpace O) (L : ℂ→L[ℝ]ℝ) (i : Stationary.Ink G r) :
    projector O J Y x L (P.wage i)=L (∫q,NativeMarkedAddressTokens.addressValue O J Y x q ∂(μ i)) := by
  letI : IsFiniteMeasure (μ i) := (h i).2.1
  have hI (s : J→ Bool) : Integrable (fun q=>phase J s*(mica (family O J Y x s) J q:ℝ):Sky D→ℂ) (μ i) :=
    ((integrable_mica O J _ _).ofReal).const_mul _
  simp_rw [resolve O J Y x]
  rw [integral_finsetSum _ fun s _=>hI s,map_sum]
  simp only [projector,_root_.sum_apply,_root_.smul_apply,smul_eq_mul]
  apply sum_congr rfl
  intro s _
  rw [(h i).2.2.2,integral_const_mul,integral_complex_ofReal]
  rw [mul_comm (phase J s),←Complex.real_smul,map_smul,smul_eq_mul,mul_comm]

/-- The full mixed analytic source, all invariant colours and every joint test. No factorial or independent address survives as an extra hypothesis. -/
theorem source {r : ℕ} {n : Side} (P : Comet G (Pen D J) r) (hP : shadeStar P)
    (μ : Stationary.Ink G r→ Measure (Sky D)) (h : Barn P μ) (z : ι→ Cover) (o : ι) (a : Site n) (support : ι→ Support n)
    (x : TestSpace O) (L : ℂ→L[ℝ]ℝ) (U : Config G n) :
    (dip P (projector O J Y x L)).unmasked U a=L (∑i,(NativeMarkedAddressTokens.token O J Y P μ i z o a support).read x U) := by
  rw [Atom.unmasked,dip_reads _ _ hP,map_sum]
  apply sum_congr rfl
  intro i _
  rw [weight O J Y P μ h x L i,NativeMarkedAddressTokens.value,←Complex.real_smul,map_smul,smul_eq_mul,mul_comm]
  rfl

section Numerics
variable {c f : Side} (S : StepData c f) (F : Forest S.ratio) (M : Matrix (Woods G f) (Woods G c) ℝ) (ρ : fieldDir G c 1→ AxisChart G F)

theorem measured {r : ℕ} (P : Comet G (Pen D J) r) (hP : shadeStar P)
    (μ : Stationary.Ink G r→ Measure (Sky D)) (h : Barn P μ) (z : ι→ Cover) (o : ι) (sup : ι→ Support f)
    (x : TestSpace O) (L : ℂ→L[ℝ]ℝ) (e b t : ℕ) (ht : b+e=r+t)
    (hM : M=reveal G S F*((reveal G S F).transpose*M)) (hρ : ContDiffAt ℝ ω ρ 0) (h0 : ρ 0=0) :
    (X:Ink (Active G F⊕Woods G c))^b*retool (shore S F M ρ) (loom (camSlice G S F M) (flash (ply (projector O J Y x L).toLinearMap ((volumeR P e).1 f))))=
      X^t*jet (fun y : Sloc S F G=>L (∑i,(NativeMarkedAddressTokens.token O J Y P μ i z o 0 sup).read x (Work.F03.live F (SignedMarkedChartGerm.chart S F ρ y)))) := by
  rw [SignedMarkedChartGerm.cleared S F M ρ P _ e b t ht hM hρ h0]
  simp_rw [source O J Y P hP μ h z o 0 sup x L]
end Numerics
end YM.Integration.SignedMarkedAddressEvaluation
