import YM.Integration.SignedMarkedAddressEvaluation

/-! The uncut source coordinates of the actual Riesz curvature token.
The local reading uses each specified affine field and every prescribed
undivided jet. Each coloured coefficient is separately complex multilinear. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalMeasuredSourceRows
open Function Set Finset MeasureTheory Lattice RG Wilson Marker Precision Tree Laurent
open ComparisonDensity.Address Comparison.Density.RenderM LocalComparison
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Express
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Embroider
open WilsonCoeffUV.Embroider.Canvas
open scoped BigOperators Classical Topology ContDiff

variable {I : Type} [DecidableEq I] [Fintype I] (O : I → Orbit) (Y : I → Dip)
variable (fits : ∀ i, (Y i).Fits (O i).field)

def jetAt (i : I) (k : Knob (NativeMarkedAddressTokens.axes O i)) (a : Chamber) (f : (O i).Mood) : ℂ :=
  iteratedFDeriv ℝ k.1.val ((Y i).plant f.val) a.val (dot ∘ k.2)

omit [DecidableEq I] [Fintype I] in
include fits in
private theorem smooth (i : I) (k : Knob (NativeMarkedAddressTokens.axes O i)) (f : (O i).Mood) (a : Chamber) :
    ContDiffAt ℝ k.1.val ((Y i).plant f.val) a.val := by
  obtain ⟨c,hc⟩ := (O i).admits f
  exact (((Dip.held (fits i) f hc).orders).of_le
    (Nat.cast_le.mpr (Nat.le_of_lt_succ k.1.isLt))).contDiffAt

omit [DecidableEq I] [Fintype I] in
include fits in
theorem adds (i : I) (k : Knob (NativeMarkedAddressTokens.axes O i)) (a : Chamber) (f g : (O i).Mood) :
    jetAt O Y i k a (f+g) = jetAt O Y i k a f + jetAt O Y i k a g := by
  change iteratedFDeriv ℝ _ ((Y i).plant f.val + (Y i).plant g.val) _ _ = _
  rw [iteratedFDeriv_add_apply (smooth O Y fits i k f a) (smooth O Y fits i k g a)]
  rfl

omit [DecidableEq I] [Fintype I] in
include fits in
theorem scales (i : I) (k : Knob (NativeMarkedAddressTokens.axes O i)) (a : Chamber) (z : ℂ) (f : (O i).Mood) :
    jetAt O Y i k a (z • f) = z * jetAt O Y i k a f := by
  change iteratedFDeriv ℝ _ (z • (Y i).plant f.val) _ _ = _
  rw [iteratedFDeriv_const_smul_apply (a:=z) (smooth O Y fits i k f a)]
  rfl

def region {n : Side} (support : I → Support n) :
    Comparison.Density.Testing.Region (fun i => (O i).Mood) n where
  knows i S f g := support i ⊆ S → ∀ k a, jetAt O Y i k a f = jetAt O Y i k a g
  reflexive _ _ _ _ _ _ := rfl
  tighter _ _ _ h _ _ ht hs := ht (hs.trans h)

variable (J : Finset I) {G : Gauge} {r : ℕ} {n : Side}
variable (P : Comet G (Pen (NativeMarkedAddressTokens.axes O) J) r) (μ : Stationary.Ink G r → Measure (Sky (NativeMarkedAddressTokens.axes O)))
variable (h : Stationary.Ink G r) (z : I → Cover) (o : I) (a : Site n) (s : I → Support n)

omit [DecidableEq I] [Fintype I] in
private theorem address_ext (x y : TestSpace O)
    (eq : ∀ i∈J, ∀ k a, jetAt O Y i k a (x i)=jetAt O Y i k a (y i)) (q : Sky (NativeMarkedAddressTokens.axes O)) :
    NativeMarkedAddressTokens.addressValue O J Y x q =
      NativeMarkedAddressTokens.addressValue O J Y y q := by
  unfold NativeMarkedAddressTokens.addressValue
  congr 1
  exact prod_congr rfl fun v hv => eq v hv _ _

omit [DecidableEq I] [Fintype I] in
theorem reads (b : Fin r → G.ColorIndex) :
    Comparison.Density.Testing.Reads (region O Y s) (NativeMarkedAddressTokens.token O J Y P μ h z o a s).plot J ((NativeMarkedAddressTokens.token O J Y P μ h z o a s).gem b) :=
  fun x y he => congrArg (fun v : ℂ => ((sprigB P h).coeff b:ℂ)*v) (integral_congr_ae
    (Filter.Eventually.of_forall (address_ext O Y J x y (fun i hi => he i hi
      (Finset.Subset.trans (Finset.subset_biUnion_of_mem s hi) Finset.subset_union_right)))))

private abbrev rooted (O : I → Orbit) (Y : I → Dip) (J : Finset I)
    {G : Gauge} {r : ℕ} {n : Side} (P : Comet G (Pen (NativeMarkedAddressTokens.axes O) J) r)
    (μ : Stationary.Ink G r → Measure (Sky (NativeMarkedAddressTokens.axes O)))
    (h : Stationary.Ink G r) (z : I → Cover) (o : I) (a : Site n) (s : I → Support n) :
    Token G n (fun i : I => ((O i).Mood : Type)) r :=
  NativeMarkedAddressTokens.token (ι := I) (G := G) (r := r) (n := n) O J Y P μ h z o a s

omit [DecidableEq I] [Fintype I] in
private theorem separated (x : TestSpace O) (w : Fin r → G.Color) :
    Token.touch (rooted O Y J P μ h z o a s) x w =
      (((sprigB P h).poly w : ℝ) : ℂ) *
        (∫ q : Sky (NativeMarkedAddressTokens.axes O),
          NativeMarkedAddressTokens.addressValue O J Y x q ∂(μ h)) := by
  simp only [rooted, Token.touch, NativeMarkedAddressTokens.token, Atom.poly,
    Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]
  apply sum_congr rfl
  intro i _
  ring

omit [DecidableEq I] [Fintype I] in
theorem symmetry (x : TestSpace O) (u : Fin r → G.Color) (b : G.El) :
    (rooted O Y J P μ h z o a s).touch x (fun i => G.adjoint b (u i)) = (rooted O Y J P μ h z o a s).touch x u := by
  exact (separated O Y J P μ h z o a s x _).trans ((congrArg
    (fun c : ℝ => (c:ℂ) * ∫ q,NativeMarkedAddressTokens.addressValue O J Y x q ∂(μ h))
    (sprigB_t P h b u)).trans (separated O Y J P μ h z o a s x u).symm)

private theorem integrable (x : TestSpace O) (ν : Measure (Sky (NativeMarkedAddressTokens.axes O))) [IsFiniteMeasure ν] :
    Integrable (NativeMarkedAddressTokens.addressValue O J Y x) ν := by
  have expansion := funext (SignedMarkedAddressEvaluation.resolve O J Y x)
  rw [expansion]
  apply integrable_finsetSum
  intro b _
  let B := SignedMarkedAddressEvaluation.family O J Y x b
  have hc : Continuous (fun q : Sky (NativeMarkedAddressTokens.axes O) => mica B J q) :=
    ((continuous_of_discreteTopology : Continuous positiveP).comp continuous_fst).mul
      ((folio B J).continuous.comp continuous_snd)
  exact ((hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).ofReal).const_mul _

omit [Fintype I] in
private theorem factor (x : TestSpace O) (i : I) (hi : i ∈ J) (f : (O i).Mood)
    (q : Sky (NativeMarkedAddressTokens.axes O)) :
    NativeMarkedAddressTokens.addressValue O J Y (update x i f) q =
      ((positiveP q.1 : ℝ) * (∏ v ∈ J.erase i, jetAt O Y v (q.2 v).1 (q.2 v).2 (x v)) : ℂ) *
        jetAt O Y i (q.2 i).1 (q.2 i).2 f := by
  unfold NativeMarkedAddressTokens.addressValue
  rw [←Finset.prod_erase_mul _ _ hi]
  have he : (∏ v ∈ J.erase i, NativeMarkedAddressTokens.slot O Y (update x i f) v (q.2 v).1 (q.2 v).2) =
      ∏ v ∈ J.erase i,jetAt O Y v (q.2 v).1 (q.2 v).2 (x v) :=
    prod_congr rfl fun v hv => by simp [NativeMarkedAddressTokens.slot,jetAt,(mem_erase.mp hv).1]
  rw [he]
  simp [NativeMarkedAddressTokens.slot,jetAt,mul_assoc]

include fits in
theorem linear (_sale : Barn (D := NativeMarkedAddressTokens.axes O) (J := J) P μ) (b : Fin r → G.ColorIndex) :
    RG3.Held.Letter (E := ℂ) ℂ (fun i : I => ((O i).Mood : Type)) J ((rooted O Y J P μ h z o a s).gem b) := by
  letI : IsFiniteMeasure (μ h) := (_sale h).2.1
  apply RG3.Held.Letter.cmul ((sprigB P h).coeff b : ℂ)
  refine ⟨?_,?_,?_⟩
  · intro x y eq
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (address_ext O Y J x y (fun i hi k a => by rw [eq i hi]))
  · intro x i hi f g
    rw [←integral_add (integrable O Y J (update x i f) (μ h))
      (integrable O Y J (update x i g) (μ h))]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro q
    simp only [factor O Y J x i hi,adds O Y fits,mul_add]
  · intro x i hi b f
    rw [smul_eq_mul,←integral_const_mul]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro q
    simp only [factor O Y J x i hi,scales O Y fits]
    ring


end YM.Integration.OriginalMeasuredSourceRows
end
