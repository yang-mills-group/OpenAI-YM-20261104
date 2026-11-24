import YM.Integration.IndependentSourcePathFamily

/-! The actual frozen native Wilson rows give independently marked rooted cover
input, with no assumed admissibility at the output. The two real projections of
every complex field and every complex test are retained separately and exactly. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FundedOriginalMarkedInput
open Function Finset Lattice Wilson RG Source Labels Marker
open WilsonCoeffUV WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Bank.Mosaic.Near
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address RG05Readout.Native
open Extra.Histories
open ActualRunCalibrationTests NativeCurvatureTensor ActualRunKernelPackets ActualRunCurvaturePackets
open OriginalSourceJetAddresses OriginalMarkedSourceComet IndependentSourcePathFamily
open scoped Classical BigOperators

/-- The real projection and external phase for one of the two original
complex quadratures. -/
def component (b : Bool) : ℂ →L[ℝ] ℝ := if b then Complex.imCLM else Complex.reCLM
def phase (b : Bool) : ℂ := if b then Complex.I else 1

theorem resolve (z : ℂ) : (∑ b : Bool, phase b*(component b z : ℂ))=z := by
  simp only [Fintype.sum_bool,phase,component,Bool.false_eq_true,if_true,if_false,one_mul]
  rw [mul_comm Complex.I,add_comm]
  exact Complex.re_add_im z

/-- Complex field and complex test need independent choices. This expansion
also holds inside the product for any fixed collection of independent marks. -/
theorem products {v : Type} [Fintype v] (field jet : v → ℂ) :
    (∏ i,field i*jet i) = ∑ a : v → Bool × Bool,
      ∏ i,((phase (a i).1*phase (a i).2)*
        ((component (a i).1 (field i)*component (a i).2 (jet i) : ℝ) : ℂ)) := by
  have one (z y : ℂ) : z*y=∑ b : Bool × Bool,
      (phase b.1*phase b.2)*((component b.1 z*component b.2 y : ℝ) : ℂ) := by
    calc
      _ = (∑ b : Bool,phase b*(component b z : ℂ))*(∑ b : Bool,phase b*(component b y : ℂ)) := by rw [resolve,resolve]
      _ = _ := by
        rw [Fintype.sum_prod_type,Finset.sum_mul]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun d _ => ?_)
        push_cast; ring
  simp_rw [one (field _) (jet _)]
  rw [Finset.prod_univ_sum]
  simp

variable {G : Gauge} {R : Run G} {B : MS.Local.Physical.Deck G} {p L n : ℕ} {hn : n ≤ L}
  {V : Type} [Fintype V] [DecidableEq V] (Q : MS.Land.Prescription B)
  (D : ActualRunQlocalNativeTuple.Datum R p L n hn V) (u : V → MS.Rake.Label B)
  (μ : ℝ) (orders : V → ℕ)

abbrev OrbitD (i : V) := (ActualRunQlocalNativeTuple.orbit D i).D
abbrev Count (i : V) := {s : ActualOriginalQPackets.Row (R := R) u // s.1.1=i} ×
    OriginalSourceJetAddresses.Word (depth (D.choice i).2.1)

/-- One of the actual purchases at one independent source, with the paths and
Haar input colours of its literal native slot. This is the true startup with
stored power zero, including any prescribed complex normalization of this source. -/
def chosen (normalize : V → ℂ) (colourPart : V → Bool) (i : V) (b : Count D u i) :
    Seed G (OrbitD D i) :=
  let s := b.1.val
  let ob := (ofRun R ((ActualOriginalQPackets.degree u) s.1)).data
  let r := tokenRank R (ActualOriginalQPackets.degree u) s
  let depth := (D.choice i).2.1
  let size := ((R.family.S.toDepth hn p).count.val : ℝ)⁻¹
  let original := MvPolynomial.coeff s.2.2.val (ob.shape s.2.1) *
    ActualOriginalQReaders.coordinates (R := R) u s.1 s.2.1
  let reader := ActualOriginalQReaders.fee Q u μ orders s.1 * Motion.scalar (D.motion i)
    (ActualRunQlocalNativeTuple.constant D i * multiplier depth size b.2)
  {rank:=r, head:=r, path:=fun h => ob.columns s.2.1 (word s.2.2.val h).1,
   color:=fun h => (word s.2.2.val h).2, weight:=normalize i*original*reader,
   quadrant:=component (colourPart i), knob:=⟨⟨_,Nat.lt_succ_of_le (D.depth_le i)⟩,b.2⟩,
   point:=place (R.family.S.toDepth hn p) (D.choice i).1}

/-- This finite family satisfies the actual primitive empty mask, independent
marker grade and rooted exponential norm on every placement. The numerical
bill is computed from the original finite Haar and jet rows, with no charge
involving external test values. -/
theorem admitted (normalize : V → ℂ) (colourPart : V → Bool) (grade : V → ℕ)
    (cap : ℕ) {w : ℝ} (hw : 0 < w) (Z : Finset V) (z : V → Cover) :
    let X := chosen Q D u μ orders normalize colourPart
    let B := bill X grade cap w
    let K := independent X z
    0 ≤ B ∧ Eu grade K ∧ K ∅=0 ∧ safeB z K Z cap (steep w) B := by
  exact preblock _ z Z cap hw (by intro i b; exact Nat.le_add_left _ _)

end YM.Integration.FundedOriginalMarkedInput
end
