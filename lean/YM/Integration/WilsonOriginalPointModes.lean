import YM.Integration.ActualOriginalQInitialPreparation

/-! The full uncooled point insertion is an actual gauge-dependent array with a single
scalar dependence on the test in each occupied mode. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPointModes
open Function Finset Lattice Wilson RG Marker Source Labels FVA1
open PhysicalNext.Repeat.Legato LocalComparison LocalComparison.Global ComparisonDensity.Address
open MergeProof MergeProof.Accent RG3.Script.Picnic FullQLocal.RenderedStep
open scoped Classical BigOperators

variable {V : Type}
/-- A native test for the exact point evaluation. If every admitted test is zero there,
that slot vanishes in every submitted field. -/
def calibration (D : V→Orbit) : TestSpace D := fun i=>
  if h : ∃ f : (D i).Mood,f.val 0≠0 then ((h.choose).val 0)⁻¹ • h.choose else 0

theorem at_point (D : V→Orbit) (x : TestSpace D) (i : V) :
    (x i).val 0=(x i).val 0*(calibration D i).val 0 := by
  by_cases h : ∃ f : (D i).Mood,f.val 0≠0
  · rw [calibration,dif_pos h]
    change (x i).val 0=(x i).val 0*(((h.choose).val 0)⁻¹*(h.choose).val 0)
    rw [inv_mul_cancel₀ h.choose_spec,mul_one]
  · have hx : (x i).val 0=0 := by by_contra hn;exact h ⟨x i,hn⟩
    rw [hx,zero_mul]

variable {G : Gauge} [DecidableEq V] [Fintype V] [Nonempty V] {B : MS.Local.Physical.Deck G}
    (R : Run G) (hG : G.Simple) (J : Request V) (u : V→MS.Rake.Label B)
    {N p L : ℕ} (Q : MS.Land.Prescription B) (o : V→Site (R.family.side L p))
    (μ : ℝ) (degree : V→ℕ) (above : L≤N)
local notation "D" => ActualOriginalQPointSetup.pointDatum R J p L o
local notation "tests" => ActualRunQlocalNativeTuple.orbit (D)
local notation "Y" => R.family.path.rep N p L
local notation "Γ" => Stock.census V
local notation "raw" => ActualOriginalQInput.input Q (D) u μ degree hG N above

theorem raw_mode (ref : ∀s : ActualOriginalQReaders.Slot u,R.family.ref s.2.size ≤ L)
    (x : TestSpace (tests)) (k : (Γ).Mode) (U : Config G (R.family.side L p)) :
    (((raw).leaf x).density U).part k=(∏i∈k.val,(x i).val 0)*(((raw).leaf (calibration (tests))).density U).part k := by
  let charge (i : V) := ActualOriginalCalibratedColumns.weightedObservable R B Q (u i) μ (R.family.side L p) (ActualRunQlocalNativeTuple.root (D) i) U (degree i)
  have body (y : TestSpace (tests)) : (((raw).leaf y).density U).part k=
      ((Y).eval U:ℂ)*∏i∈k.val,(y i).val 0*charge i := by
    rw [ActualOriginalQInput.density_full Q (D) u μ degree hG N above ref y U,Accent.birth,Poly.part_smul,Accent.Mach,Extra.Trajectories.pass_fire]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    exact congrArg (fun z=>z*charge i) (ActualOriginalQPointDatum.reader_eq R p L o _ _ i (y i))
  rw [body x,body (calibration (tests))]
  have union : (∏i∈k.val,(x i).val 0*charge i)=∏i∈k.val,((x i).val 0*((calibration (tests) i).val 0*charge i)) := by
    apply Finset.prod_congr rfl
    intro i _
    rw [←mul_assoc,←at_point (tests) x i]
  rw [union,Finset.prod_mul_distrib]
  ring

end YM.Integration.WilsonOriginalPointModes
