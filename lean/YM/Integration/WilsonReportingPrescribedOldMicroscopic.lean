import YM.Integration.ActualStartupNormalizedQ
import YM.Integration.ActualTrajectoryTransport
import YM.MergeProof.South.Loft

/-! The complete original prescribed density at an arbitrary dated Wilson
representation. Its normalized earlier reading is the actual same-period
conditional of the signed product of corrected columns on each marker face. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingPrescribedOldMicroscopic
open Function MeasureTheory Lattice Wilson RG Source Marker Precision
open IterationFour.Vacuum LocalComparison PhysicalNext.Repeat.Legato
open Push.GridApprox MergeProof MergeProof.Accent
open RG3.Script.Picnic FullQLocal.RenderedStep
open scoped Classical BigOperators

variable {G : Gauge} {B : MS.Local.Physical.Deck G} {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
  (R : Run G) (Q : MS.Land.Prescription B) {m per n : ℕ} {nm : n ≤ m + 1}
  (D : ActualRunQlocalNativeTuple.Datum R per (m+1) n nm V) (u : V→MS.Rake.Label B)
  (μ : ℝ) (orders : V→ℕ) (hG : G.Simple) {N : ℕ} (top : m + 1 ≤ N)
  (age : ∀a : ActualOriginalQReaders.Slot u,R.family.ref a.2.size ≤ m + 1)
  (x : TestSpace (ActualRunQlocalNativeTuple.orbit D))
local notation "T" => ActualOriginalQInput.input Q D u μ orders hG N top
local notation "word" => ActualStartupNormalizedQ.modeObservable Q D u μ orders x

include age in
/-- The complete prior is that of the realized cutoff N, even when the
prescribed source is born at its strictly earlier reporting scale. -/
theorem stated (s : (Stock.census V).Mode) (W : Config G (R.family.side (m+1) per)) :
    (((T).leaf x).density W).part s=(R.family.path.rep N per (m+1)).eval W • word s W := by
  rw [ActualOriginalQInput.density_full Q D u μ orders hG N top age]
  change (((R.family.path.rep N per (m+1)).eval W : ℂ) • Poly.pass (Mach (Stock.census V) _)).part s=_
  rw [Poly.part_smul,Mach,Extra.Trajectories.pass_fire]
  rfl

include age in
/-- Original Haar integrability comes from the genuine, possibly interacting
Wilson representation and finite continuous physical marked columns. -/
theorem admitted : Integrable ((T).leaf x).density (prior G _) := by
  apply Integrable.of_eval
  intro i
  change Integrable (fun W=>(((T).leaf x).density W).part i) (prior G _)
  simp_rw [stated R Q D u μ orders hG top age x]
  exact Push.SectorMeasure.Env.smul_L1 ((R.family.path.rep N per (m+1)).envelope
    (R.makes.wilson.represents N per (m+1) top).good)
    ((ActualStartupNormalizedQ.mode_continuous Q D u μ orders x i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

private theorem scalar (A : History G) (N p l : ℕ) (f : Config G (A.S.side l p)→ℂ) {j : ℕ} (jl : j ≤ l) :
    gust A N p l f j jl=pushTo A N p jl f := by
  induction jl using Nat.decreasingInduction with
  | self=>rw [gust_base,pushTo_self]
  | of_succ i ii ih=>rw [gust_step A N p l f ii,Birth.push_first A N p ii,ih]

include age in
/-- This reads each ordered subset before spatial tests, lower integration
or taking a logarithm. All stages use the same old cutoff, kernel and prior. -/
theorem original {j : ℕ} (live : j ≤ m + 1) (s : (Stock.census V).Mode) (U : Config G (R.family.side j per)) :
    (((R.family.path.rep N per j).eval U)⁻¹ • gust R.family.path N per (m+1)
      ((T).leaf x).density j live U).part s =
      actualTransport R.family (N:=N) (word s) live U := by
  let get := (Poly.get s).restrictScalars ℝ
  have held := congrFun (gust_choose R.family.path N per ((T).leaf x).density
    (admitted R Q D u μ orders hG top age x) live s) U
  have represented : (fun W=>(((T).leaf x).density W).part s)=
      fun W=>(R.family.path.rep N per (m+1)).eval W • word s W :=
    funext (stated R Q D u μ orders hG top age x s)
  rw [represented,←scalar] at held
  exact (get.map_smul _ _).trans (congrArg (fun z:ℂ=>((R.family.path.rep N per j).eval U)⁻¹ • z) held)

end YM.Integration.WilsonReportingPrescribedOldMicroscopic
