import YM.Integration.WilsonPositionOriginalDressedQCohortFibre

/-! Every face of the original, simultaneously issued Q cohort, at every
fixed outgoing coarse field. All subwords keep the same Wilson denominator. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDressedQCohortSource
open Function Finset Filter Set MeasureTheory Lattice Wilson RG Marker Cells OPE.Therm
open Source Labels FVA1 LocalComparison ComparisonDensity.Address RG3.Held RG3.Script.Picnic OriginalForcedAddresses
open MergeProof MergeProof.Accent MergeProof.Replicums PhysicalNext.Repeat.Legato
open QLocalPhysicalPathKernel WilsonMacroscopicForwardTransfer
open ActualOriginalQReaders
open scoped Topology Classical BigOperators
variable {G:Gauge}(R:Run G){B:MS.Local.Physical.Deck G}{p i n:ℕ}{hn:n ≤ i+1}{V:Type}
  [DecidableEq V][Fintype V][Nonempty V](Q:MS.Land.Prescription B)
  (D:ActualRunQlocalNativeTuple.Datum R p (i+1) n hn V)(u:V→MS.Rake.Label B)(μ:ℝ)(orders:V→ℕ)
  (x:TestSpace (ActualRunQlocalNativeTuple.orbit D))
local notation "fine" => (Config G (R.family.side (i+1) p))
local notation "Γ" => (Stock.census V)
def letter (v:V) (U:fine):ℂ:=ActualRunQlocalNativeTuple.reader D v (x v)*
  ActualOriginalCalibratedColumns.weightedObservable R B Q (u v) μ
        (R.family.side (i+1) p) (ActualRunQlocalNativeTuple.root D v) U (orders v)
local notation "A" => (letter R Q D u μ orders x)
local notation "F" => (fun U:fine=>Poly.pass (Mach Γ (fun v=>(A) v U)))

omit [DecidableEq V] [Fintype V] [Nonempty V] in
theorem continuous_letter (v:V):Continuous ((A) v):=by
  apply continuous_const.mul
  simp_rw [ActualOriginalCalibratedColumns.weighted_observable_original]
  apply continuous_finsetSum;intro e _
  exact continuous_const.mul ((R.family.localSection e.size).continuous_places _ _)

omit [Nonempty V] in
theorem continuous_source:Continuous (F):=by
  change Continuous (fun U:fine=>(Poly.pass (Mach Γ fun v=>(A) v U)).part)
  apply continuous_pi;intro s
  simp only [Mach,Extra.Trajectories.pass_fire]
  exact continuous_finsetProd _ fun v _=>continuous_letter R Q D u μ orders x v

theorem original (simple:G.Simple){N:ℕ}(live:i<N)
    (href:∀s:Slot u,R.family.ref s.2.size ≤ i+1)
    (W:Config G (R.family.side i p))(s:(Γ).Mode):
    ((R.family.path.levels.clock.op i p).push (R.family.path.rep N p (i+1)).beta
      ((ActualOriginalQInput.input Q D u μ orders simple N live).leaf x).density W).part s =
    ((R.family.path.rep N p i).eval W:ℂ)*
        exterior (C:=R.family) (N:=N) (Nat.le_succ i) (fun U=>∏v∈s.val,(A) v U) W :=by
  classical
  have filed:((ActualOriginalQInput.input Q D u μ orders simple N live).leaf x).density=
      fun U=>(R.family.path.rep N p (i+1)).eval U • (F) U:=by
    funext U
    rw [ActualOriginalQInput.density_packet_factor Q D u μ orders simple N live href x U,
        ActualOriginalQPackets.source_factor Q D u μ orders N live]
    exact_mod_cast rfl
  rw [filed]
  letI:=isMarkov R.family (p:=p) R.makes live
  letI:IsProbabilityMeasure (next R.family N p i W):=inferInstance
  have safe:Integrable (F) (next R.family N p i W):=
    (continuous_source R Q D u μ orders x).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [WilsonPositionOriginalDressedQCohortFibre.coefficient R live (F) s W safe]
  simp only [Mach,Extra.Trajectories.pass_fire]

end YM.Integration.WilsonPositionOriginalDressedQCohortSource
