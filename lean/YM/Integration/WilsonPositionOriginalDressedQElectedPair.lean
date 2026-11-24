import YM.Integration.WilsonPositionOriginalDressedQCohortSource
import YM.Integration.WilsonPositionOriginalDressedQPayout

/-! All four corners of the two-name endpoint on its literal, original
funded Q program, with the one elected lower prior on all faces. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDressedQElectedPair
open Set Function Filter MeasureTheory Lattice Wilson RG Marker Cells QuadraticLocal
open Source Labels FVA1 LocalComparison ComparisonDensity.Address
open PhysicalNext.Repeat.Legato MergeProof MergeProof.Accent MergeProof.Replicums
open RG3.Held RG3.Script.Picnic OriginalForcedAddresses ActualOriginalQReaders
open WilsonMacroscopicForwardTransfer WilsonPositionOriginalDressedQCohortSource
open scoped Topology Classical BigOperators
variable {G:Gauge}(R:Run G){B:MS.Local.Physical.Deck G}{p i n:ℕ}{hn:n ≤ i+1}{V:Type}
  [DecidableEq V][Fintype V][Nonempty V](Q:MS.Land.Prescription B)
  (D:ActualRunQlocalNativeTuple.Datum R p (i+1) n hn V)(u:V→MS.Rake.Label B)(μ:ℝ)(orders:V→ℕ)
  {T I:Type}(test:T → TestSpace (ActualRunQlocalNativeTuple.orbit D))(simple:G.Simple){N:ℕ}(live:i<N)
local notation "Γ" => (Stock.census V)
local notation "Ψ" => (R.family.path.rep N p i)
local notation "S" => (R.family.path.levels.clock.op i p)

def table (t:T)(U:Config G (R.family.side i p)):Poly Γ:=
  (S).push (R.family.path.rep N p (i+1)).beta
    ((ActualOriginalQInput.input Q D u μ orders simple N live).leaf (test t)).density U
local notation "Y" => (table R Q D u μ orders test simple live)
local notation "q" => (fun t=>letter R Q D u μ orders (test t))
variable {o:V→Site (R.family.side i p)}{P:Rep G (R.family.side i p)}
  {w:V→ℝ}{k r reg hard:ℝ}(L:QuadraticLocal.Lamps T I G P.p o (Stock.census V))
local notation "ℒ" => (WilsonRootedKioskOccupiedSlip.bare L)

theorem original (href:∀s:Slot u,R.family.ref s.2.size ≤ i+1)
    (coarse:P.eval=(Ψ).eval)
    (Z:WilsonRootedKioskSealedPost.Return P o Γ w k r reg hard ℒ Y)
    (a b:V)(apart:a≠b)(s:(Γ).Mode)(roots:s.val={a,b})(t:T)(W:Config G (R.family.side i p)):
    (Z.output.density t W).part s+(P.eval W:ℂ)*((ℒ) t W).part s=
    (P.eval W:ℂ)*(exterior (C:=R.family) (N:=N) (Nat.le_succ i)
        (fun U=>(q) t a U*(q) t b U) W-
      exterior (C:=R.family) (N:=N) (Nat.le_succ i) ((q) t a) W*((ℒ) t W).part ((Γ).fire b)-
      exterior (C:=R.family) (N:=N) (Nat.le_succ i) ((q) t b) W*((ℒ) t W).part ((Γ).fire a)+
      ((ℒ) t W).part ((Γ).fire a)*((ℒ) t W).part ((Γ).fire b)):=by
  rw [←WilsonPositionOriginalDressedQPayout.original L Y Z a b apart s roots t W]
  have returns:=WilsonPositionOriginalDressedQCohortSource.original R Q D u μ orders (test t) simple live href W
  change ∀v:(Γ).Mode,(Y t W).part v=_ at returns
  rw [returns s,returns ((Γ).fire a),returns ((Γ).fire b),←coarse]
  simp [roots,Census.fire,apart]
  ring

end YM.Integration.WilsonPositionOriginalDressedQElectedPair
