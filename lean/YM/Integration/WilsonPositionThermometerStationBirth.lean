import YM.Integration.WilsonPositionThermometerStationUnit
import YM.Integration.ActualRunFullPages

/-! The three original thermometer insertions have one common top. In the
genuine, full regular and forced pages the intake vector is the actual
inverse-normalized top coordinate on that very trajectory. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionThermometerStationBirth
open Function Set Filter Finset MeasureTheory Lattice Wilson RG Source Extraction Table Spec Marker FVA1
open Climb Trace.Pilot Next.UVStress Next.Rank RG12 RG17 PhysMS PhysicalNext.Repeat.Legato
open MergeProof MergeProof.East MergeProof.Accent MergeProof.Replicums MergeProof.Ribbon
open Push.GridApprox.Nil OriginalForcedAddresses ActualRunUnmaskedPartners XSpace XSpace.Rose
open scoped Topology Classical BigOperators
variable {G : Gauge} (R : Run G) (N p : ℕ) (d : ℕ)

/-- This is the very top Wilson source before a thermal or chart change. -/
theorem kernel (ref : R.family.ref d ≤ N) (w : R.family.book.Ref d) (x : Site (R.family.side N p)) :
    ActualRunPhysicalPages.kernel R N p N d (Price.awake R.family d N N p w) x = R.family.O N p w x := by
  let T := R.family.factory d N p
  have bare : Price.columns R.family d N N p w = T.terminal.symm w :=
    (R.makes.calibrated d N p ref).bare_coord _
  have hn : (R.family.S.a N : ℂ)^d ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (R.family.S.a_pos _).ne')
  rw [ActualRunPhysicalPages.kernel_physical R N p N d le_rfl, Price.awake, bare]
  change _ • R.family.O N p (T.terminal (_ • T.terminal.symm w)) x = _
  rw [map_smul, LinearEquiv.apply_symm_apply]
  rw [(R.family.linearO N p d x).map_smul,smul_smul,mul_inv_cancel₀ hn,one_smul]

variable {I : Type} [DecidableEq I] [Fintype I] {D : ℕ} (V : Vane R.family D) (j : Fin (D+1)) (v : I → (Bel R.family.book).Field j)

def payload (i : I) : R.family.label j := Price.awake R.family j N N p (V.wheel.atCut (N,p) j (v i))

set_option pp.explicit true in
private theorem marked_log (ref : R.family.ref j ≤ N)
    (o : Positions I (R.family.side N p)) (U : Config G (R.family.side N p)) :
    actualLog R N p N o (fun _ : I => j.val) (payload R N p V j v) U =
    Mach (Replicum.Bud I) (fun i => R.family.O N p (V.wheel.atCut (N,p) j (v i)) (o.origin i) U) := by
  simp only [actualLog,payload,kernel R N p j ref]

theorem original (simple : G.Simple) (ref : R.family.ref j ≤ N)
    (o : Positions I (R.family.side N p)) (U : Config G (R.family.side N p)) :
    essence (ActualRunFullPages.pages R simple N p N le_rfl o (fun _ => j)
      (payload R N p V j v)) (fun _=>0) (fun _=>1) U =
    ((R.family.path.rep N p N).eval U : ℂ) • Poly.pass (Mach (Replicum.Bud I) (fun i =>
      R.family.O N p (V.wheel.atCut (N,p) j (v i)) (o.origin i) U)) := by
  calc
    _ = fullInput R N p N o (fun _ => j.val) (payload R N p V j v) U :=
      ActualRunFullPages.essence_full R simple N p N le_rfl o (fun _ => j.val)
        (payload R N p V j v) (fun _ => ref) U
    _ = _ := congrArg (fun a : Poly (Replicum.Bud I) => ((R.family.path.rep N p N).eval U : ℂ) • Poly.pass a)
      (marked_log R N p V j v ref o U)

end YM.Integration.WilsonPositionThermometerStationBirth
end
