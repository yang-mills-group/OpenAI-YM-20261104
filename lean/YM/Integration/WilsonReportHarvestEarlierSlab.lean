import YM.Integration.WilsonAllDateHarvestHistoricalEntry
import YM.Integration.ActualTrajectoryTransport

/-! Put the complete field at the higher reporting date into one genuine
lower Wilson conditional. The original licensed marker maps and cell
weights are included before any connected logarithm is taken. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReportHarvestEarlierSlab
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Labels Source Extra.Histories
open Push Local MergeProof Accent Menu Marker RG05Readout RG05Readout.Address RG05Readout.Native
open RG05Readout.Many RG05Readout.View Bid Pressure Copper Ac GridApprox.Nil
open Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage
open scoped Classical BigOperators
variable {G:Gauge}{C:Family G}{per n b t j N:ℕ}{V:ℕ→Type}[∀i,DecidableEq (V i)]
    {W:Type*}{A:Planner C per n V W}{H:∀i,Census (V i)}{s:W→ℕ}
    {F:∀i,Config G (C.side i per)→Poly (H i)}{nb:n ≤ b}
    (row:Replay A s nb t F N)

private def one (i:ℕ)(bi:b ≤ i)(it:i<t):Poly (H (i+1))→ₐ[ℂ]Poly (H i):=
  feed (fun x=>budwgt C per i (s (A.labelY i ((A.narrows i (nb.trans bi)) x).1)))
    (row.downhill i bi it).choose

/-- The actual composite marker transfer. Each factor sends its resident
to the true parent with the required weight for that resident's grade. -/
def route (j:ℕ)(bj:b ≤ j)(jt:j ≤ t):Poly (H t)→ₐ[ℂ]Poly (H j):=
  Nat.decreasingInduction (motive:=fun i _=>b ≤ i→Poly (H t)→ₐ[ℂ]Poly (H i))
    (fun i it go bi=>(one row i bi it).comp (go (bi.trans i.le_succ)))
    (fun _=>AlgHom.id ℂ (Poly (H t))) jt bj

private theorem base (bt:b ≤ t):route row t bt le_rfl=AlgHom.id ℂ (Poly (H t)):=by
  unfold route;rw [Nat.decreasingInduction_self]

private theorem earlier (bj:b ≤ j)(jt:j<t):
    route row j bj jt.le=(one row j bj jt).comp (route row (j+1) (bj.trans j.le_succ) jt):=by
  unfold route;rw [Nat.decreasingInduction_succ_left]

private theorem passed {I J:Type}[DecidableEq I][DecidableEq J]{P:Census I}{Q:Census J}
    (g:Config G (C.side t per)→Poly P)(live:Integrable g (prior G _))(S:Poly P→ₗ[ℂ]Poly Q)(jt:j ≤ t):
    gust C.path N per t (fun W=>S (g W)) j jt=fun U=>S (gust C.path N per t g j jt U):=by
  induction jt using Nat.decreasingInduction with
  | self => simp only [gust_base]
  | of_succ i it ih =>
    rw [gust_step C.path N per t _ it,ih]
    simp only [gust_step C.path N per t g it]
    exact amp_live S _ (gust_live C.path N per t g live it)
      (C.path.levels.transition_mass i per (C.path.β N per (i+1)))

theorem issued (live:Integrable (F t) (prior G _))(bj:b ≤ j)(jt:j ≤ t):
    F j=fun U=>route row j bj jt (gust C.path N per t (F t) j jt U):=by
  induction jt using Nat.decreasingInduction with
  | self=>rw [base];simp only [gust_base,AlgHom.coe_id,id_eq]
  | of_succ i it ih=>
    let ticket:=row.downhill i bj it
    let y:=C.path.levels.clock.op i per
    let β:=C.path.β N per (i+1)
    let step:=one row i bj it
    let rest:=route row (i+1) (bj.trans i.le_succ) it
    let f:=gust C.path N per t (F t) (i+1) it
    have top:F (i+1)=(fun W=>rest (f W)):=ih (bj.trans i.le_succ)
    have signed:=amp_live rest.toLinearMap y (gust_live C.path N per t (F t) live it)
      (C.path.levels.transition_mass i per β)
    rw [earlier row bj it,gust_step C.path N per t (F t) it]
    calc F i = (fun U=>step (y.push β (F (i+1)) U)):=ticket.choose_spec
         _ = (fun U=>step (y.push β (fun W=>rest (f W)) U)):=
          congrArg (fun φ:Config G (C.side (i+1) per)→Poly (H (i+1))=>fun U=>step (y.push β φ U)) top
         _ = _:=congrArg (fun φ:Config G (C.side i per)→Poly (H (i+1))=>fun U=>step (φ U)) signed

theorem normalized (made:C.Makes)(bt:t ≤ N)(live:Integrable (F t) (prior G _))
    (bj:b ≤ j)(jt:j ≤ t)(U:Config G (C.side j per)):
    ((C.path.rep N per j).eval U)⁻¹ • F j U =
      actualTransport C (N:=N) (fun W=>((C.path.rep N per t).eval W)⁻¹ •
        route row j bj jt (F t W)) jt U:=by
  let move:=route row j bj jt
  have cancel (W:Config G (C.side t per)):(C.path.rep N per t).eval W •
      (((C.path.rep N per t).eval W)⁻¹ • move (F t W))=move (F t W):=by
    rw [smul_smul,mul_inv_cancel₀ (Multi.AxisShift.chosen_positive made.wilson bt W).ne',one_smul]
  unfold actualTransport
  simp_rw [show ∀W:Config G (C.side t per),(C.path.rep N per t).eval W •
    (((C.path.rep N per t).eval W)⁻¹ • route row j bj jt (F t W))=move (F t W) from cancel]
  rw [issued row live bj jt]
  exact congrArg (((C.path.rep N per j).eval U)⁻¹ • ·)
    (congrFun (passed (N:=N) (F t) live move.toLinearMap jt) U).symm

end YM.Integration.WilsonReportHarvestEarlierSlab
