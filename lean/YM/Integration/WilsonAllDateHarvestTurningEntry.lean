import YM.Integration.WilsonAllDateHarvestTuningModes
import YM.Integration.WilsonMarkedUltravioletReportingEntries

/-! The full dated regular and forced activities use the separation radius
chosen for the lower measured interval, before any occupied support is read. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonAllDateHarvestTurningEntry

open Finset Filter Lattice Wilson RG Marker Push GridApprox.Nil MergeProof Accent
open Extra.Histories RG05Readout.Many PhysicalNext.Repeat.Legato
open private spend from YM.Integration.WilsonMarkedUltravioletReportingEntries
open scoped BigOperators Classical
variable {G:Gauge} (R:Run G)

theorem original {n m N per D d k h:ℕ} (nm:n ≤ m) (mN:m ≤ N)
    (o:Fin 3 → Site (R.family.side n per)) (E:Fin 3 → Motion) (roster:Census (Fin 3))
    {Q:ℝ} (qp:0 < Q) (ceiling:Q ≤ (R.family.path.levels.clock.hatBeta m)^h)
    (room:D*(4*(R.family.path.levels.budget m).B+2)+2*(R.family.path.levels.budget m).B ≤
      (R.family.path.levels.budget m).B^2) :
    let C:=R.family
    let J:=Mine.masts o E nm (barren o E roster m) m
    let P:=C.path.rep N per m
    let places:=(Mine.tree o E).supportX m
    let α:=(C.path.levels.budget m).supportExponent
    let M:=(C.path.levels.clock.hatBeta m)^((k+h)*3)
    ∀ (rows:ManyStem C o m → RG05Readout.Address.Three G (C.side m per))
      (Z:Config G (C.side m per) → Poly J),
      MenuBoard P rows Z places (fun _=>envelope C m d k Q m) α 1 →
      ∃H K, Carton places H K P.p.threshold ∧
        Z=restore P (fun v=>(rows v).2.1) (fun v=>profile P.activities (rows v).2.2) H K ∧
        Towed (fun _:ManyStem C o m=>(1:ℝ)) id H P.p.B (α-1) (M*Real.exp (-(D:ℝ))) ∧
        Towed (fun _:ManyStem C o m=>(1:ℝ)) (fun b:Box (C.side m per)=>b.1)
          K P.p.B (α-1) (M*Real.exp (-(D:ℝ))) := by
  intro C J P places α M rows Z board
  let w:=fun _:ManyStem C o m=>envelope C m d k Q m
  have mp:0 ≤ M:=pow_nonneg (zero_lt_one.trans (C.path.levels.fits.delayed m)).le _
  have wp (v:ManyStem C o m):0 < w v:=mul_pos (rust_paid _).1 (grantw (totalpos qp m))
  have sizes (s:J.Mode):1 ≤ M*Poly.toll w s:=by
    apply WilsonMarkedUltravioletReportingReserve.weights C m d k h 3 (fun _:ManyStem C o m=>Q)
      (fun _=>qp) (fun _=>ceiling) s
    simpa only [Fintype.card_fin] using WilsonAllDateHarvestTuningModes.cardinal o E roster nm le_rfl s
  have same:P.p=C.path.levels.budget m:=(R.T.choice.represents N per m mN).vac
  have apart (s:J.Mode) (two:2 ≤ s.val.card):
      ∃ a ∈ s.val, ∃ b ∈ s.val,D*(4*P.p.B+2)+2*P.p.B < separation (places a) (places b) := by
    obtain ⟨a,ha,b,hb,_,_,distant⟩:=WilsonAllDateHarvestTuningModes.pair o E roster nm s two
    refine ⟨a,ha,b,hb,?_⟩
    rw [same]
    exact lt_of_le_of_lt room (Nat.lt_of_succ_le distant)
  obtain ⟨H,K,legal,regular,forced,field⟩:=board.grants
  exact ⟨H,K,legal,field,
    spend regular wp mp le_rfl sizes (fun i=>(legal.exp i).1.toBorne) (fun i=>(legal.exp i).2) apart,
    spend forced wp mp le_rfl sizes (fun i=>(legal.flag i).1.toBorne) (fun i=>(legal.flag i).2) apart⟩

end YM.Integration.WilsonAllDateHarvestTurningEntry
