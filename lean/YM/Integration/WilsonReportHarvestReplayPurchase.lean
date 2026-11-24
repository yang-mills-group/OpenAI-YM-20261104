import YM.Integration.WilsonReportHarvestReplayEntries

/-! Price both complete signed ledgers on the actual original ward
from a direct spatial room invoice, independently of which date paid it. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportHarvestReplayPurchase
open Finset Function Filter Lattice Wilson RG Marker Push AbsoluteSums
open Extra.Histories Ac MergeProof MergeProof.Accent GridApprox.Nil RG05Readout.Many
open PhysicalNext.Repeat.Legato
open private spend from YM.Integration.WilsonMarkedUltravioletReportingEntries
open scoped Classical
variable {G:Gauge}(R:Run G){b m i N per:ℕ}(bm:b ≤ m)(mi:m ≤ i)(live:i ≤ N)
variable (o:Fin 3→Site (R.family.side b per))(E:Fin 3→Motion)(roster:Census (Fin 3))
set_option quotPrecheck false
local notation "A" => R.family.path.levels
local notation "J" => Mine.masts o E bm (barren o E roster m) i
local notation "P" => R.family.path.rep N per i
local notation "positions" => (Mine.tree o E).supportX i
local notation "α" => ((A).budget i).supportExponent

include live in
theorem purchased (rows:ManyStem R.family o i→RG05Readout.Address.Three G (R.family.side i per))
    (Z:Config G (R.family.side i per)→Poly J)(w:ManyStem R.family o i→ℝ)
    (wp:∀v,0<w v)(board:MenuBoard P rows Z positions w α 1)(D:ℕ){M δ:ℝ}
    (mp:0 ≤ M)(fee:M*Real.exp (-(D:ℝ)) ≤ δ)(wallet:∀s:(J).Mode,1 ≤ M*Poly.toll w s)
    (housing:D*(4*((A).budget i).B+2)+2*((A).budget i).B ≤
      (R.family.S.toDepth mi per).count.val*((A).budget m).B^2):
    ∃H K,Carton positions H K (P).p.threshold ∧
      Z=restore P (fun v=>(rows v).2.1) (fun v=>profile (P).activities (rows v).2.2) H K ∧
      Towed (fun _:ManyStem R.family o i=>(1:ℝ)) id H (P).p.B (α-1) δ ∧
      Towed (fun _:ManyStem R.family o i=>(1:ℝ)) (fun v:Box (R.family.side i per)=>v.1) K (P).p.B (α-1) δ := by
  have same:(P).p=(A).budget i:=(R.T.choice.represents N per i live).vac
  have apart (s:(J).Mode)(two:2 ≤ s.val.card):
      ∃a∈s.val,∃b∈s.val,D*(4*(P).p.B+2)+2*(P).p.B < separation (positions a) (positions b):=by
    obtain ⟨a,ha,b,hb,separated⟩:=WilsonReportHarvestResidentScale.pair o E roster bm mi s two
    exact ⟨a,ha,b,hb,by rw [same];exact housing.trans_lt separated⟩
  obtain ⟨H,K,layout,regular,forced,all⟩:=board.grants
  refine ⟨H,K,layout,all,?_,?_⟩
  · exact spend regular wp mp fee wallet (fun i=>(layout.exp i).1.toBorne) (fun i=>(layout.exp i).2) apart
  · exact spend forced wp mp fee wallet (fun i=>(layout.flag i).1.toBorne) (fun i=>(layout.flag i).2) apart

end YM.Integration.WilsonReportHarvestReplayPurchase
