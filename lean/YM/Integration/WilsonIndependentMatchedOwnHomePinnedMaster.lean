import YM.Integration.WilsonIndependentMatchedOwnHomeMeasuredRoster
import YM.Integration.WilsonIndependentSpoutMasterReport

/-! Linear measurement in the actual public input held fixed before either
cut. The original pinned field, the old vacuum and the reported clock are
kept on every term of the complete finite basis. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentMatchedOwnHomePinnedMaster
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer.Patrol
open WilsonMarkedIndependentNormalizedElection (normalized)
open WilsonIndependentSpoutMasterArms (arm basis)
open WilsonIndependentSpoutMasterCoordinates (axis)
open WilsonIndependentMatchedOpeningPayment (affiled)
open WilsonIndependentSpoutScalarLedger (ground)
open WilsonOlderFreshSoftCoverScalar (clock)
open WilsonIndependentSpoutMasterReport (report)
open WilsonPositionProgramPinnedHearthHistory (pin)
open WilsonSeparatedPrefixMovingPinHearing (hear shiftHom)
open scoped BigOperators Classical
variable {G:Gauge}{H:Hol G}{n e:ℕ}{E W V:Credit}

theorem translate (q:Cost)(P:Era G ℝ)(s:Cover):
    shiftHom s (affiled q P)=affiled q (shiftHom s P):=by
  refine Prod.ext ?_ ?_
  · funext n l r z
    simp [shiftHom,shifted,affiled,skewV,revolve,affix,Finset.sum_apply]
  · funext l r z
    simp [shiftHom,shifted,affiled,skewV,revolve,affix,Finset.sum_apply]

variable (R:Realm G (e+1) E)(Q:Fin (n+1)→SealR G)(φ:Wilt Q)(b:Herit Q)
local notation "A₀" => R.draws
local notation "O₀" => R.paid

def point (m c older K N:ℕ)(y:ℝ)(o:CellR)(s:Cover):Cost:=
  ground (hear R (capP Q) N c older s K (Ashore Q A₀ O₀ φ (normalized A₀ O₀ Q b m N) m K N y o))

theorem paid (fund:HorizonP H R W V Q)(m c older K N:ℕ)(live:R.anchor ≤ K)(early:older ≤ m)(prior:m ≤ K)(top:K ≤ N)
    (y:ℝ)(o:CellR)(s:Cover):
    point R Q φ b m c older K N y o s=
      ∑a:(∀i,Alma (Q i).F),clock A₀ O₀ N m older (∏i,b i (a i))*point R Q φ (WilsonIndependentSpoutMasterArms.basis Q a) m c older K N y o s:=by
  have lic (i:Fin (n+1))(a:Alma (Q i).F):Auth (Q i).h (arm A₀ O₀ (Q i) (φ i) (axis (Q i) a) m K N y o):=by
    let P:PassportC H R (Q i) W V:=(fund i).some
    rw [←P.lands,←P.modes]
    exact WilsonIndependentSpoutMasterArms.licensed _ P.f.arch _ _ m K N (P.tap.symm ▸ live) top y o
  let k:=capP Q
  let relClock:=reel (relativeC A₀ O₀ N m (K-m))
  let site:=pin R.draws.S c K s
  let raw (a:∀i,Alma (Q i).F):=Ashore Q A₀ O₀ φ (normalized A₀ O₀ Q (WilsonIndependentSpoutMasterArms.basis Q a) m N) m K N y o
  let row a:=shiftHom site (raw a)
  let wallet (a:∀i,Alma (Q i).F):=∏i,b i (a i)
  let full a:=affiled (relClock (wallet a)) (row a)
  have authentic a:Auth k (row a):=(manCo _ (fun i=>(Q i).h) (fun i=>lic i (a i))).shifted _
  have submitted a:Auth k (full a):=WilsonIndependentMatchedOpeningFee.grant _ (authentic a) _
  unfold point hear
  rw [WilsonIndependentSpoutMasterArms.original A₀ O₀ Q φ b m K N y o lic]
  simp only [map_sum,translate]
  change ground (cruises A₀ O₀ N k K older (∑a,full a))=_
  rw [WilsonIndependentSpoutDoseBoundary.checkedSum A₀ O₀ R.hG R.green N K older k (early.trans prior) top full submitted,
    WilsonIndependentSpoutMasterReport.collected]
  apply Finset.sum_congr rfl;intro a _
  change ground (cruises A₀ O₀ N k K older (full a))=clock A₀ O₀ N m older (wallet a)*ground (cruises A₀ O₀ N k K older (row a))
  have sent:=WilsonOlderFreshSoftSocketHistory.original A₀ O₀ R.hG R.green N k K older (early.trans prior) top
    (full a) (row a) (relClock (wallet a)) (submitted a) (authentic a) (fun _=>rfl)
  unfold ground
  rw [sent,WilsonOlderFreshSoftSocketKinetic.valued,←WilsonOlderFreshSoftSocketKinetic.combine A₀ O₀ N K m older early prior]
  have follows:=WilsonIndependentFittedRelativeClock.restored A₀ O₀ R.hG R.green N m (K-m) (by omega) (wallet a)
  simpa only [show m+(K-m)=K by omega,relClock] using congrArg (fun v=>clock A₀ O₀ N m older v*
    WilsonOlderFreshSoftSocketKinetic.reading (cruises A₀ O₀ N k K older (row a)).2 Fin.elim0) follows

theorem original (fund:HorizonP H R W V Q)(m c older K N:ℕ)(live:R.anchor ≤ K)(early:older ≤ m)(prior:m ≤ K)(top:K ≤ N)
    (y:ℝ)(o:CellR)(s:Cover):
    report A₀ O₀ N m older (point R Q φ b m c older K N y o s)=
      ∑a:(∀i,Alma (Q i).F),(∏i,b i (a i))*report A₀ O₀ N m older (point R Q φ (WilsonIndependentSpoutMasterArms.basis Q a) m c older K N y o s):=by
  rw [paid R Q φ b fund m c older K N live early prior top y o s]
  simp only [report,map_sum,map_mul]
  exact Finset.sum_congr rfl fun a _=>congrArg (·*_) (WilsonIndependentSpoutMasterReport.cancellation A₀ O₀ R.hG R.green m N older early (prior.trans top) _)
end YM.Integration.WilsonIndependentMatchedOwnHomePinnedMaster
end

