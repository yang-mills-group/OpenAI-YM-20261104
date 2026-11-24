import YM.Integration.WilsonSeparatedOriginalSlabCenteredMean
import YM.Integration.WilsonSeparatedOriginalSlabChildCentered
import YM.Integration.WilsonSeparatedOriginalSlabPosting

/-! One actual retained original Wilson history for every signed replica reading, with its complete old vacuum and three physical centers computed in the original clamped law. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabCubicPosting
open Function Finset Set Filter MeasureTheory Lattice Wilson RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.Many RG05Readout.View RG05Readout.Records RG05Readout.Flatten RG05Readout.Pulse
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi
open PhysicalNext PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station
open WilsonSeparatedOriginalSlabPosting WilsonReportHarvestSlabCubic WilsonSeparatedOriginalSlabChildSites Push.GridApprox
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){b m t per:ℕ}(nm:b+1 ≤ m)(mt:m ≤ t)(nt:b+1 < t)
variable (s:Fin 3 → ℕ)(S:(i:Fin 3) → Emblems R.family (s i))(P:(i:Fin 3) → Sight R.family (s i) per)(x:(i:Fin 3) → Palette R.family (s i))
local notation "C"=>R.family
local notation "n"=>b+1
local notation "topN"=>t+1
local notation "Sites"=>Site ((C).side (b+1) per)
local notation "fine"=>fun i:Fin 3=>Launch (m:=m) s S x i topN
local notation "A"=>R.family.S.oneStep b per
local notation "top"=>nt.le.trans t.le_succ

def retained (o:Fin 3 → Sites)(f:Fin 3 → Body){δ:ℝ}(e:WilsonReportHarvestSlabCenteredSample.Measured R nm mt nt s S P x o f δ)(a:Dates R b):ℂ:=
  let L:=Classical.choose e
  let hi:=(a.2.2.trans b.le_succ).trans top
  let v:=fun i:Fin 3=>-actualTransport C (N:=t+1) (Records.clinic C per topN (s i) (Many.point (S i) (x i) m topN) n (o i) (1,false) (f i)) hi 1
  pushTo (C).path topN per (a.2.2.trans b.le_succ) (fun W=>WilsonReportHarvestSlabCenteredPush.score v (baseFold o (fun _=>(1,false)) (Stock.census (Fin 3)) (L n W))) 1/liftVac (C).path topN per a.val 1

theorem billed (o:Fin 3 → Sites)(f:Fin 3 → Body){δ:ℝ}(e:WilsonReportHarvestSlabCenteredSample.Measured R nm mt nt s S P x o f δ)(a:Dates R b):
    ‖WilsonSeparatedOriginalReplicaScanner.sample R s fine o top ((Nat.succ_le_succ a.2.2).trans top) 1 (joint univ f)-
      retained R nm mt nt s S P x o f e a‖ ≤ δ:=by
  obtain ⟨_,_,_,_,_,_,h⟩:=Classical.choose_spec e
  rw [WilsonSeparatedOriginalSlabCenteredMean.original]
  exact h a.val a.2.1 a.2.2

def ticket (hb:(C).ref 0 ≤ b)(o:Fin 3 → Sites)(δ:ℝ)(f:Fin 3 → Body)(w:Sites → ℂ):Prop:=
  ∀c,∃e:WilsonReportHarvestSlabCenteredSample.Measured R nm mt nt s S P x (site A o c) f δ,
    w c=retained R nm mt nt s S P x (site A o c) f e ⟨b,hb,le_rfl⟩

def sensor (s:Fin 3→ℕ)(v:(i:Fin 3)→Palette R.family (s i))(o:Fin 3→Sites)(c:Sites):Wave (Fin 3) →ₗ[ℂ]ℂ:=
  WilsonSeparatedOriginalReplicaScanner.sample R s v (site A o c) top top 1

theorem original (hb:(C).ref 0 ≤ b)(o:Fin 3 → Sites)(f:Fin 3 → Body){δ:ℝ}
    (sold:∀c,WilsonReportHarvestSlabCenteredSample.Measured R nm mt nt s S P x (site A o c) f δ):
    ∃F:Sites→ℂ,WilsonSeparatedOriginalSlabWholeProfile.settled R (sensor R (per:=per) nt s fine) o
      (ticket R nm mt nt s S P x hb o δ) δ f F:=by
  let a:Dates R b:=⟨b,hb,le_rfl⟩
  exact ⟨fun c=>retained R nm mt nt s S P x (site A o c) f (sold c) a,
    fun c=>⟨sold c,rfl⟩,fun c=>billed R nm mt nt s S P x (site A o c) f (sold c) a⟩

end YM.Integration.WilsonSeparatedOriginalSlabCubicPosting
