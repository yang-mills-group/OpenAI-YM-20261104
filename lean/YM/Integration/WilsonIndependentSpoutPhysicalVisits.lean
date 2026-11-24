import YM.Integration.WilsonIndependentSpoutPhysicalOrbit
import YM.Integration.WilsonIndependentSpoutVisitRoster

/-! Price every finite signed mixture of the real physical board readings on one preselected course. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
namespace YM.Integration.WilsonIndependentSpoutPhysicalVisits
open Lattice RG Tree Wilson Source Labels PertExtension XSpace XSpace.Rose XSpace.Cirrus Precision
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Next.Foundations
open RegulatorIR RegulatorIR.Oracle RegulatorIR.Ledger RegulatorIR.Uniform RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Kick
open RegulatorIR.Atlas RegulatorIR.Calibration RegulatorIR.Taping RegulatorIR.Budget RegulatorIR.Budget.Layer
open RegulatorIR.Epoch RegulatorIR.Prim RegulatorIR.Geometry RegulatorIR.Gain RegulatorIR.Halo RegulatorIR.Momentum RegulatorIR.Ledger.Sky
open RegulatorIR.Profiles RegulatorIR.Budget.Packet RegulatorIR.Cluster RegulatorIR.Binding
open RegulatorIR.Clocks
open WilsonIndependentRawRosterWord WilsonIndependentRawWordGeometry
open WilsonOriginalPublicNodalPhysicalMerBook (Issued)
open WilsonOriginalPublicNodalEnrolledMerStop (aged series)
open scoped Classical ENNReal NNReal

open WilsonIndependentSpoutPhysicalOrbit (raw returned amount)
open scoped BigOperators
variable {G:Gauge}{X I T:Type}[Fintype T](R:Run G)(W:Initialize G)(V:XSpace.Run)
    (m j:X → ℕ)(w:X → ℕ → ℕ)(blocks:∀x k,(R.family.S.block (m x+k)).val=V.ratio^(w x k))
    (Z:∀p:Patch,p.Branches R.family.path.levels.clock.kernel G){p:ℕ}{F:Tent j}(issued:Issued R V m j w blocks Z p F)
    (σ:T → I → Bool)(d:I → ℕ)(key:(t:T) → (i:I) → (R.family.labels.level (d i)).Index){E:I → ℕ}(cut:∀i,d i<E i)
    (arms:Composite I){Cells:X → Type}[∀v,Fintype (Cells v)][∀v,Nonempty (Cells v)]
    (sites:(v:X) → Cells v → I → Cover)(sample:X → Sample 2)
    (x:(v:X) → Cells v → Room)(ip:X → ℕ)(H c₀:ℝ)
local notation "C" => WilsonPositionProgramInfraredCircuit.circuit R V m j w blocks
local notation "Y" => Oracle.books R.family.path.levels.clock.kernel
local notation "S" => (C).dialect Y G Z (sheet F)

def price (q:ℕ)(stop:Choice j)(tail:X → ℝ)(k:ℕ)(H₀:ℝ):Prop:=
  ∀(v:X)(L:Type)[Fintype L](b:L → Cells v)(t:L → T)(fee:L → PowerSeries ℂ),
    ‖PowerSeries.coeff q (∑l,fee l*raw R W (σ (t l)) d (key (t l)) arms (fun _=>sites v (b l)) sample v)-
      PowerSeries.coeff q (∑l,fee l*returned R W m j (σ (t l)) d (key (t l)) cut arms (fun _=>sites v (b l)) stop v)‖≤
      (∑z:L × Fin (q+1),‖PowerSeries.coeff z.2.val (fee z.1)‖) *
        (H₀*(amount R V m j w ip H v)^k*tail v)

private theorem collect (q:ℕ)(stop:Choice j)(tail:X → ℝ)(positive:∀v,0≤tail v)
    (given:∀(t:T)(pick:∀v,Cells v)(e:Fin (q+1)),∃H₀:ℝ,∃k:ℕ,0≤H₀ ∧ ∀v:X,
      ‖PowerSeries.coeff (q-e.val) (raw R W (σ t) d (key t) arms (fun v=>sites v (pick v)) sample v)-
        PowerSeries.coeff (q-e.val) (returned R W m j (σ t) d (key t) cut arms (fun v=>sites v (pick v)) stop v)‖≤
          H₀*(amount R V m j w ip H v)^k*tail v):
    ∃k:ℕ,∃H₀:ℝ,0≤H₀ ∧ price R W V m j w σ d key cut arms sites sample ip H q stop tail k H₀:=by
  let U (v:X)(c:Cells v)(t:T × Fin (q+1)):=PowerSeries.coeff (q-t.2.val)
    (raw R W (σ t.1) d (key t.1) arms (fun _=>sites v c) sample v)
  let V₀ (v:X)(c:Cells v)(t:T × Fin (q+1)):=PowerSeries.coeff (q-t.2.val)
    (returned R W m j (σ t.1) d (key t.1) cut arms (fun _=>sites v c) stop v)
  have each(t:T × Fin (q+1))(pick:∀v,Cells v):∃k:ℕ,∃H₀:ℝ,0≤H₀ ∧ ∀v,
    ‖U v (pick v) t-V₀ v (pick v) t‖≤H₀*(amount R V m j w ip H v)^k*tail v:=by
    obtain ⟨H₀,k,nn,bill⟩:=given t.1 pick t.2
    exact ⟨k,H₀,nn,bill⟩
  obtain ⟨k,H₀,nn,paid⟩:=WilsonIndependentSpoutVisitWallet.original (amount R V m j w ip H) tail
    (WilsonPositionProgramInfraredMeter.lower R V m j w ip H) positive U V₀ each
  refine ⟨k,H₀,nn,?_⟩
  intro v L _ b t fee
  rw [WilsonIndependentSpoutVisitRoster.convolution,WilsonIndependentSpoutVisitRoster.convolution]
  exact WilsonIndependentSpoutVisitWallet.applied _ (fun z:L × Fin (q+1)=>U v (b z.1) (t z.1,z.2))
    (fun z=>V₀ v (b z.1) (t z.1,z.2)) (fun z=>paid v _ _) (fun z=>PowerSeries.coeff z.2.val (fee z.1))

variable (simple:G.Simple)(same:∀v,TopF (WilsonPositionProgramInfraredCircuit.count V j w) v=(sample v).F.p.side)
    (fare:∀v c,1+WilsonIndependentRawRosterBudget.span (x v c) (sites v c) arms ≤ amount R V m j w ip H v)
    (clear:0<c₀)(safe:∀pick:∀v,Cells v,((WilsonPositionProgramInfraredCircuit.circuit R V m j w blocks).dialect
      (Oracle.books R.family.path.levels.clock.kernel) G Z (sheet F)).cushion c₀ (fun v=>x v (pick v)))
include issued simple same fare clear safe
theorem stopped (q:ℕ)(hq:q≤p)(stop:Choice j):
    ∃k:ℕ,∃H₀:ℝ,0≤H₀ ∧ price R W V m j w σ d key cut arms sites sample ip H q stop
      (fun v=>(S).modifyErr 0 1 (1/2) stop v) k H₀:=by
  apply collect
  · intro v
    apply add_nonneg ((S).transfer_pos v).le
    exact inv_nonneg.mpr (Real.rpow_nonneg ((S).hl _).le _)
  intro t pick e
  exact WilsonIndependentSpoutPhysicalOrbit.stopped R W V m j w blocks Z issued (σ t) d (key t) cut arms
    (fun v=>sites v (pick v)) sample (fun v=>x v (pick v)) ip H c₀ simple same (fun v=>fare v (pick v))
    clear (safe pick) (q-e.val) (by omega) stop

theorem terminal (q:ℕ)(hq:q≤p):
    ∃k:ℕ,∃H₀:ℝ,0≤H₀ ∧ price R W V m j w σ d key cut arms sites sample ip H q (WilsonIndependentRawPeriodPower.terminal j)
      (fun v=>(S).P v ^ (-(1/4:ℝ))) k H₀:=by
  apply collect
  · intro v
    exact Real.rpow_nonneg ((C).synchronize v).le _
  intro t pick e
  exact WilsonIndependentSpoutPhysicalOrbit.terminal R W V m j w blocks Z issued (σ t) d (key t) cut arms
    (fun v=>sites v (pick v)) sample (fun v=>x v (pick v)) ip H c₀ simple same (fun v=>fare v (pick v))
    clear (safe pick) (q-e.val) (by omega)

end YM.Integration.WilsonIndependentSpoutPhysicalVisits
