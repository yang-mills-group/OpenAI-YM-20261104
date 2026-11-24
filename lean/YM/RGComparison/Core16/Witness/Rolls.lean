import YM.RGComparison.Core16.Witness.Framed
import YM.OPE.Rough.Gate

/-! Strengthening the Calendar, retain Smoothing & profile choices. Pre L headroom (for OPE
rough tickets), ratio selection & post L delays for the actual reporting scale. -/

set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Witness
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open Bid Motion
open scoped Topology BigOperators Classical
variable {G:Gauge} (s:Sheet G)
open scoped Matrix.Norms.Frobenius

set_option synthInstance.maxHeartbeats 80000 in
lemma lintel (hG:G.Simple) : ∃ P:Rolls s, (∀ i, ∃ k:ℕ, (P.L i).val=3^k) ∧ ∀ (a:Levels G),
    a.clock.stage=s.profile → a.clock.factor=P.L → Headroom a:=by
    choose A hA using Rolls.eventually_large s hG
    choose B hB using fun j d=> Doors.pre_tilt (2*(s.profile j).columns) (orbitCost ((Labels.frames G).level d))
    let b j:= (Finset.range (j+1)).sup (B j)
    let c j:=max (A j) (b j)
    let p j := (Finset.range (j+1)).sup c
    let L j:= (⟨3^(p j), pow_pos (by decide) _⟩:Side)
    have hL j:c j ≤ (L j).val:= by
        refine le_trans (Finset.le_sup (f:=c) (Finset.mem_range.mpr (Nat.lt_succ_self j))) ?_
        let x:= p j; suffices x < 3^x from this.le
        exact Nat.lt_pow_self (by norm_num)
    let P: Rolls s:= ⟨L, fun j=> hA j (L j) ((le_max_left ..).trans (hL j)) ((show Odd (3:ℕ) from ⟨1,rfl⟩).pow), fun i j hij=> pow_le_pow_right₀ (by decide) (Finset.sup_mono (Finset.range_mono (Nat.succ_le_succ hij)))⟩
    refine ⟨P,fun i=> ⟨p i,rfl⟩,fun a h h' m d hd=>?_⟩
    let i:= a.clock.J (m+1)
    let T:= L i; let f:= s.profile i
    rw [show a.S.block m=T from (a.fits.sameFactor m).symm.trans (congr_fun h' i),show a.params (m+1)=f from congr_fun h i]
    exact (hB i d T ((Finset.le_sup (Finset.mem_range_succ_iff.mpr hd)).trans ((le_max_right ..).trans (hL i)))).2

/-- Eq. gramdelay. Supplement further estimates' own `1+C_post ≤ 1+log Λ`
requirements by further increases; these don't claim all those delayed. -/
def mainLog (Q:Levels G) (m:ℕ) : ℝ := 2+Real.log (Q.clock.hatBeta m)
structure CalendarGate (Q:Levels G) : Prop where
  ratios m : ∃ k:ℕ, (Q.S.block m).val=3^k
  slow m : let t₁:= mainLog Q m; 1 + ((Q.S.block m).val:ℝ) ≤ Real.log t₁ ∧
      1 + (Q.params m).columns ≤ Real.log t₁ ∧ 1+(Q.params (m+1)).columns ≤ Real.log t₁

/-- Calendar used also for the soft precision arithmetic. Not just `Gentle`. -/
lemma buy_calendar {s:Sheet G}{P:Rolls s}{T:Protection P}(V:Delays T)(hp: ∀ i,∃ k:ℕ,(P.L i).val=3^k) :
    ∃ U:Delays T, DelayLe V U ∧ ∀ U', DelayLe U U'→ ∀ {X:Bar U'} (W:Wait X) (a:Levels G),
       Paid W a → CalendarGate a:=by
    let ζ (x:ℝ):= Real.log (2+Real.log x)
    have hT:Tendsto ζ atTop atTop:=Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_left _ _ Real.tendsto_log_atTop)
    obtain ⟨U,hU,_,h⟩:= delay_extra V (fun j x=> 1+((P.L j).val:ℝ) ≤ ζ x ∧ 1+(s.profile j).columns ≤ ζ x ∧ 1+(s.profile (j-1)).columns ≤ ζ x) (fun _ _ _=>True) (fun _=> (hT.eventually_ge_atTop _).and ((hT.eventually_ge_atTop _).and (hT.eventually_ge_atTop _))) (fun _ _=> by simp)
    refine ⟨U,hU,fun U' hi _ _ a hA=> ⟨fun m=>?_,fun m=>?_⟩⟩
    · rw [Extra.Iteration.block_eq hA]; exact hp _
    have hh:= ((h U' hi).1 _ _ (hA.pays m))
    rw [Extra.Iteration.block_eq hA, params_eq hA m, params_eq hA (m+1)]
    refine ⟨hh.1,?_,hh.2.1⟩
    rcases stepStages_target (step_paid a m) with h|h
    · rw [h]; exact hh.2.1
    rw [h]; exact hh.2.2
end YM.RGComparison.Core16.Witness
