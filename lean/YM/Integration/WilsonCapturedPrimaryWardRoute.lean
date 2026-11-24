import YM.Integration.WilsonThermometerOffsetTrajectory
import YM.RG05Readout.Many.Ramp

/-! Extend an already appointed upper addressed course through earlier dates.
The filed links at and above its old starting date stay the very same maps. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWardRoute
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Trace.Physical OPE MergeProof Push Local
open PhysicalNext.Repeat.Legato RG05Readout RG05Readout.Address Copper
open WilsonThermometerOffsetTrajectory
open scoped Topology Classical BigOperators
variable {G:Gauge} {C:Family G} {D:Rail C} {B:ℕ → ℕ → ℝ} {N p d k m:ℕ} {h:C.Makes}
    {sites:∀i,Bud C p i} {V:Sight C d p} {r:Emblems C d}

theorem restrict (t:Enrolled h D B k N p d sites V r) (km:k ≤ m):Enrolled h D B m N p d sites V r:=
  ⟨t.starts,fun j start=>t.legal j (km.trans start),fun j start=>t.follows j (km.trans start)⟩

theorem extend (t:Enrolled h D B m N p d sites V r) (mN:m ≤ N) (km:k ≤ m) (a:Awake D B k d):
    ∃ (V':Sight C d p) (r':Emblems C d),Enrolled h D B k N p d sites V' r' ∧
      ∀j,m ≤ j → r' j=r j ∧ V' j=V j:=by
  induction km using Nat.decreasingInduction with
  | self=>exact ⟨V,r,t,fun _ _=>⟨rfl,rfl⟩⟩
  | of_succ k km ih=>
    obtain ⟨V',r',track,agrees⟩:=ih (show Awake D B (k+1) d from
      ⟨fun i hi=>(a.post i hi).trans k.le_succ,fun i hi=>a.cash i (k.le_succ.trans hi),
       fun p i N hi=>a.toll p i N (k.le_succ.trans hi)⟩)
    have live:k<N:=km.trans_le mN
    obtain ⟨W,q,paid,ride⟩:=WilsonThermometerOffsetGraph.step h live
      (a.toll p k N le_rfl live) (track.legal (k+1) le_rfl live) (sites k)
    refine ⟨update V' k W,update r' k q,⟨?_,?_,?_⟩,?_⟩
    · rw [update_of_ne live.ne'];exact track.starts
    · intro i start under
      by_cases hi:i=k
      · subst i;rw [update_self];exact paid
      rw [update_of_ne hi];exact track.legal i (by omega) under
    · intro i start under
      rw [update_of_ne (show i+1≠k by omega)]
      by_cases hi:i=k
      · subst i;rw [update_self,update_self];exact ride
      rw [update_of_ne hi,update_of_ne hi];exact track.follows i (by omega) under
    · intro j start
      rw [update_of_ne (show j≠k by omega),update_of_ne (show j≠k by omega)]
      exact agrees j start

theorem same {q r:Emblems C d} {j:ℕ} (live:m ≤ j) (h:∀a,m ≤ a → q a=r a):
    finer q live=finer r live:=by
  induction j,live using Nat.le_induction with
  | base=>simp only [base_value]
  | succ j hj ih=>rw [finer_next hj,finer_next hj,h j hj,ih]

end YM.Integration.WilsonCapturedPrimaryWardRoute
