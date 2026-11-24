import YM.Integration.WilsonMaxwellThermometerStationHeads
import YM.Integration.WilsonPositionCorrectedCap
import YM.Integration.WilsonPositionThermometerStationNorm

/-! The three signed maximal blocks at the original cutoff converge to the actual
positioned source coordinates together. The estimate is before N and period and
retains every missing-slot unit on its own cap. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerNominatedOrientation
open Function Filter RG Lattice Wilson Source Labels Next.Rank Next.Rank.Price Next.Rank.Atlas
open Next.Rank.Station Further.CorrectedLift Cells Extraction Table Climb Trace Trace.Pilot Next.UVStress MergeProof.East
open PhysicalNext.Repeat.Legato WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open Spec OPE OPE.Orbits RG17 PhysMS PhysMS.Frame Maxwell XSpace XSpace.Normalize WilsonPositionCapTransport
open WilsonMaxwellThermometerMaximalHead WilsonMaxwellThermometerStationHeads
open scoped BigOperators Classical Topology
variable {G:Gauge} (R:Run G)
local notation "C"=>R.family
local notation "road"=>R.family.path.levels

private theorem changeTarget {d:ℕ}(F:Labels.Frame G d)(χ:ℝ)(x p u:F.Coeff):
    error F χ x u≤error F χ x p+F.coeffSize (p-u):=by
  unfold error Labels.Frame.coeffSize
  rw [←Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _=>?_
  by_cases h:F.grades i=(d,d/2)
  · simp only [if_pos h]
    calc
      _=‖((χ:ℂ)*x i-p i)+(p i-u i)‖:=by congr 1;abel
      _≤_:=norm_add_le _ _
  · simp only [if_neg h,zero_add]
    exact norm_nonneg _

def deviation (A:Group C 6)(N per:ℕ)(s:Finset (Fin 3))(i:Fin 3):ℝ:=
  let j:=index A (grade i)
  let w:=A.change (grade i) (source C s i)
  let χ:=(shrink C A.station.k N per)^(j.val/2)/(Station.mag road A.station.b A.station.k)^j.val
  let x:=awake C j A.station.k N per (A.station.wheel.atCut (N,per) j w)
  error ((C).labels.level j) χ x (ladder C j (source C s i))

variable {f:Extraction.Order} {Y:Ultrafilter (ℕ×ℕ)} {H:(Bel R.family.book).Hierarchy}
    {S:Table R.family.book}

theorem inBook (simple:G.Simple)(A:ℝ→Group C 6)(P:ℝ→tower S)
    (paid:Book (f:=f) (l:=Y) (H:=H) A P) {δ:ℝ}(pos:0<δ):
    ∀ᶠ r in trail, ∀ N per,(A r).station.k<N→∀s i,deviation R (A r) N per s i<δ:=by
  have dates:Tendsto (fun r=>(A r).station.k) trail atTop:=
    tendsto_atTop.mpr fun k=>(paid k).mono fun _ h=>h.1
  have late:=dates.eventually (WilsonMaxwellThermometerStationHeads.original (f:=f) (H:=H) R simple)
  have kfee:= (rate R simple).comp dates
  have one:Tendsto (fun _:ℝ=>(1:ℝ)) trail (𝓝 1):=tendsto_const_nhds
  have small:Tendsto (fun r=>|fee R (A r).station.k/(1-fee R (A r).station.k)|) trail (𝓝 0):=by
    simpa only [Function.comp_def,Pi.div_apply,sub_zero,zero_div,abs_zero] using
      (kfee.div (one.sub kfee) (by norm_num : (1:ℝ)-0≠0)).abs
  have same:localCost trail P P:=fun _ _=>by simp
  have oneSlot (s:Finset (Fin 3))(i:Fin 3):∀ᶠ r in trail,∀ N per,(A r).station.k<N→deviation R (A r) N per s i<δ:=by
    let d:=grade i
    let u:=source C s i
    let w:=fun r=>(A r).change d u
    let B:=WilsonPositionThermometerStationNorm.cost C d
    have near:Tendsto w trail (𝓝 u):=by
      simpa only [WilsonPositionCapTransport.through,LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply] using
        WilsonPositionCapTransport.near P P A paid same d u
    have close:Tendsto (fun r=>‖w r-u‖) trail (𝓝 0):=by
      simpa only [sub_self,norm_zero] using (near.sub (tendsto_const_nhds (x:=u))).norm
    have bound:Tendsto (fun r=>|fee R (A r).station.k/(1-fee R (A r).station.k)| *(B*‖w r‖)+B*‖w r-u‖)
        trail (𝓝 0):=by
      simpa only [zero_mul,mul_zero,zero_add] using
        (small.mul (tendsto_const_nhds.mul near.norm)).add (tendsto_const_nhds.mul close)
    filter_upwards [paid 0,late,bound.eventually_lt_const pos] with r ready checked tiny
    intro N per large
    have measured:=checked (A r) rfl ready.2.1 N per large s i
    let F:Labels.Frame G d:=(C).labels.level d
    have rent:=WilsonPositionThermometerStationNorm.ladder C d (w r)
    have move:=WilsonPositionThermometerStationNorm.ladder C d (w r-u)
    have nonneg:0≤F.coeffSize (ladder C d (w r)):=Finset.sum_nonneg fun _ _=>norm_nonneg _
    apply lt_of_le_of_lt _ tiny
    apply (changeTarget F _ _ (ladder C d (w r)) _).trans
    apply add_le_add
    · exact measured.trans ((mul_le_mul_of_nonneg_right (le_abs_self _) nonneg).trans
        (mul_le_mul_of_nonneg_left rent (abs_nonneg _)))
    · change (R.family.labels.level d).coeffSize (ladder C d (w r)-ladder C d u) ≤ B*‖w r-u‖
      rw [←map_sub]
      exact move
  filter_upwards [eventually_all.mpr fun s=>eventually_all.mpr (oneSlot s)] with r ready N per large s i
  exact ready s i N per large

theorem original (simple:G.Simple)(F:Final C f S)(J:ℝ→tower S)(V:Store G)
    (A:ℝ→Group C 6)(book:Book (f:=f) (l:=Y) (H:=H) A J)(lead:Leading F J)
    {δ:ℝ}(pos:0<δ):
    ∀ᶠ r in trail,∀ N per,(A r).station.k<N→∀s i,
      deviation R (WilsonPositionCorrectedCap.adjusted F J V A r) N per s i<δ:=
  inBook R simple _ _ (WilsonPositionCorrectedCap.original F J V A book lead) pos

end YM.Integration.WilsonMaxwellThermometerNominatedOrientation
