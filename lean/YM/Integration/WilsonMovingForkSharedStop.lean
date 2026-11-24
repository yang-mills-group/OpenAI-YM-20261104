import YM.Integration.WilsonMovingForkElectedPhase
import YM.Integration.WilsonMovingForkProbeEars

/-! The arbitrary pre-elected original stop receives the signed displaced
cell on a wider window and all public full/Gram rows on its original homes. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
noncomputable section
namespace YM.Integration.WilsonMovingForkSharedStop
open Function Filter Finset Set Metric Lattice Extraction Table Spec PhysMS Trace Trace.Pilot Climb
open GapsContact GapsContact.Ascent Contacts.Mat WilsonSeparatedGridDesign WilsonSeparatedGridTree WilsonSeparatedBranchStencil
open OPE RG16 RG16.Literal RG17 FVA2 FVA2.Register MS MS.Land PhysicalNext.Repeat.Legato
open WilsonThermometerUnitFilingCoarse WilsonThermometerUnitFilingFourSquare
open WilsonOriginalTwoFlatGridCapture (word)
open WilsonOriginalTwoFlatGridScaling (gap)
open WilsonPositionHomogeneousFrame (homogeneous)
open WilsonReflectedPublicStationFare (station)
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonThermometerUnitFilingFourPoolClock (outer)
open WilsonMovingForkOpticalBook (reporter)
open WilsonMovingForkHeterogeneousCut (Filed Heard Invoice)
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
  {H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}{l:Ultrafilter (ℕ×ℕ)}
  (J:ℝ → tower S)(Z:WilsonPrescription G){I:Type}[Fintype I][DecidableEq I][Nonempty I]

open WilsonMovingForkProbeEars (Charge)
open WilsonMovingForkProbeMaster (subface visit)
open WilsonMovingForkAbsolutePhase (Sampled)

theorem enrolled {J₀ u:ℕ}(stop:Stop R.family 0 J₀ u)
    (order:(l:Filter _) ≤ f.fuse)(fac:Facilities R.family f S)(bliss:Bliss F l z H)
    (slow:WilsonWindowReportingPace.Slow R.kit)(lead:Leading F J)(owed:∀d,∀ᶠr in trail,Frame.obedient F H (J r) d)
    (D T B:ℕ)(d:I→Fin (D+1))(x:∀i,Free R.family (d i).val){δ:ℝ}(dp:0<δ)
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (priced:∀s,WilsonMovingForkWindowBooks.Priced F (books s)):
    ∃fee:I→ℝ,(∀i,1≤fee i) ∧
      (∀b:ℕ,B≤b → ∀M η:ℝ,1≤M → 0<η →
        Sampled F J Z fac.simpleGate D T B b d x M η δ books u fee) ∧
      ∀η M:ℝ,0<η → 0≤M → ∀P q n:ℕ,0<n → ∀look:Fin n ↪ I,∀E:Type,∀[Fintype E],
        Charge F J Z D T B d x books η M u P q n look E:=by
  obtain ⟨_,_,_,L⟩:=fac.costlier
  obtain ⟨fee,unit,all⟩:=WilsonMovingForkElectedPhase.filed F J Z L.toPackage stop fac bliss slow lead owed
    D T B d x dp books priced
  refine ⟨fee,unit,all,?_⟩
  intro η M ep mp P q n has look E inst
  let face:=subface look
  let index:=visit look
  have occupied:face.Nonempty:=⟨_,(index ⟨0,has⟩).property⟩
  have purchase:=WilsonMovingForkElectedPhase.same F J Z D T B d x books u fee unit
    (all B le_rfl (M+1) (η/2) (by linarith) (half_pos ep))
  let select:=fun i:Fin n=>(index i).val
  obtain ⟨m,C₀,cn,grid⟩:=WilsonMovingForkGridHearing.original F J Z order fac.simpleGate bliss slow lead owed
    D T B d ep books select E P (M:=M)
  obtain ⟨D₀,positive,phase⟩:=WilsonOriginalTwoFlatPublicReindex.sampled F J Z fac.simpleGate D T B d x
    (M+1) (η/2) δ books u purchase q face occupied index
  refine ⟨m,C₀,D₀,cn,positive,?_⟩
  have gpos:=(wilson_link F fac.simpleGate bliss.budgets bliss.keen bliss.lies).positive
  filter_upwards [grid,phase,gpos] with r sites passed gp
  intro rp ρ span anchor j mesh selector di
  obtain ⟨uj,originalPhase⟩:=passed.2.2 ρ span anchor
  refine ⟨uj,?_⟩
  intro weak v book arms K jK b names t c ut tc ck pred w wn good wage ref X cost separate prog values
  apply sites rp ρ span anchor (fun i=>x (select i)) weak K jK b names u t c uj ut tc ck pred
    (D₀*(wilson z r)^q) w (add_nonneg (mul_nonneg positive.le (pow_nonneg gp.le _)) wn)
  · intro o h N per live
    exact (originalPhase N per live o h.1 h.2 weak).1
  · exact wage
  · exact cost
  · exact separate

end YM.Integration.WilsonMovingForkSharedStop
