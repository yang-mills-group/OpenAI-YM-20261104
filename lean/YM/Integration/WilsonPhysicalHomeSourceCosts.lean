import YM.Integration.WilsonPhysicalActualMixedCosts
import YM.Integration.WilsonPhysicalActualMixedFaces
import YM.Integration.WilsonThermometerUnitFilingFourPoolClock

/-! The weak and pooled physical names have one finite variation bound over all choices
of their real home radii in the reporting window. The assignment and its books precede
the radii, the direction of each source, and the choice of an ordinary face. -/

namespace YM.Integration.WilsonPhysicalHomeSourceCosts
noncomputable section
open Function Filter Finset MeasureTheory Lattice RG Wilson Extra.Histories
open Table Climb Spec PhysicalNext.Repeat.Legato Trace.Target Trace.Pilot
open OPE Next.Extract RG.Supply MS MS.Land FVA2 FVA2.Register PhysMS
open Set Metric Stock
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonPhysicalAllGradeWeakElection WilsonPhysicalWeakWallStaff WilsonPhysicalWeakSameStation WilsonPhysicalWeakWallBooks
open WilsonPhysicalWeakWallBounded (cost)
open WilsonPhysicalActualMixedMenus (Choices multiplier)
open WilsonPhysicalActualMixedFaces (Menu phase)
open WilsonThermometerUnitFilingFourPoolClock (outer longer)
open scoped Classical BigOperators Topology
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}{l:Ultrafilter (ℕ×ℕ)}
variable (F:Final R.family f S)(J:ℝ→tower S){H:(Bel R.family.book).Hierarchy}{arch:Trace.Terrace.Arch R.family}
  (simple:G.Simple)(birth:Assignment F J H l simple){D T:ℕ}{δ:ℝ}
  (books:(r:{r:ℝ//0<r ∧ r<δ})→Book F (l:=l) H arch D T r.val)
  (shared:∀r,∃cap:D≤(birth.day r.val).1,Shared F (books r) (trim cap (birth.day r.val).2))
variable (Z:WilsonPrescription G)(lead:Leading F J)(obeys:∀d,∀ᶠr in trail,Frame.obedient F H (J r) d)
local notation "C" => R.family
local notation "Home" => {r:ℝ//0<r ∧ r<δ}

include shared lead obeys in
theorem station (d:Fin (D+1)):
    ∃c:ℝ,0≤c ∧ ∃a:ℝ,0<a ∧ ∀s:Home,s.val<a→∀x:(Bel (C).book).Field d,
      ∑e,‖WilsonPhysicalActualWeakNames.coefficient F J Z d (books s) x e‖≤c*cost (C) x:=by
  let u:Filter Home:=comap Subtype.val trail
  have near:Tendsto (fun s:Home=>s.val) u trail:=tendsto_comap
  obtain ⟨c,cp,paid⟩:=WilsonPhysicalActualWeakNames.bounded F J simple birth books shared Z lead obeys u id near d
  obtain ⟨q,hq,kept⟩:=Filter.mem_comap.mp paid
  obtain ⟨a,ap,small⟩:=Metric.mem_nhdsWithin_iff.mp hq
  refine ⟨c,cp,a,ap,?_⟩
  intro s hs
  apply kept
  apply small
  exact ⟨by simpa only [mem_ball,Real.dist_eq,sub_zero,abs_of_pos s.property.1] using hs,s.property.1⟩

include shared lead obeys in
theorem original (bliss:Bliss F l arch H){n:ℕ}(d:Fin n→Fin (D+1))(h:ℕ):
    ∃C₀:Fin n→ℝ,(∀i,0≤C₀ i) ∧ ∀ᶠr in trail,∀ρ:Fin n→Home,(∀i,(ρ i).val≤outer arch h r)→
    ∀(x:(i:Fin n)→(Bel (C).book).Field (d i))(b:Fin n→Bool)(turn:Fin n→Motion)(s:(Stock.census (Fin n)).Mode),
      (∑z:Menu (R:=R) d b s,‖phase F J Z (fun i=>books (ρ i)) d x b turn s z‖)≤
        ∏i:↥s.val,if b i then C₀ i*cost (C) (x i) else 1:=by
  choose C₀ pos a ap pay using fun i=>station F J simple birth books shared Z lead obeys (d i)
  have within:∀i,∀ᶠr in trail,outer arch h r<a i:=fun i=>(longer F simple bliss h).eventually
    ((gt_mem_nhds (ap i)).filter_mono nhdsWithin_le_nhds)
  refine ⟨C₀,pos,?_⟩
  filter_upwards [Filter.eventually_all.mpr within] with r small ρ actual x b turn s
  have eq:(∑z:Menu (R:=R) d b s,‖phase F J Z (fun i=>books (ρ i)) d x b turn s z‖)=
      ∏i:↥s.val,WilsonPhysicalActualMixedMenus.fee F J Z (d i) (books (ρ i)) (x i) (b i):=by
    unfold phase
    convert! WilsonPhysicalActualMixedMenus.variation F J Z (fun i:↥s.val=>books (ρ i))
      (fun i:↥s.val=>d i) (fun i:↥s.val=>x i) (fun i:↥s.val=>b i) (fun i:↥s.val=>turn i) using 3
  rw [eq]
  apply Finset.prod_le_prod
  · intro i _
    rw [←WilsonPhysicalActualMixedMenus.restored]
    exact Finset.sum_nonneg fun _ _=>norm_nonneg _
  · intro i _
    by_cases yes:b i
    · simpa only [WilsonPhysicalActualMixedMenus.fee,yes,ite_true,Bool.true_eq] using
        pay i (ρ i) ((actual i).trans_lt (small i)) (x i)
    · simp [WilsonPhysicalActualMixedMenus.fee,yes]

end
end YM.Integration.WilsonPhysicalHomeSourceCosts
