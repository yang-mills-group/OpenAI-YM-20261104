import YM.Integration.WilsonIndependentConditionedBankClosing
import YM.Integration.WilsonIndependentConditionedGramSpatialCourse
import YM.Integration.WilsonReflectedMixedObservedSchool

/-! The original public school buys its one optical berth before the independent numerical order and the observing placements. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedBankRulerCourse
open Filter Lattice RG Wilson PhysicalNext.Repeat.Legato Extraction Table Spec Trace.Pilot Trace.Physical
open GapsContact Climb Next.Rank XSpace XSpace.Cirrus Pert.Asymptotics
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonThermometerUnitFilingFourPoolClock (outer)
open WilsonReflectedMixedLocatedSchool (Paid)
open WilsonReflectedOpticalRate (depth)
open WilsonAddressedMixedStationRange (width)
open WilsonIndependentConditionedGramSpatialCourse (Page)
open WilsonIndependentConditionedGramSpatialHost (date)
open WilsonMovingForkOpticalBook (reporter)
open WilsonOriginalPublicRelativeGramKineticMesh (thermal)
open WilsonInvariantActionPosition (berth)
open scoped Topology BigOperators Classical
variable {G:Gauge}{R:Run G}{ord:Extraction.Order}{S:Table R.family.book}(F:Final R.family ord S)
    {l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{Z:Trace.Terrace.Arch R.family}
    {I:Type}[Fintype I][Nonempty I]

theorem cold (R:Run G)(simple:G.Simple):∀ᶠ f:ℕ in atTop,8*thermal R f≤1:=by
  filter_upwards [(WilsonAdmissionScale.logarithm_tendsto R.family.path.levels simple).eventually_ge_atTop (Real.log 64)]
    with f large
  have pos:0<R.family.path.levels.clock.hatBeta f:=zero_lt_one.trans (R.family.path.levels.fits.delayed f)
  have lower:64≤R.family.path.levels.clock.hatBeta f:=(Real.log_le_log_iff (by norm_num) pos).mp large
  change 8*(Real.sqrt _)⁻¹≤1
  rw [←div_eq_mul_inv,div_le_one (Real.sqrt_pos.mpr pos)]
  simpa only [show Real.sqrt 64=8 by norm_num] using Real.sqrt_le_sqrt lower

def Quoted (E₀ E₁ H U τ q P:ℕ)(ζ:ℝ):Prop:=
  (P:ℝ)+1+((2*E₀:ℕ):ℝ) ≤ ((2*τ:ℕ):ℝ)*(3*ζ/4) ∧
  (P:ℝ)+1+((2*(E₁+U*H):ℕ):ℝ) ≤ ((q+1:ℕ):ℝ)-((2*(τ+1):ℕ):ℝ)*H

theorem original (simple:G.Simple)(bliss:Bliss F l Z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    {D T h t:ℕ}{δ:ℝ}(d:I→Fin (D+1))
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H Z D T s.val)
    (read:(i:I)→{s:ℝ // 0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val)
    (appointed:WilsonReflectedMixedObservedSchool.Joined F D T h t d books read):
    ∃M:I→ℝ,∃E:I→ℕ,(∀i,1≤M i) ∧ ∀(effort:I→ℕ)(target P:ℕ)(ζ:ℝ),0<ζ →
    ∃pwr:ℕ,(∀i,effort i+1≤2*pwr) ∧
      let τ:=depth ((2*pwr+∑i,E i)+1) (width T h) D
      let U:=2*T+11+2*h
      let cap:=max 1 (4*∑i,M i)
      let stage:=(∑i,E i)+WilsonAddressedMixedRawTrial.power T h τ D
      ∃Q:ℕ,∀q≥Q,(∀i j:I,Quoted (E i+E j) (E i+E j+max (E i) (E j))
        (2*((d i).val+(d j).val)+1) U τ q P ζ) ∧
      ∀(floor p:ℕ)(ε:ℝ),0<ε → ∀ᶠr in trail,
      ∀ρ:I→{s:ℝ // 0<s ∧ s<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer Z h r) → (∃i,(ρ i).val=r) →
        let m:=date R simple r
        let f:=reporter F books ρ
        let K:=berth R τ f
        floor ≤ m ∧ Page R r m f K τ U p ε ∧
        (∀N per,K≤N→ |regulatorRun R.family N per K|≤8*thermal R f ∧ |regulatorRun R.family N per K|≤1) ∧
        (∀phys:Bool,Paid F D T d books (fun i s=>read i s phys) M E ρ f) ∧
        WilsonReflectedMixedObservedPanel.Received F D T h t d effort books read M cap
          (WilsonReflectedMixedSharpPanel.reserve 2 ζ) stage target ρ f K:=by
  classical
  obtain ⟨M,E,big,issued⟩:=appointed
  refine ⟨M,E,big,?_⟩
  intro effort target P ζ positive
  let S₀:=∑i,E i
  let U:=2*T+11+2*h
  let cost:=4*D+1
  obtain ⟨need,ready⟩:=WilsonIndependentConditionedBankClosing.before P 1 ζ positive cost (2*S₀) (3*S₀+U*cost)
  let pwr:=max need (Finset.univ.sup effort+1)
  have capacity (i:I):effort i+1≤2*pwr:=by
    have small:=Finset.le_sup (f:=effort) (Finset.mem_univ i)
    have enough:=le_max_right need (Finset.univ.sup effort+1)
    dsimp only [pwr];omega
  refine ⟨pwr,capacity,?_⟩
  intro τ U' cap stage
  have depth₀:need≤τ:=by
    have ok:=le_max_left need (Finset.univ.sup effort+1)
    dsimp only [τ,depth,pwr]
    omega
  obtain ⟨Q,high⟩:=ready τ depth₀
  refine ⟨Q,?_⟩
  intro q afterQ
  obtain ⟨lo,hi⟩:=high q afterQ
  constructor
  · intro i j
    have lim (i:I):E i≤S₀:=Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)
    have fits:2*((d i).val+(d j).val)+1≤cost:=by
      have a:=(d i).isLt;have b:=(d j).isLt
      dsimp [cost];omega
    have e₀:2*(E i+E j)≤2*(2*S₀):=by have:=lim i;have:=lim j;omega
    have e₁:2*(E i+E j+max (E i) (E j)+U'*(2*((d i).val+(d j).val)+1))≤2*(3*S₀+U*cost):=by
      have room:=Nat.mul_le_mul_left U fits
      change 2*(E i+E j+max (E i) (E j)+U*(2*((d i).val+(d j).val)+1))≤_
      have:=lim i;have:=lim j;omega
    have ec:((2*((d i).val+(d j).val)+1:ℕ):ℝ)≤cost:=by exact_mod_cast fits
    have a₀:((2*(E i+E j):ℕ):ℝ)≤((2*(2*S₀):ℕ):ℝ):=by exact_mod_cast e₀
    have a₁:((2*(E i+E j+max (E i) (E j)+U'*(2*((d i).val+(d j).val)+1)):ℕ):ℝ)≤
        ((2*(3*S₀+U*cost):ℕ):ℝ):=by exact_mod_cast e₁
    have spend:=mul_le_mul_of_nonneg_left ec (by positivity : 0≤((2*(τ+1):ℕ):ℝ))
    unfold Quoted
    constructor
    · linarith only [lo,a₀]
    · linarith only [hi,a₁,spend]
  · intro floor p ε good
    have physical:=issued 2 ζ positive effort pwr target capacity
    have spatial:=WilsonIndependentConditionedGramSpatialCourse.original F simple bliss slow D T h τ p d good books
    obtain ⟨c,coldF⟩:=eventually_atTop.mp (cold R simple)
    filter_upwards [physical,spatial,(WilsonIndependentConditionedGramSpatialHost.late R simple).eventually_ge_atTop (max floor c)]
      with r originalPage grid live
    intro ρ margin base m f K
    have field:=originalPage ρ margin base
    have pg:Page R r m f K τ U' p ε:=(grid ρ margin base).1
    refine ⟨(le_max_left floor c).trans live,pg,?_,field⟩
    intro N per top
    have kin:=WilsonOriginalPublicRelativeGramKineticMesh.original_gauge R simple f K N per pg.higher.le top
    exact ⟨kin,kin.trans (coldF f (((le_max_right floor c).trans live).trans pg.before))⟩

end YM.Integration.WilsonIndependentConditionedBankRulerCourse
