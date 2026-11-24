import YM.Integration.WilsonPhysicalActualMixedMenus

/-! Physical home prices for the exact microscopic roster. Every grade, home and
public source in the comparison uses the one original booked stage. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalActualMixedCosts
open Function Filter Finset MeasureTheory Lattice RG Wilson Extra.Histories
open Table Climb Spec PhysicalNext.Repeat.Legato Trace.Target Trace.Pilot
open OPE Next.Extract RG.Supply MS MS.Land FVA2 FVA2.Register PhysMS
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonPhysicalAllGradeWeakElection WilsonPhysicalWeakWallStaff WilsonPhysicalWeakSameStation WilsonPhysicalWeakWallBooks
open WilsonPhysicalWeakWallBounded (cost)
open WilsonPhysicalActualMixedMenus (Choices source name multiplier fee)
open WilsonPhysicalActualWeakCylinders (product)
open scoped Classical BigOperators Topology
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}{l:Ultrafilter (ℕ×ℕ)}
variable (F:Final R.family f S)(J:ℝ→tower S){H:(Bel R.family.book).Hierarchy}{arch:Trace.Terrace.Arch R.family}
  (simple:G.Simple)(birth:Assignment F J H l simple){D T:ℕ}{δ:ℝ}
  (books:(r:{r:ℝ//0<r ∧ r<δ})→Book F (l:=l) H arch D T r.val)
  (shared:∀r,∃cap:D≤(birth.day r.val).1,Shared F (books r) (trim cap (birth.day r.val).2))
variable (Z:WilsonPrescription G)(lead:Leading F J)(obeys:∀d,∀ᶠr in trail,Frame.obedient F H (J r) d)
variable {I X:Type}[Fintype I](d:I→Fin (D+1))(u:Filter X)(home:I→X→{r:ℝ//0<r ∧ r<δ})
  (near:∀i,Tendsto (fun z=>(home i z).val) u trail)
local notation "C" => R.family
local notation "B" z:max => (fun i:I=>books (home i z))

include shared lead obeys near in
theorem original:∃B₀:I→ℝ,(∀i,0≤B₀ i) ∧ ∀ᶠz in u,∀(v:(i:I)→(Bel R.family.book).Field (d i))
    (weak:I→Bool)(turn:I→Motion),
    (∑e:Choices (R:=R) d weak,‖multiplier F J Z (B z) d v weak turn e‖)≤
      ∏i,if weak i then B₀ i*cost (C) (v i) else 1:=by
  choose B₀ pos hired using fun i=>WilsonPhysicalActualWeakNames.bounded F J simple birth books shared Z lead obeys u (home i) (near i) (d i)
  refine ⟨B₀,pos,?_⟩
  filter_upwards [Filter.eventually_all.mpr hired] with z live v weak turn
  rw [WilsonPhysicalActualMixedMenus.variation]
  apply Finset.prod_le_prod
  · intro i _
    rw [←WilsonPhysicalActualMixedMenus.restored]
    exact Finset.sum_nonneg fun _ _=>norm_nonneg _
  · intro i _
    by_cases yes:weak i
    · simpa only [WilsonPhysicalActualMixedMenus.fee,yes,ite_true,Bool.true_eq] using live i (v i)
    · simp [WilsonPhysicalActualMixedMenus.fee,yes]

include shared lead obeys near in
theorem earned:∃B₀:I→ℝ,(∀i,0≤B₀ i) ∧ ∀ᶠz in u,∀(v:(i:I)→(Bel R.family.book).Field (d i))
    (weak:I→Bool)(turn:I→Motion)(N p:ℕ)(site:I→Site ((C).side N p))(forecast:Choices (R:=R) d weak→ℂ)
    (Δ:ℝ),0≤Δ→(∀e:Choices (R:=R) d weak,‖(C).omega N p
      (product d turn N p site (fun i=>source F J Z (d i) ((B z) i) (v i) (weak i) (e i) N p))-forecast e‖≤Δ)→
    ‖(C).omega N p (product d turn N p site (fun i=>name F J Z (d i) ((B z) i) (v i) (weak i) N p))-
        ∑e:Choices (R:=R) d weak,multiplier F J Z (B z) d v weak turn e*forecast e‖≤
      (∏i,if weak i then B₀ i*cost (C) (v i) else 1)*Δ:=by
  obtain ⟨B₀,pos,price⟩:=original F J simple birth books shared Z lead obeys d u home near
  refine ⟨B₀,pos,?_⟩
  filter_upwards [price] with z paid v weak turn N p site forecast Δ nonneg quote
  refine (WilsonPhysicalActualMixedMenus.charged F J Z (B z) d v weak turn N p site forecast (fun _=>Δ) quote).trans ?_
  rw [←Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (paid v weak turn) nonneg

end YM.Integration.WilsonPhysicalActualMixedCosts
