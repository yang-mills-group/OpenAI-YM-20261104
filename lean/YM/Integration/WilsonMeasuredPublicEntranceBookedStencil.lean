import YM.Integration.WilsonMeasuredPublicEntranceChosenTestCost
import YM.Integration.WilsonMeasuredPublicEntranceNamedTestGrid
import YM.Integration.WilsonMovingForkPublicGrid

/-! One signed interpolation stencil on the actual purchased reporting level.
All weak and pooled field choices and their time adjoints share the same nodes. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace YM.Integration.WilsonMeasuredPublicEntranceBookedStencil
open Function Filter Finset Set Metric Lattice Wilson RG Extraction Table Spec PhysMS Trace Trace.Pilot Climb
open GapsContact GapsContact.Ascent Contacts.Mat WilsonSeparatedGridDesign WilsonSeparatedBranchStencil
open WilsonPositionHomogeneousFrame FVA2 FVA2.Register MS MS.Land RG17 PhysicalNext.Repeat.Legato
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonAddressedPublicCardBooks (Housed)
open WilsonOriginalTwoFlatPublicNamedFare (chosen)
open WilsonMeasuredPublicEntranceWeakTestCost (slot)
open WilsonThermometerUnitFilingFourPoolClock (outer)
open WilsonMovingForkOpticalBook (reporter)
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    {l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}
    (J:ℝ→tower S)(Z:WilsonPrescription G)
    {I:Type}[Fintype I][Nonempty I]{D T:ℕ}(d:I→Fin (D+1)){δ:ℝ}
    (books:(r:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T r.val)
local notation "a" => R.family.S.a
local notation "g" => wilson z

def chart {n:ℕ}(pick:Fin n→I)(r:{s:ℝ // 0<s ∧ s<δ})
    (y:(i:I)→(Bel R.family.book).Field (d i).val)(v:(i:I)→Free R.family (d i).val)
    (b marked:Fin n→Bool)(x:Points n):ℂ:=
  S.classMoment S (fun i=>(d (pick i)).val) (r.val • x) (fun i=>slot F (marked i)
    (chosen F J Z r.val ((books r).V (d (pick i))) (b i) (y (pick i)) (v (pick i))))

def date (r:{s:ℝ // 0<s ∧ s<δ}):ℕ:=reporter F books (fun _:I=>r)

theorem original (simple:G.Simple)(bliss:Bliss F l z H)(cash:Trace.Terrace.PostT R.family.path.levels)
    (slow:WilsonWindowReportingPace.Slow R.kit)(below:(l:Filter (ℕ×ℕ))≤f.fuse)(lead:Leading F J)
    (owed:∀d,∀ᶠr in trail,Frame.obedient F H (J r) d){n:ℕ}(pick:Fin n→I)(E:Type)[Fintype E]
    {η M:ℝ}(ep:0<η)(P:ℕ):
    ∃m:ℕ,∃K:ℝ,0≤K ∧ ∀ᶠt in trail,∀r:{s:ℝ // 0<s ∧ s<δ},r.val=t → Housed F (books r) →
      let j:=date (I:=I) F books r
      let dp:=div_pos (R.family.S.a_pos j) r.property.1
      ∀ref:E→E4,∀X:Points n,(∀i,‖X i‖≤M) → (∀i k,i≠k→η≤dist (X i) (X k)) →
      let T₀:=sold m ref dp X
      (∀q:T₀.sample,∃o:Fin n→ Cover,tag (a j) o=r.val • T₀.site q ∧
        tag (a j) o∈generic n ∧ tag (a j) o∈conf n ∧
        (∀i,‖R.family.S.gridPoint j (o i)‖≤(M+1)*r.val) ∧
        Pairwise fun i k=>(η/2)*r.val≤‖R.family.S.gridPoint j (o i)-R.family.S.gridPoint j (o k)‖) ∧
      ∀y:(i:I)→(Bel R.family.book).Field (d i).val,∀v:(i:I)→Free R.family (d i).val,∀b marked:Fin n→Bool,
      let field:=chart F J Z d books pick r y v b marked
      ‖field X-read T₀ field‖≤K*(∏i,(‖v (pick i)‖+‖y (pick i)‖))*(g r.val)^P:=by
  classical
  let di:=fun i=>(d (pick i)).val
  choose h C cn incomes using fun i:Fin n=>WilsonMeasuredPublicEntranceChosenTestCost.original F J Z simple bliss cash slow below lead owed T (d (pick i))
  obtain ⟨m,K,kn,quad⟩:=WilsonMeasuredPublicEntranceNamedTestGrid.original F simple bliss di ep (∑i,h i) P E
  obtain ⟨gap,pp,margin⟩:=WilsonMovingForkScreenedSites.margin ep m n E
  have link:=wilson_link F simple bliss.budgets bliss.keen bliss.lies
  have tiny:=((link.conforms simple).pow 2).eventually (ge_mem_nhds (by simpa using pp:(0:ℝ)^2<gap))
  refine ⟨m,K*∏i,C i,mul_nonneg kn (prod_nonneg fun i _=>cn i),?_⟩
  filter_upwards [quad,tiny,link.positive,Filter.eventually_all.mpr incomes,
    WilsonOriginalTwoFlatPublicMixedMesh.original F simple bliss slow D T 0 d books] with t sale small gp income mesh
  rintro r rfl housed j dp ref X reach separated T₀
  have outer₀:outer z 0 r.val=r.val:=by simp [outer]
  have booked:=mesh (fun _:I=>r) (fun _=>⟨le_rfl,outer₀.ge⟩) ⟨Classical.arbitrary I,rfl⟩
  have size:a j/r.val≤(g r.val)^2:=booked.1
  constructor
  · have normed:∀i,‖r.val • X i‖≤M*r.val:=fun i=>by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos r.property.1,mul_comm M];exact mul_le_mul_of_nonneg_left (reach i) r.property.1.le
    exact WilsonMovingForkScreenedSites.actual R.family.S j m ref r.property.1 le_rfl X normed separated (margin _ dp.le (size.trans small))
  · intro y v b marked field
    let w:=fun i=>slot F (marked i) (chosen F J Z r.val ((books r).V (d (pick i))) (b i) (y (pick i)) (v (pick i)))
    have money:(∏i,Ascent.cost F (di i) r.val (w i)*(wilson z r.val)^(h i))≤
        ∏i,C i*(‖v (pick i)‖+‖y (pick i)‖):=prod_le_prod
      (fun i _=>mul_nonneg (Ascent.cost_pos F (di i) r.val (w i)) (pow_nonneg gp.le (h i)))
      (fun i _=>income i (books r) housed (y (pick i)) (v (pick i)) (b i) (marked i))
    have receipt:=sale ref w ((∏i,C i)*(∏i,(‖v (pick i)‖+‖y (pick i)‖))) (by simpa only [prod_mul_distrib,Finset.prod_pow_eq_pow_sum] using! money) _ dp size X separated
    exact receipt.trans_eq (by ring)

end YM.Integration.WilsonMeasuredPublicEntranceBookedStencil
end
