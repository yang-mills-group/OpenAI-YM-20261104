import YM.Integration.WilsonMovingForkScreenedSites
import YM.Integration.WilsonMovingForkOpticalBook
import YM.Integration.WilsonOriginalTwoFlatPublicMixedMesh

/-! Actual original moving grid for every enrolled subroster of one elected
public book. Sample nodes and interpolation weights are shared by all
weak/pooled corners; the common date still sees the unselected marks. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.Integration.WilsonMovingForkPublicGrid
open Function Filter Finset Set Metric Lattice Extraction Table Spec PhysMS Trace Trace.Pilot Climb
open GapsContact GapsContact.Ascent Contacts.Mat WilsonSeparatedGridDesign WilsonSeparatedBranchStencil
open WilsonPositionHomogeneousFrame FVA2 FVA2.Register MS MS.Land RG17 PhysicalNext.Repeat.Legato
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonThermometerUnitFilingFourPoolClock (outer)
open WilsonMovingForkOpticalBook (reporter)
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
  {H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}{l:Ultrafilter (ℕ×ℕ)}
  (J:ℝ → tower S)(Z:WilsonPrescription G){I:Type}[Fintype I][DecidableEq I][Nonempty I]
local notation "a" => R.family.S.a

omit [DecidableEq I] in
theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (lead:Leading F J)(owed:∀d,∀ᶠr in trail,Frame.obedient F H (J r) d)
    (D T B:ℕ)(d:I → Fin (D+1)){δ η M:ℝ}(ep:0 < η)
    (books:(s:{s:ℝ // 0 < s ∧ s < δ}) → Book F (l:=l) H z D T s.val)
    {n:ℕ}(select:Fin n → I)(E:Type)[Fintype E](P:ℕ):
    ∃m:ℕ,∃K:ℝ,0 ≤ K ∧ ∀ᶠr in trail,∀rp:0 < r,∀ρ:I → {s:ℝ // 0 < s ∧ s < δ},
      (∀i,r ≤ (ρ i).val ∧ (ρ i).val ≤ outer z B r) → (∃i,(ρ i).val=r) →
      let j:=reporter F books ρ
      let dp:=div_pos (R.family.S.a_pos j) rp
      let di:=fun i=>(d (select i)).val
      ∀u:(i:Fin n) → Free R.family (di i),∀ref:E → E4,∀X:Points n,
      (∀i,‖r • X i‖ ≤ M*outer z B r) → (∀i k,i≠k → η ≤ dist (X i) (X k)) →
      let prog:=sold m ref dp X
      let field:=fun x:Points n=>S.classMoment S di (r • x) (fun i=>homogeneous F J Z (ρ (select i)).val (di i) (u i))
      ‖field X-read prog field‖ ≤ K*(∏i,‖u i‖)*(wilson z r)^P ∧
      ∀s:prog.sample,∃o:Fin n → Cover,tag (a j) o=r • prog.site s ∧
        tag (a j) o∈generic n ∧ tag (a j) o∈conf n ∧
        (∀i,‖R.family.S.gridPoint j (o i)‖ ≤ (M+1)*outer z B r) ∧
        (Pairwise fun i k=>(η/2)*r ≤ ‖R.family.S.gridPoint j (o i)-R.family.S.gridPoint j (o k)‖):=by
  let di:=fun i=>(d (select i)).val
  obtain ⟨m,K,kn,paid⟩:=WilsonMovingForkOpticalQuadrature.original F J Z simple bliss lead owed di ep B P E
  obtain ⟨Δ,positive,fits⟩:=WilsonMovingForkScreenedSites.margin ep m n E
  have hg:=wilson_link F simple bliss.budgets bliss.keen bliss.lies
  have small:=((hg.conforms simple).pow 2).eventually (ge_mem_nhds (by simpa using positive: (0:ℝ)^2 < Δ))
  refine ⟨m,K,kn,?_⟩
  filter_upwards [paid,small,WilsonOriginalTwoFlatPublicMixedMesh.original F simple bliss slow D T B d books]
    with r quad low mesh
  intro rp ρ span anchor j dp di' u ref X reach separate prog field
  have sale:=mesh ρ span anchor
  have grid:a j/r ≤ (wilson z r)^2:=sale.1
  have outer_id:outer z B r=r/(wilson z r)^B:=by simp only [outer,div_eq_mul_inv,inv_pow]
  have near:r ≤ outer z B r:=(span (Classical.arbitrary I)).1.trans (span _).2
  refine ⟨quad ref (fun i=>(ρ (select i)).val)
    (fun i=>by simpa only [←outer_id] using span (select i)) u _ dp grid X separate,?_⟩
  exact WilsonMovingForkScreenedSites.actual R.family.S j m ref rp near X reach separate
    (fits _ dp.le (grid.trans low))

end YM.Integration.WilsonMovingForkPublicGrid
