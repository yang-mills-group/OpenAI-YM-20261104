import YM.Integration.WilsonMovingForkHeterogeneousCut
import YM.Integration.WilsonMovingForkPublicGrid

/-! The complete true point observable from one normalized Wilson trial at
its literal screened sites. The last term is solely the independently
prescribed field's change from its own sampled array to its real position. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
noncomputable section
namespace YM.Integration.WilsonMovingForkGridHearing
open Function Filter Finset Set Metric Lattice Extraction Table Spec PhysMS Trace Trace.Pilot Climb
open GapsContact GapsContact.Ascent Contacts.Mat WilsonSeparatedGridDesign WilsonSeparatedGridTree WilsonSeparatedBranchStencil
open RG16 RG16.Literal RG17 FVA2 FVA2.Register MS MS.Land PhysicalNext.Repeat.Legato
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
  (J:ℝ → tower S)(Z:WilsonPrescription G){I:Type}[Fintype I][Nonempty I]
local notation "a" => R.family.S.a

theorem original (order:(l:Filter _) ≤ f.fuse)(simple:G.Simple)(bliss:Bliss F l z H)
    (slow:WilsonWindowReportingPace.Slow R.kit)(lead:Leading F J)(owed:∀d,∀ᶠr in trail,Frame.obedient F H (J r) d)
    (D T B:ℕ)(d:I → Fin (D+1)){δ η M:ℝ}(ep:0 < η)
    (books:(s:{s:ℝ // 0 < s ∧ s < δ}) → Book F (l:=l) H z D T s.val)
    {n:ℕ}(select:Fin n → I)(E:Type)[Fintype E](P:ℕ):
    ∃m:ℕ,∃C₀:ℝ,0 ≤ C₀ ∧ ∀ᶠr in trail,∀rp:0 < r,∀ρ:I → {s:ℝ // 0 < s ∧ s < δ},
      (∀i,r ≤ (ρ i).val ∧ (ρ i).val ≤ outer z B r) → (∃i,(ρ i).val=r) →
      let j:=reporter F books ρ
      let dp:=div_pos (R.family.S.a_pos j) rp
      let di:=fun i=>(d (select i)).val
      ∀x:(i:Fin n) → Free R.family (di i),∀weak:Fin n → Bool,
      let v:=fun i=>homogeneous F J Z (ρ (select i)).val (di i) (x i)
      let book:=fun i=>(books (ρ (select i))).rows (d (select i))
      let arms:=fun i=>(book i).arm (weak i) (v i)
      ∀K:ℕ,∀jK:j ≤ K,∀b:Filed R di K,(∀i,b.station i=station F (book i) (weak i)) →
      ∀u t c:ℕ,∀uj:u ≤ j,∀ut:u ≤ t,∀tc:t ≤ c,∀ck:c ≤ K,
      ∀pred:Points n → ℂ,∀phase:ℝ,∀w:Invoice,0 ≤ phase+w.total t c K →
      let good:=fun o:Fin n → Cover=>(∀i,‖R.family.S.gridPoint j (o i)‖ ≤ (M+1)*outer z B r) ∧
        (Pairwise fun i k=>(η/2)*r ≤ ‖R.family.S.gridPoint j (o i)-R.family.S.gridPoint j (o k)‖)
      (∀o,good o → ∀N per,∀top:j < N,‖gap R N per u (uj.trans top.le)
        (word R di j N per top.le o (fun i=>(arms i).source (N,per)))‖ ≤ phase) →
      (∀o,good o → Heard (f:=f) b ut tc ck jK arms o pred w) →
      ∀ref:E → E4,∀X:Points n,(∀i,‖r • X i‖ ≤ M*outer z B r) → (∀i k,i≠k → η ≤ dist (X i) (X k)) →
      let prog:=sold m ref dp X
      let values:=fun y:Points n=>pred (r • y)
      (∀N per, K < N → ∀i,
        b.A N per i (WilsonMovingForkMixedSeed.doses R di b.station (N:=N) (per:=per) (b.A N per)
          (fun h=>(arms h).source (N,per)) i)=WilsonOriginalMicroscopicGuardedPage.full R (di i) N per
          (station F (book i) (weak i)) ((arms i).source (N,per))) ∧
      ‖S.classMoment S di (r • X) v-pred (r • X)‖ ≤ C₀*(∏i,‖x i‖)*(wilson z r)^P+
        (total n m E)^levels n*(phase+w.total t c K)+‖read prog values-values X‖:=by
  obtain ⟨m,H₀,hn,nodes⟩:=WilsonMovingForkPublicGrid.original F J Z simple bliss slow lead owed D T B d ep books select E P (M:=M)
  refine ⟨m,H₀,hn,?_⟩
  filter_upwards [nodes] with r stock
  intro rp ρ span anchor j dp di x weak v book arms K jK b orig u t c uj ut tc ck pred phase w pn good oldest signed ref X reach apart prog values
  obtain ⟨truth,placements⟩:=stock rp ρ span anchor x ref X reach apart
  constructor
  · intro N per live i
    rw [←orig i]
    exact WilsonMovingForkMixedSeed.page R di (fun i=>(b.before i).trans live.le) (b.A N per) (fun h=>(arms h).source (N,per)) i
  let field:=fun y:Points n=>S.classMoment S di (r • y) v
  have pernode:∀k:prog.sample,‖field (prog.site k)-values (prog.site k)‖ ≤ phase+w.total t c K:=by
    intro k
    obtain ⟨o,eq,gen,_,home,gaps⟩:=placements k
    have bound:=WilsonMovingForkHeterogeneousCut.site b F order uj jK ut tc ck arms o gen pred phase w
      (oldest o ⟨home,gaps⟩) (signed o ⟨home,gaps⟩)
    dsimp [field,values]
    rw [←eq]
    exact bound
  have compare:=WilsonMovingForkHeterogeneousCut.finite prog field values _ pernode
  have fee:=((checked m ref dp X).2.1)
  have tri(p q s:ℂ):‖p-s‖ ≤ ‖p-q‖+‖q-s‖:=by simpa only [dist_eq_norm] using dist_triangle p q s
  have analytic:‖field X-read prog field‖ ≤ H₀*(∏i,‖x i‖)*(wilson z r)^P:=truth
  have cap:bill prog ≤ (total n m E)^levels n:=fee
  change ‖field X-values X‖ ≤ _
  linarith only [tri (field X) (read prog field) (values X),tri (read prog field) (read prog values) (values X),
    analytic,compare,mul_le_mul_of_nonneg_right cap pn]

end YM.Integration.WilsonMovingForkGridHearing
