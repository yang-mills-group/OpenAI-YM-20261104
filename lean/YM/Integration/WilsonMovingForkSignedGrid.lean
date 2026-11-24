import YM.Integration.WilsonMovingForkPublicGrid

/-! Supported finite signed observations can each be heard on the actual
screened reporting sites with the same physical fields. Every interpolation
order is selected before the measured point set and its weights. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.WilsonMovingForkSignedGrid
open Function Filter Finset Set Metric Lattice Extraction Table Spec PhysMS Trace Trace.Pilot Climb
open GapsContact GapsContact.Ascent Contacts.Mat WilsonSeparatedGridDesign WilsonSeparatedBranchStencil WilsonSeparatedGridTree
open WilsonPositionHomogeneousFrame FVA2 FVA2.Register MS MS.Land RG17 PhysicalNext.Repeat.Legato
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonThermometerUnitFilingFourPoolClock (outer)
open WilsonMovingForkOpticalBook (reporter)
open scoped Classical Topology BigOperators
attribute [local instance] Trial.count
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
  {H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}{l:Ultrafilter (ℕ×ℕ)}
  (J:ℝ → tower S)(Z:WilsonPrescription G){I:Type}[Fintype I][Nonempty I]
local notation "a" => R.family.S.a

theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (lead:Leading F J)(owed:∀d,∀ᶠr in trail,Frame.obedient F H (J r) d)
    (D T B:ℕ)(d:I → Fin (D+1)){δ η M:ℝ}(ep:0<η)
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    {Kind:Type}[Fintype Kind](n:Kind→ℕ)(pick:∀k,Fin (n k)→I)(E:Type)[Fintype E](P:ℕ):
    ∃m:Kind→ℕ,∃C:Kind→ℝ,(∀k,0≤C k) ∧ ∀ᶠr in trail,∀rp:0<r,
    ∀ρ:I→{s:ℝ //0<s ∧ s<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z B r)→(∃i,(ρ i).val=r)→
      let j:=reporter F books ρ
      let dp:=div_pos (R.family.S.a_pos j) rp
      ∀v:∀i,Free R.family (d i).val,
      let fields:=fun i=>homogeneous F J Z (ρ i).val (d i).val (v i)
      ∀ref:E→E4,∀{J':Type}[Fintype J'],∀kind:J'→Kind,∀X:∀t,Points (n (kind t)),
      (∀t i,‖r • X t i‖≤M*outer z B r)→(∀t i k,i≠k→η≤dist (X t i) (X t k))→
      let book t:=sold (m (kind t)) ref dp (X t)
      let obs t x:=S.classMoment S (fun i=>(d (pick (kind t) i)).val) x (fun i=>fields (pick (kind t) i))
      ∃roots:∀t,(book t).sample→Fin (n (kind t))→ Cover,
      (∀t b,tag (a j) (roots t b)=r • (book t).site b ∧ tag (a j) (roots t b)∈generic _ ∧
         (∀i,‖R.family.S.gridPoint j (roots t b i)‖≤(M+1)*outer z B r) ∧
         Pairwise fun i k=>(η/2)*r≤‖R.family.S.gridPoint j (roots t b i)-R.family.S.gridPoint j (roots t b k)‖) ∧
      ∀μ:J'→ℂ,let coin t (b:(book t).sample):=μ t*((book t).weight b:ℂ)
      (∑t,∑b:(book t).sample,‖coin t b‖)≤∑t,‖μ t‖*(total (n (kind t)) (m (kind t)) E)^levels (n (kind t)) ∧
      ‖(∑t,μ t*obs t (r • X t))-∑t,∑b:(book t).sample,coin t b*obs t (tag (a j) (roots t b))‖≤
        ∑t,‖μ t‖*(C (kind t)*(∏i,‖v (pick (kind t) i)‖)*(wilson z r)^P):=by
  choose m C nonnegative acquired using fun k:Kind=>WilsonMovingForkPublicGrid.original F J Z
    simple bliss slow lead owed D T B d (M:=M) ep books (pick k) E P
  refine ⟨m,C,nonnegative,?_⟩
  filter_upwards [Filter.eventually_all.mpr acquired] with r shared
  intro rp ρ span home j dp v fields ref J' census kind X reach aside book obs
  have sale(t:J'):=shared (kind t) rp ρ span home (fun i=>v (pick (kind t) i)) ref (X t) (reach t) (aside t)
  choose roots situated generic _ wall clear using fun t b=>(sale t).2 b
  refine ⟨roots,fun t b=>⟨situated t b,generic t b,wall t b,clear t b⟩,?_⟩
  intro μ coin
  constructor
  · apply Finset.sum_le_sum;intro t _
    dsimp only [coin];simp_rw [norm_mul,Complex.norm_real];rw [←Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left ((WilsonSeparatedGridDesign.checked _ ref dp (X t)).2.1) (norm_nonneg _)
  · have pegs(t:J'):(∑b:(book t).sample,coin t b*obs t (tag (a j) (roots t b)))=
        μ t*read (book t) (fun x=>obs t (r • x)):=by
      unfold WilsonSeparatedBranchStencil.read;rw [Finset.mul_sum]
      apply Finset.sum_congr rfl;intro b _
      have here:tag (a j) (roots t b)=r • (book t).site b:=situated t b
      rw [here];simp only [coin,Complex.real_smul,mul_assoc]
    simp_rw [pegs];rw [←Finset.sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum;intro t _
    rw [←mul_sub,norm_mul]
    exact mul_le_mul_of_nonneg_left (sale t).1 (norm_nonneg _)

end YM.Integration.WilsonMovingForkSignedGrid
end
