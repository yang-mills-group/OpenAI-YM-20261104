import YM.Integration.WilsonThermometerIndividualSourceWallet

/-! Individual wages for the literal three Wilson arms, with every grade, angular path and real test on their original bare school. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerWardIndividualScene
open Function Filter Finset Lattice Wilson RG Source Labels Marker QuadraticLocal Earn Sunrise QuadraticLocal.Affinity
open FVA1 Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress Next.Rank Next.Rank.East
open MergeProof MergeProof.East MergeProof.Accent Next.Rank.Price PhysicalNext.Repeat.Legato
open WilsonOriginalStarSceneWords WilsonOriginalStarSceneRows WilsonOriginalStarSceneRent
open WilsonOriginalThermometerPalette
open WilsonThermometerWardBareScene WilsonThermometerIndividualSourceWallet
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) (dim:Fin 3→ℕ) (N p:ℕ) (o:Fin 3→Site (R.family.side N p))
  (v:(j:Fin 3)→R.family.label (dim j))
local notation "C" => R.family
local notation "J" => Stock.census (Fin 3)
local notation "g" => Pert.Asymptotics.regulatorRun (C) N p N
local notation "rep" => (C).path.rep N p N
local notation "coins" => (fun j=>awake (C) (dim j) N N p (v j))

theorem purchased (pos:∀j,0<dim j) (σ Ω:ℝ) (one:1≤Ω)
    (order count shelf stage vac coarse:ℕ) (slots:3≤count) (space:∑j,dim j ≤ shelf)
    (fit:maximum R dim≤order) (room:order+1 ≤ stage) (future:order≤coarse) (stamp:∀j,dim j≤coarse)
    (cover:order+shelf≤AllOrder.Burn.horizon vac+2) :
    let A:=aperture R dim coins σ Ω
    let w:=fun j=>(A j)⁻¹
    let M:=models R dim N p o v σ pos
    Scene.Armada M w dim σ Ω⁻¹ order count shelf ∧ Mentor.Cruise.Voter M σ order count stage vac coarse ∧
      Tableau WilsonThermometerCourseHearing.sectors disks M ∧
      ∀s:(J).Mode,Poly.toll w s*(∏j∈s.val,A j)=1:=by
  intro A w M
  have non:∀j,0<A j:=fun j=>zero_lt_one.trans_le (funded R dim coins σ Ω one j)
  have setup:(rep).p=(C).path.levels.budget N:=(R.makes.wilson.represents N p N le_rfl).vac
  have band:g≤2*(rep).p.threshold:=by
    rw [setup]
    exact (RG04B.thresholdHat R.makes (p:=p) (le_rfl (a:=N))).2
  have fee:=billable R dim coins σ Ω g (rep).p.threshold one
    (ActualRunKernelPackets.regulator_pos R N p N le_rfl).le (rep).p.threshold_pos band
  have X:=WilsonOriginalStarGradedScene.fleet R dim o σ g (rep).p.threshold coins probe pos w
    (fun j=>inv_pos.mpr (non j)) (fun j x=>(x j).property) order count shelf fit
    (by simpa using slots) space
  refine ⟨X.higher fee,⟨fun i=>?_,X.quota,room,fun club=>?_⟩,?_,fun s=>?_⟩
  · exact ⟨X.honor _,X.purchases.spend _,((X.purchases.usable i).1).trans future,stamp _⟩
  · rw [Press.tall M club dim X.purchases.usable]
    exact (Nat.add_le_add_left (X.crew _) _).trans cover
  · exact ⟨fun i=>(WilsonOriginalStarSceneMasked.tests R dim o σ g (rep).p.threshold coins _ _ probe
      WilsonOriginalThermometerRealPalette.attentive).bill i⟩
  · change (∏j∈s.val,(A j)⁻¹)*(∏j∈s.val,A j)=1
    rw [prod_inv_distrib,inv_mul_cancel₀ (prod_ne_zero_iff.mpr (fun j _=>(non j).ne'))]

end YM.Integration.WilsonThermometerWardIndividualScene
