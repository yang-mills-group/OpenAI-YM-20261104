import YM.Integration.WilsonPositionProgramFinite
import YM.Integration.WilsonPositionProgramFixedFrame

/-! The real original chronological program supplies one MS basis table at every finite
order. Applying the one filed position change to this table uses one common program and
period before the source positions and their independently calibrated field tensors are read. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramConvertedRun
open Function Filter Set Finset Maxwell Lattice Precision RG PhysicalNext.Repeat.Legato
open RegulatorIR RegulatorIR.FVAAlt2 RegulatorIR.Oracle RegulatorIR.Calibration
open YM.FVAAlt2
open RegulatorIR.FVAAlt2.Lodge MS MS.Dial MS.Land MS.Rake MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus FVA2 FVA2.Register FVA2.Arrival FVA2.Scale
open WilsonPositionProgramFixedFrame
open scoped BigOperators Classical Topology
set_option quotPrecheck false
variable {G : Gauge} (Z : WilsonPrescription G) {simple : G.Simple}
    {M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {T : Prescription (Press.portDeck G)} {dial : Bool} (matchMS : Main.Match Z simple M T dial)
    {K : KernelChoices} {X : Type} (Y : RegulatorIR.Oracle.Program K)
    (branch : ∀ P : RG.Patch, P.Branches K G) (C : Run G) (R : Lodge.Contract C Y branch)
    (t : X → ℕ) (ht : ∀ x, R.floor Y branch C ≤ t x) (μ : ℝ) (p : ℕ)
local notation "Tr" => R.profile Y branch C t ht
variable (F : RegulatorIR.Calibration.Tent (R.profile Y branch C t ht).entire) {color : G.ColorIndex}
    (book : RegulatorIR.Calibration.Notebook (R.profile Y branch C t ht).desk Y G branch color
      (Rocket.native (R.profile Y branch C t ht).entire) F p)
    (Q : Prescription (Press.portDeck G)) (calibration : TaylorOKPl M (Lobby.Table (basisR C) (Press.portDeck G)) Q)
    {n : ℕ} (d : ℕ) (origin : X → Cover) (sites : Fin n → X → Cover)
    {A : Type} [Fintype A] [DecidableEq A] (mask : Marker.Census A) (mark : A)
local notation "pose" => (Tr).PoseT μ origin sites
local notation "xpos" => (fun a : X => points (fun j => MS.Theater.out.symm (testP pose a j)))

include matchMS book calibration in
theorem original (l : Filter X) (before : ∀ x, p ≤ t x) (tends : Tendsto t l atTop)
    (head : (Tr).VenueT origin) (motion : MS.Tide.Profile (pose).profile sites)
    (valid : MS.Rake.Mesh (pose).profile (Fleet.info sites)) :
    ∃ σ : X → ℕ, ∃ W : Sound.From.Lecture Y branch C R t ht F μ origin sites mask mark p,
      ∀ (period : X → ℕ), (∀ᶠ x in l, σ x ≤ period x) → ∀ k ≤ p, ∀ v : Tags G d n,
      ∃ D : ℝ, 0<D ∧ ∀ᶠ x in l, ∀ hx : xpos x ∈ conf n,
        ‖value Z (M:=M) μ v k (fun labels j=>Sound.From.Reader Y branch C R t ht F p
          (Dframe.flash ∘ labels) Q μ period origin sites mask mark W j x) -
          Measure.outlook Z.scheme Z.criterion d n ⟨xpos x,hx⟩ k v‖ ≤
          D * Real.exp (-mildG * (Tr).Θ x) := by
  obtain ⟨σ,paid⟩ := Sound.guards (I:=Fin n) Y branch C R t ht F p d Q μ
  obtain ⟨W⟩ := Sound.From.inRoom Y branch C R t ht F p μ origin sites mask mark book
  refine ⟨σ,W,?_⟩
  intro per hper k hk v
  have base (z : Fin n → Dframe.Toon G d) (j : Fin (k+1)) :
      ∃ D : ℝ, 0<D ∧ ∀ᶠ x in l,
        ‖Sound.From.Reader Y branch C R t ht F p (Dframe.flash ∘ z) Q μ per origin sites mask mark W j x -
          Dframe.meteor μ M d (xpos x) j (Dframe.fill z)‖ ≤ D * Real.exp (-mildG * (Tr).Θ x) := by
    have hp : (j:ℕ) ≤ p := by omega
    have raw := Sound.finalT simple Y branch C R t ht F p d (Dframe.flash ∘ z) Q M l μ per
      origin sites book before tends head motion valid paid hper
      (fun a => Nat.lt_succ_iff.mp (z a).1.isLt) calibration j hp
    obtain ⟨D,pos,epoch⟩ := raw.2
    refine ⟨D,pos,?_⟩
    filter_upwards [epoch] with x h
    rw [Sound.From.daytime Y branch C R t ht F p (Dframe.flash ∘ z) Q μ per
      origin sites mask mark book W x j hp,Dframe.ribbon]
    exact h
  choose D pos data using base
  let total := ∑ z,∑ j,D z j
  have nonneg : 0≤total := sum_nonneg fun z _=>sum_nonneg fun j _=>(pos z j).le
  have bound (z) (j) : D z j≤total := (single_le_sum (f:=D z) (fun i _=>(pos z i).le) (mem_univ j)).trans
    (single_le_sum (f:=fun u=>∑ i,D u i) (fun u _=>sum_nonneg fun i _=>(pos u i).le) (mem_univ z))
  have cash : 0 ≤ fee Z (M:=M) μ v k := sum_nonneg fun _ _=>sum_nonneg fun _ _=>sum_nonneg fun _ _=>norm_nonneg _
  refine ⟨1+fee Z (M:=M) μ v k*total,by positivity,?_⟩
  filter_upwards [eventually_all.mpr (fun z=>eventually_all.mpr (fun j=>data z j))] with x all
  intro hx
  rw [←output Z matchMS μ v k ⟨xpos x,hx⟩]
  refine (priced Z (M:=M) μ v k (E:=total*Real.exp (-mildG*(Tr).Θ x)) ?_).trans ?_
  · intro z j hj
    have fit : j<k+1 := by omega
    exact (all z ⟨j,fit⟩).trans (mul_le_mul_of_nonneg_right (bound z ⟨j,fit⟩) (Real.exp_pos _).le)
  · rw [←mul_assoc]
    exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

end YM.Integration.WilsonPositionProgramConvertedRun
