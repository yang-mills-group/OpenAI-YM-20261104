import YM.Integration.WilsonPositionProgramCells
import YM.FVAAlt2.Sound.From

/-! The finite variable-block program and the independent position directory at the same
separated configuration. The original program uses its own finite warm history and period.
The uniform position estimate allows an independently chosen auxiliary mesh. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramFinite
open Function Filter Set Maxwell Lattice Precision RG PhysicalNext.Repeat.Legato
open RegulatorIR RegulatorIR.FVAAlt2 RegulatorIR.Oracle RegulatorIR.Calibration
open YM.FVAAlt2
open RegulatorIR.FVAAlt2.Lodge MS MS.Dial MS.Land MS.Rake MS.Tide MS.Fleet
open XSpace XSpace.Cirrus FVA2 FVA2.Register FVA2.Arrival
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
    {n : ℕ} (d : ℕ) (labels : Fin n → Dframe.Toon G d)
    (origin : X → Cover) (sites : Fin n → X → Cover)
    {A : Type} [Fintype A] [DecidableEq A] (mask : Marker.Census A) (mark : A)
local notation "pose" => (Tr).PoseT μ origin sites
local notation "xpos" => (fun a : X => points (fun j => MS.Theater.out.symm (testP pose a j)))

include matchMS book calibration in
theorem compared (l : Filter X) (before : ∀ x, p ≤ t x) (tends : Tendsto t l atTop)
    (head : (Tr).VenueT origin) (motion : MS.Tide.Profile (pose).profile sites)
    (valid : MS.Rake.Mesh (pose).profile (Fleet.info sites))
    (K₀ : Set (Points n)) (compact : IsCompact K₀) (clear : K₀ ⊆ conf n)
    (located : ∀ᶠ x in l, xpos x ∈ K₀) :
    ∃ σ : X → ℕ, ∃ W : Sound.From.Lecture Y branch C R t ht F μ origin sites mask mark p,
      ∀ (period : X → ℕ), (∀ᶠ x in l, σ x ≤ period x) → ∀ k ≤ p,
      ∃ A₁ A₂ : ℝ, 0 < A₁ ∧ 0 < A₂ ∧ ∃ i₀ : ℕ, ∀ᶠ x in l, ∀ i ≥ i₀, ∀ B (P : Handoff.Directory Z i B),
        Handoff.Directory.budget G n d + k ≤ B →
        ‖Sound.From.Reader Y branch C R t ht F p (Dframe.flash ∘ labels) Q μ period origin sites mask mark W k x -
          WilsonPositionProgramPoint.entry Z (T:=T) P d μ (draw (xpos x) (Z.run.step i)
            (river (Z.run.step i))) (Dframe.fill labels) k‖ ≤
        A₁ * Real.exp (-mildG * (Tr).Θ x) + A₂ * (Speed.chip (Z.run.step i) + (Z.run.step i).spacing) := by
  obtain ⟨σ,paid⟩ := Sound.guards (I:=Fin n) Y branch C R t ht F p d Q μ
  obtain ⟨W⟩ := Sound.From.inRoom Y branch C R t ht F p μ origin sites mask mark book
  refine ⟨σ,W,?_⟩
  intro per hper k hk
  have hs := Sound.finalT simple Y branch C R t ht F p d (Dframe.flash ∘ labels) Q M l μ per
    origin sites book before tends head motion valid paid hper
    (fun j => Nat.lt_succ_iff.mp (labels j).1.isLt) calibration k hk
  obtain ⟨A₁,pos₁,formal⟩ := hs.2
  obtain ⟨A₂,pos₂,aux⟩ := WilsonPositionProgramCells.compact Z matchMS d μ (Dframe.fill labels) k
    K₀ compact clear
  obtain ⟨i₀,tail⟩ := eventually_atTop.mp aux
  refine ⟨A₁,A₂,pos₁,pos₂,i₀,?_⟩
  filter_upwards [formal, located] with x h₁ hx
  intro i hi B P cap
  have h₂ := tail i hi B P cap (xpos x) hx
  rw [Dframe.ribbon] at h₂
  rw [Sound.From.daytime Y branch C R t ht F p (Dframe.flash ∘ labels) Q μ per
    origin sites mask mark book W x k hk]
  let v := tour M (Dframe.flash ∘ labels) μ (testP pose x) Finset.univ k
  change ‖_ - v‖ ≤ _ at h₁ h₂
  rw [norm_sub_rev] at h₂
  rw [← dist_eq_norm] at h₁ h₂ ⊢
  exact (dist_triangle _ v _).trans (add_le_add h₁ h₂)

end YM.Integration.WilsonPositionProgramFinite
end
