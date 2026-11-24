import YM.Integration.WilsonOriginalPublicNodalSeed
import YM.Integration.WilsonViewerAlignedPublic

/-! Each finite public Schwinger pin is the genuine Wilson cutoff product at
the same embedded sites as its finite restarted trial. The price separates
the physical phase, the signed joint entrance, the returned filed primitives
and the independent change into the common positioned source coordinates. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalOrdinaryPinExpense
open Filter Set Function Finset Lattice Wilson RG Source Labels MeasureTheory PhysicalNext.Repeat.Legato
open Pert.Asymptotics RegulatorIR.FVAAlt2 XSpace XSpace.Normalize XSpace.Rose XSpace.Cirrus
open Extraction Table Spec OPE OPE.Orbits Climb Trace.Pilot Next.UVStress PhysMS Maxwell
open FVA2 FVA2.Register FVA2.Scale MS MS.Land MS.Fleet
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonMovingForkMixedSeed (doses product)
open WilsonMovingForkSeededPoint (seats)
open WilsonOriginalTwoFlatGridCapture (word)
open WilsonOriginalPublicPivotReflected (board evaluated)
open WilsonOriginalPublicNodalSeed (vector signed)
open WilsonThermometerUnitFilingCoarse (reading)
open WilsonThermometerUnitFilingFlatTelescope (numerator)
open WilsonThermometerWeakMeasuredSeries WilsonPositionHomogeneousFrame
open WilsonViewerGridPins WilsonViewerAlignedResidual WilsonViewerElectedHierarchy
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) (W:Initialize G) {n:ℕ} (d:Caps n)
  (Y:(ℕ×ℕ) → R.family.book.Vector d) {s K N per u:ℕ}
  (file:Filed R d K) (sk:s≤K) (kn:K≤N) (uk:u≤K)
  (o:Fin n → Cover) (pt:Sample n)
local notation "source" => word R d s N per (sk.trans kn) o (Y (N,per))
local notation "pin" => seats (R:=R) sk per o
local notation "weights" => doses R d file.station (N:=N) (per:=per) (file.A N per) (Y (N,per))
local notation "plant" => product R d (N:=N) pin weights
local notation "loan" => vector R d (N:=N) (per:=per) file (Y (N,per))
local notation "g₀" => regulatorRun R.family N per K

theorem literal :
    atCut (R:=R) d s o Y (N,per)=R.family.omega N per source := by
  simp only [atCut,Cells.location,dif_pos (sk.trans kn)]
  rfl

def price (q:ℕ) (target:ℂ) : ℝ :=
  ‖WilsonOriginalTwoFlatGridScaling.gap R N per u (uk.trans kn) source‖+
  ‖reading R (N:=N) (RG16.Literal.credit R.family N per 0 source K kn) u uk-
    reading R (N:=N) (numerator R N per K plant) u uk‖+
  ‖signed R W d (N:=N) (per:=per) file (Y (N,per)) uk pt q‖+
  ‖evaluated q g₀ (board R W d loan pt univ)-target‖

theorem finite (placed:∀ i,wrap (R.family.side K per) (pt.layout i)=pin i) (q:ℕ) (target:ℂ) :
    ‖atCut (R:=R) d s o Y (N,per)-target‖≤price R W d Y (per:=per) file sk kn uk o pt q target := by
  have sale:= (WilsonOriginalPublicNodalSeed.original R W d file (Y (N,per)) sk kn uk o pt placed q le_rfl).2
  rw [literal R d Y sk kn o]
  unfold price
  set O:=R.family.omega N per source
  set I:=evaluated q g₀ (board R W d loan pt univ)
  set E:=signed R W d (N:=N) (per:=per) file (Y (N,per)) uk pt q
  calc
    ‖O-target‖ ≤ ‖O-I‖+‖I-target‖:=norm_sub_le_norm_sub_add_norm_sub .. 
    _ ≤ _ := add_le_add (by
      have middle:=norm_sub_le_norm_sub_add_norm_sub (O-I) E 0
      simp only [sub_zero] at middle
      exact middle.trans (add_le_add sale le_rfl)) le_rfl

variable {f:Extraction.Order} {S:Table R.family.book} {ℓ:Ultrafilter (ℕ×ℕ)} (F:Final R.family f S)
  (J:ℝ→tower S) (Z:WilsonPrescription G) {simple:G.Simple}
  (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
  {σ:Prescription (Press.portDeck G)} {dial:Bool} (ms:Main.Match Z simple M σ dial)
  (ν:ℝ) {H:ℕ} (v:MaxwellSlots R.family d) (within:∀i,d i≤H)
  (P:Report F ℓ H (WilsonPositionHomogeneousFrame.reading F J Z)) (W₀:Finset E4)
local notation "rows" r:max => fun z i => (P.rows r).field ⟨d i,Nat.lt_succ_of_le (within i)⟩ z
  ((homogeneous F J Z r) (d i) (v i))
local notation "dict" r:max y:max k:max q:max => WilsonViewerGridMS.read Z M ms ν (commonCaps v within) q
  (WilsonPositionHomogeneousFrame.reading F J Z r) y k

/-- The restart, stored complete matrices and internal order are elected once
for the whole compact position panel at each radius. Original regulator limits
keep their stated order. The independent chart uses its own board on that pin. -/
theorem original (p q:ℕ)
    (cash:∀ K₀,IsCompact K₀→K₀⊆conf n→∃ C:ℝ,0≤C ∧ ∀ᶠ r in trail,
      ∃ (K u depth:ℕ) (file:Filed R d K) (sk:P.grid.date r≤K) (uk:u≤K),
        ∀ o y, y∈K₀→Pin R.family.S W₀ r (P.grid.date r) o y→
          ∃ᶠ k:ℕ in atTop, f.late fun N per=>∃ (kn:K≤N) (pt:Sample n),
            (∀ i,wrap (R.family.side K per) (pt.layout i)=seats (R:=R) sk per o i) ∧
            price R W d (rows r) (per:=per) file sk kn uk o pt depth (dict r y k q) ≤
              C*(WilsonPositionHomogeneousFrame.reading F J Z r)^p):
    PinBill Z M ms ν v within P W₀ p q := by
  intro K₀ compact clear
  obtain ⟨C,C₀,bought⟩:=cash K₀ compact clear
  refine ⟨C,C₀,?_⟩
  filter_upwards [bought] with r rows_bought o y member pinned
  obtain ⟨K,u,depth,file,sk,uk,filled⟩:=rows_bought
  apply (filled o y member pinned).mono
  intro k ears
  unfold Extraction.Order.late at ears ⊢
  filter_upwards [ears] with per issued
  filter_upwards [issued] with N bill
  obtain ⟨kn,pt,placed,paid⟩:=bill
  exact (finite R W d (rows r) (per:=f.per.choose per) file sk kn uk o pt placed depth _).trans paid

end YM.Integration.WilsonPhysicalOrdinaryPinExpense
end

