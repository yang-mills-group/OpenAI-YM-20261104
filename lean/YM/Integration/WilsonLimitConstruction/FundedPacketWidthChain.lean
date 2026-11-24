import YM.Integration.FullQLocalProfileAllocation
import YM.Integration.WilsonLimitConstruction.FundedPresoldPacketWidths

/-! Allocate every finite native component diagram with the same prescribed
packet ceiling on both sides of each edge. All choices precede the original
length, cutoff, and physical period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedPacketWidthChain
open Lattice RG RG.Supply Precision PhysicalNext.Repeat.Legato
open FullQLocal FullQLocal.PreRun.Profile
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Cadenza
variable {G : Gauge} {s : Sheet G} {q : MapPrices} {native : NativeComponentRecipe.Choice s}

def meet (P Q : ProfileWidths) : ProfileWidths where
  width i := min (P.width i) (Q.width i)
  positive i := lt_min (P.positive i) (Q.positive i)

variable (D : ℕ→Diagram s q native) (H : ℕ→ProfileWidths)

def ceiling (n : ℕ) := meet (D (n+1)).inputStrip (meet (H n) (H (n+1)))

def components (n : ℕ) : ComponentAllocation (D n) := (components_below (D n) (ceiling D H n)).choose

theorem exit (n i : ℕ) :
    ((components D H n).component (D n).output).width i≤(ceiling D H n).width i :=
  (components_below (D n) (ceiling D H n)).choose_spec i

def inlet : ℕ→ProfileWidths
  | 0 => meet (D 0).inputStrip (H 0)
  | n+1 => (components D H n).component (D n).output

theorem fits (n i : ℕ) : (inlet D H n).width i≤(D n).inputStrip.width i := by
  cases n with
  | zero => exact min_le_left _ _
  | succ n => exact (exit D H n i).trans (min_le_left _ _)

def allocation (n : ℕ) : Allocation (D n) where
  input := inlet D H n
  component := (components D H n).component
  input_strip := fits D H n
  component_strip := (components D H n).component_strip
  same_mesh := (components D H n).same_mesh

theorem swap (n : ℕ) : (allocation D H n).output=(allocation D H (n+1)).input := rfl

theorem before (n i : ℕ) : (allocation D H n).input.width i≤(H n).width i := by
  cases n with
  | zero => exact min_le_right _ _
  | succ n => exact (exit D H n i).trans ((min_le_right _ _).trans (min_le_right _ _))

theorem after (n i : ℕ) : (allocation D H n).output.width i≤(H n).width i :=
  (exit D H n i).trans ((min_le_right _ _).trans (min_le_left _ _))

theorem target (n : ℕ) (C : Family G) (m : ℕ) :
    (allocation D H n).target C m≤(H n).width (C.path.levels.clock.J m) := by
  have meet_le : (allocation D H n).target C m ≤ (allocation D H n).output.pair C (m-1) := min_le_left _ _
  cases m with
  | zero => exact meet_le.trans ((min_le_right _ _).trans (after D H n _))
  | succ m => exact meet_le.trans ((min_le_left _ _).trans (after D H n _))

end YM.Integration.WilsonLimitConstruction.FundedPacketWidthChain
end
