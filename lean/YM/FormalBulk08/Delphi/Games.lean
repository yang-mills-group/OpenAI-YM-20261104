import YM.FormalBulk08.First.Dollars
import YM.FormalBulk08.Sierra.Here
import YM.FormalBulk08.Copula.Bill

/-! Issuance for polymer marks (supplemental). No phase regress among
new powers. Length schedule using even unchanged J. Smoothing-order tests
in Ft.(Kgraph) STILL from primary footprint. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Delphi
open Lattice Laurent Bloch Precision Stationary RG Wilson Filter Function
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix
open Next.Free Reef Flat Dove Dove.Lab North Elm Spigot Aster Source Drops Labels
open RG.Supply Push.PriceCompiler Borough Sable Tundra Sierra
variable {X:Type}{G:Gauge}{K:KernelChoices}{W:Borough.Window G K}{F:∀ d,Frame G d}{H:Hol G}{ρ:ChartRatio G}{Q:Herald}{Y:Sheet G}{P:Rolls Y}{T:Protection P}{V:Delays T}{A:Levels G}
variable {U:Empire G K X}{i j e r l u D E R d:ℕ}
-- any stipulated FINITE powers at a stage.
section
variable (Z:Frame G d)(H K)
def Good (d D u j t:ℕ) := d < D ∧ (d+1)*(d+1)≤ u ∧ 4≤j ∧ d+1≤j-2∧4≤t deriving Decidable

def perCap (D E R u j t:ℕ)(o:Loc G 1):ℝ:= if h:Good d D u j t then (preCairn K Z H o D E R u j t h.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2 h.2.1).choose else 0
lemma cairn_up {j t:ℕ}(h:Good d D u j t)(o:Loc G 1):0≤ perCap K H Z D E R u j t o ∧ Cairn K Z o D E R u j t (perCap K H Z D E R u j t o):= by rw [perCap,dif_pos h]; exact (preCairn K Z H o _ _ _ _ _ _ h.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2 h.2.1).choose_spec
-- implicit H variable order

def burrow (D E R u j t:ℕ)(o:Loc G 1) (P:Patch)(V:Lodge P):ℝ:= if h: Good d D u j t ∧ perCap K H Z D E R u j t o ≤ (P.L.val:ℝ) then ((cairn_up K H Z (D:=D) (u:=u) (j:=j) (t:=t) h.1 o).2 P h.2 V).choose else 0
lemma buried_up {t j:ℕ}(o:Loc G 1) (P:Patch)(V:Lodge P)(h:Good d D u j t)(ht: perCap K H Z D E R u j t o ≤ (P.L.val:ℝ)): Buried K Z o D E R u j t P V (burrow K H Z D E R u j t o P V):= by rw [burrow,dif_pos ⟨h,ht⟩]; exact ((cairn_up K H Z h o).2 P ht V).choose_spec
end
section
variable (G K)
def skirtV (u R E j t:ℕ):ℝ:= if h: 4≤j ∧ 4≤t then (hill_rests u R E G K h.1 h.2).choose else 0
lemma skirts {t j:ℕ} (h:4≤j)(he:4≤t):∀ P: Patch,skirtV G K u R E j t≤ (P.L.val:ℝ) →∀ V:Lodge P,∃ B:ℝ,Hearth K P V u R E j t G B:= by rw [skirtV,dif_pos ⟨h,he⟩];exact (hill_rests u R E G K h he).choose_spec.2

def tracks (u R E j t:ℕ)(P:Patch)(V:Lodge P):ℝ:= if h:(4≤j∧ 4≤t)∧skirtV G K u R E j t≤ (P.L.val:ℝ) then (skirts G K h.1.1 h.1.2 P h.2 V).choose else 0
lemma tracts {j t:ℕ}(P:Patch)(V:Lodge P)(h:4≤j)(hp:4≤t)(he:skirtV G K u R E j t≤(P.L.val:ℝ)): Hearth K P V u R E j t G (tracks G K u R E j t P V):= by rw [tracks,dif_pos ⟨⟨h,hp⟩,he⟩];exact (skirts G K h hp P he V).choose_spec
end
end YM.FormalBulk08.Delphi
