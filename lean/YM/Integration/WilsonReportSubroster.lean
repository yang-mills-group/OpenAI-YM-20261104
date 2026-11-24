import YM.Integration.WilsonMovingReportDisplacement
import YM.Integration.WilsonReportMomentDifference

/-! Each subset of physical insertions uses its original calibrated labels,
actual torus positions and Wilson law, in one fixed enumeration. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportSubroster
open Function Finset Filter Set Metric Lattice Wilson RG Source Marker Extraction Spec
open PhysicalNext.Repeat.Legato RG17 FullVolume
open scoped Classical BigOperators Topology
variable {n : ℕ}

abbrev count (s : Finset (Fin n)) := Fintype.card (↑s)
def order (s : Finset (Fin n)) : Fin (count s) ≃ ↑s := (Fintype.equivFin _).symm
def pick (s : Finset (Fin n)) (j : Fin (count s)) : Fin n := (order s j).val

theorem count_le (s : Finset (Fin n)) : count s≤n := by
  simpa only [count,Fintype.card_coe,Fintype.card_fin] using (Finset.card_le_univ s)

def window (s : Finset (Fin n)) (x : Points n) : Points (count s) :=
  points fun j=>x (pick s j)

theorem continuous_window (s : Finset (Fin n)) : Continuous (window s) :=
  (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i=>PiLp.continuous_apply 2 _ (pick s i))

theorem geometric (s : Finset (Fin n)) {K : Set (Points n)} (hk : IsCompact K) (sep : K⊆conf n) :
    IsCompact (window s '' K) ∧ window s '' K ⊆ conf (count s) := by
  refine ⟨hk.image (continuous_window s),?_⟩
  rintro _ ⟨x,hx,rfl⟩
  exact (sep hx).comp (Subtype.val_injective.comp (order s).injective)

theorem coordinates (s : Finset (Fin n)) (r t : ℝ) (z : Positions n) :
    r • tag t (z ∘ pick s) = window s (r • tag t z) := rfl

def all (s : Finset (Fin n)) : Census (Fin (count s)) where
  choices := univ
  blank := mem_univ _
  solo _ := mem_univ _
  down _ _ _ := mem_univ _

variable {G : Gauge} {C : Family G} {N p : ℕ}

theorem actual (s : Finset (Fin n)) (d : Caps n) (v : (j:Fin n)→C.label (d j))
    (z : Fin n→Site (C.side N p)) :
    moment (C.beta N p) (fun U=>∏ j∈s,C.O N p (v j) (z j) U) =
    C.numeric N p (fun j=>⟨d (pick s j),v (pick s j)⟩) (z ∘ pick s) := by
  change moment _ _ = moment _ (fun U=>∏ j:Fin (count s),C.O N p (v (pick s j)) (z (pick s j)) U)
  congr 1; funext U
  rw [Finset.prod_subtype s (fun _=>Iff.rfl) (fun j=>C.O N p (v j) (z j) U)]
  exact Fintype.prod_equiv (order s).symm _ _ (fun j=>
    congrArg (fun a : ↑s=>C.O N p (v a.val) (z a.val) U) ((order s).apply_symm_apply j).symm)

theorem raw {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    {F : Spec.Final R.family f S} (L : Layout F) (r:ℝ)
    (s : Finset (Fin n)) (d : Caps n) (w : R.family.book.Vector d) (i : ℕ×ℕ) (z : Positions n) :
    moment (R.family.beta i.1 i.2) (fun U=>∏ j∈s,R.family.O i.1 i.2 (atRef L (d j) r i (w j)) (wrap _ (z j)) U) =
    WilsonMovingReportDisplacement.read R L r (d ∘ pick s) (fun j=>w (pick s j)) i (z ∘ pick s) :=
  actual s d _ _

end YM.Integration.WilsonReportSubroster
