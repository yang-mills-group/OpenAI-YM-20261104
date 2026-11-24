import YM.Integration.ActualOriginalQAtRank
import YM.Integration.ActualOriginalQPreRunApplication
import Mathlib.Data.Nat.Pairing
import YM.Integration.ActualQlocalRequestFamily

/-!
A countable base-request family is enlarged by every natural rank cap.
The pairing is fixed before the sole Run choice. For each base index and
every original Q load, its full canonical request occurs at the paired
index using the literal rankCap of that load. No bound on that rank and
no enumeration of the loads themselves is required.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualOriginalQCountableRequests
open Filter Lattice Wilson RG Marker
open PhysicalNext.Repeat.Legato
open FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric.Retained
open ActualOriginalQPreRunApplication
open scoped Topology

variable {G : Gauge} {D : MS.Local.Physical.Deck G}

theorem request_atRank {V : Type} [Fintype V]
    (u : V → MS.Rake.Label D) (K : Request V) :
    ActualOriginalQPreRunRequest.request u K =
      atRank (ActualOriginalQPreRunRequest.rankCap u) K := rfl

section General
variable {A : ℕ → Type}

/-- Equality transport of the original load; no label or monomial is changed. -/
def castLoad {j l : ℕ} (h : j = l) (u : A j → MS.Rake.Label D) :
    A l → MS.Rake.Label D :=
  h ▸ u

variable [∀ j, Fintype (A j)]

theorem rank_castLoad {j l : ℕ} (h : j = l) (u : A j → MS.Rake.Label D) :
    ActualOriginalQPreRunRequest.rankCap (castLoad h u) =
      ActualOriginalQPreRunRequest.rankCap u := by
  cases h
  rfl

/-- Every base alphabet is repeated once for each natural rank. -/
abbrev Alphabet (A : ℕ → Type) (k : ℕ) := A (Nat.unpair k).1

def index (j : ℕ) (u : A j → MS.Rake.Label D) : ℕ :=
  Nat.pair j (ActualOriginalQPreRunRequest.rankCap u)

def load (j : ℕ) (u : A j → MS.Rake.Label D) :
    Alphabet A (index j u) → MS.Rake.Label D :=
  castLoad (A := A) (j := j) (l := (Nat.unpair (index j u)).1)
    (congrArg Prod.fst (Nat.unpair_pair j (ActualOriginalQPreRunRequest.rankCap u))).symm u

theorem load_rank (j : ℕ) (u : A j → MS.Rake.Label D) :
    ActualOriginalQPreRunRequest.rankCap (load j u) =
      ActualOriginalQPreRunRequest.rankCap u :=
  by
    unfold load
    exact rank_castLoad (A := A) (j := j) (l := (Nat.unpair (index j u)).1) _ u

variable [∀ j, DecidableEq (A j)] (K : ∀ j, Request (A j))

def base (k : ℕ) : Request (Alphabet A k) :=
  K (Nat.unpair k).1

def requests (k : ℕ) : Request (Alphabet A k) :=
  atRank (Nat.unpair k).2 (base K k)

def census (k : ℕ) : Census (Alphabet A k) :=
  Stock.census (Alphabet A k)

/-- Every original Q load is covered by the fixed paired family. -/
theorem covered (j : ℕ) (u : A j → MS.Rake.Label D) :
    CoveredAt (B := census (A := A)) (J := requests K)
      (index j u) (load j u) (base K (index j u)) := by
  refine ⟨rfl, ?_⟩
  change atRank (Nat.unpair (index j u)).2 (base K (index j u)) = _
  rw [request_atRank]
  apply congrArg (fun n => atRank n (base K (index j u)))
  calc
    (Nat.unpair (index j u)).2 = ActualOriginalQPreRunRequest.rankCap u :=
      congrArg Prod.snd (Nat.unpair_pair j (ActualOriginalQPreRunRequest.rankCap u))
    _ = ActualOriginalQPreRunRequest.rankCap (load j u) := (load_rank j u).symm

/-- Simultaneous coverage of all base requests and all original loads. -/
theorem covers :
    Covers (B := census (A := A)) (J := requests K)
      (fun q : (j : ℕ) × (A j → MS.Rake.Label D) => index q.1 q.2)
      (fun q => load q.1 q.2) (fun q => base K (index q.1 q.2)) :=
  fun q => covered K q.1 q.2

variable {hG : G.Simple} {R : Run G}
  (r : PreRun.Receipt hG (Alphabet A) (census (A := A)) (requests K) R)

/-- Every order/load uses the same single preselected receipt and Run. -/
def grant (hReadout : RG05Preconstruction.ReadoutPurchase R.b)
    (j : ℕ) (u : A j → MS.Rake.Label D)
    (cap : ℕ → ℝ) (hcap : ∀ m, 0 ≤ cap m)
    (hcap0 : Tendsto cap atTop (𝓝 0)) :=
  initialGrant r hReadout (index j u) (load j u)
    (base K (index j u)) (covered K j u) cap hcap hcap0

/-- The floor tail is allowed to depend on this fixed order/load, then
precedes every later datum and physical period on the same Run. -/
theorem local_floors (j : ℕ) (u : A j → MS.Rake.Label D) :
    ∃ first : ℕ, ∀ d : LocalFormal.Datum R.family (Stock.census (Alphabet A (index j u))),
      first ≤ d.level →
      Handoff.LocalFloors (r.chosen.entry (index j u)).floor r.n d :=
  initial_local_floors r (index j u)

end General

/-- The already validated complete natural-code dictionary supplies the base. -/
abbrev dictionaryAlphabet (P : ActualQlocalRequestFamily.Recipe) (j : ℕ) :=
  Fin (ActualQlocalRequestFamily.family P j).1

def dictionaryBase (P : ActualQlocalRequestFamily.Recipe) (j : ℕ) :
    Request (dictionaryAlphabet P j) :=
  (ActualQlocalRequestFamily.family P j).2

/-- One fixed real recipe yields a single countable family covering every
dictionary order and every original load, before the Run is chosen. -/
theorem dictionary_covers (P : ActualQlocalRequestFamily.Recipe) :
    Covers (B := census (A := dictionaryAlphabet P)) (J := requests (dictionaryBase P))
      (fun q : (j : ℕ) × (dictionaryAlphabet P j → MS.Rake.Label D) => index q.1 q.2)
      (fun q => load q.1 q.2) (fun q => base (dictionaryBase P) (index q.1 q.2)) :=
  covers (dictionaryBase P)

/-- Every finite whole-test request matching the fixed real recipe occurs
with the native three-cost cap and finite relabeling. The stronger period
lower bound remains exactly the one in that capped base request. -/
theorem dictionary_complete {V : Type} [Fintype V]
    (P : ActualQlocalRequestFamily.Recipe) (K : Request V)
    (hP : ActualQlocalRequestFamily.Matches P K)
    (hwhole : ∀ v, ∃ d w : ℕ, K.tests v = ⟨.whole, d, w⟩) :
    ∃ e : Fin (Fintype.card V) ≃ V, ∃ j : ℕ,
      ActualQlocalRequestFamily.family P j =
        ⟨Fintype.card V, ActualQlocalRequestFamily.capped
          (ActualQlocalRequestTransport.reindex e K)⟩ ∧
      ∀ u : dictionaryAlphabet P j → MS.Rake.Label D,
        CoveredAt (B := census (A := dictionaryAlphabet P))
          (J := requests (dictionaryBase P)) (index j u) (load j u)
          (base (dictionaryBase P) (index j u)) := by
  obtain ⟨e, j, hj⟩ := ActualQlocalRequestFamily.complete_finite P K hP hwhole
  exact ⟨e, j, hj, fun u => covered (dictionaryBase P) j u⟩

end YM.Integration.ActualOriginalQCountableRequests
end
