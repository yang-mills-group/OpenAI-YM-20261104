import YM.Integration.FullQLocalRequestData
import YM.Integration.FullQLocalStrongTargetData

/-!
Finite input-capacity closure before any physical Run is selected.
Each successor uses the capacities of the exact preceding selected
specification. This file selects no widths, model, Grant, or Run.
-/
set_option autoImplicit false
noncomputable section
universe u

namespace YM.Integration.FullQLocal.PreRun.SuccessiveRequests
open FullQLocal.RenderedStep

variable {V : Type}

/-- Raise only the next input capacities, including the retuning power. -/
def nextRequest (J : Request V) (caps : Handoff.OutputCapacities) (r : ℕ) :
    Request V :=
  { J with
    vacuumRankCap := max J.vacuumRankCap caps.vacuumRank
    inputPacketRankCap := max J.inputPacketRankCap caps.packetRank
    inputPacketPowerCap := max J.inputPacketPowerCap (max caps.packetPower (r + 2)) }

theorem nextRequest_caps (J : Request V) (caps : Handoff.OutputCapacities) (r : ℕ) :
    caps.vacuumRank ≤ (nextRequest J caps r).vacuumRankCap ∧
    caps.packetRank ≤ (nextRequest J caps r).inputPacketRankCap ∧
    caps.packetPower ≤ (nextRequest J caps r).inputPacketPowerCap ∧
    r + 2 ≤ (nextRequest J caps r).inputPacketPowerCap := by
  exact ⟨le_max_right _ _, le_max_right _ _,
    (le_max_left _ _).trans (le_max_right _ _),
    (le_max_right _ _).trans (le_max_right _ _)⟩

theorem nextRequest_old_caps (J : Request V) (caps : Handoff.OutputCapacities) (r : ℕ) :
    J.vacuumRankCap ≤ (nextRequest J caps r).vacuumRankCap ∧
    J.inputPacketRankCap ≤ (nextRequest J caps r).inputPacketRankCap ∧
    J.inputPacketPowerCap ≤ (nextRequest J caps r).inputPacketPowerCap := by
  exact ⟨le_max_left _ _, le_max_left _ _, le_max_left _ _⟩

/-- A complete Request with just the three variable input caps erased. -/
def skeleton (J : Request V) : Request V :=
  { J with vacuumRankCap := 0, inputPacketRankCap := 0, inputPacketPowerCap := 0 }

theorem skeleton_nextRequest (J : Request V) (caps : Handoff.OutputCapacities) (r : ℕ) :
    skeleton (nextRequest J caps r) = skeleton J := rfl

/-- Keep a request together with its own selected pre-Run specification. -/
structure Stage (F : Request V → Type u) where
  request : Request V
  selected : F request

namespace Stage
variable {F : Request V → Type u}

/-- Selection occurs only after the preceding specification determines the caps. -/
def next (limits : ∀ J, F J → Handoff.OutputCapacities)
    (select : ∀ J, F J) (r : ℕ) (S : Stage F) : Stage F where
  request := nextRequest S.request (limits S.request S.selected) r
  selected := select (nextRequest S.request (limits S.request S.selected) r)

/-- All finite depths are constructed before applying any physical constructor. -/
def chain (limits : ∀ J, F J → Handoff.OutputCapacities)
    (select : ∀ J, F J) (r : ℕ) (seed : Stage F) : ℕ → Stage F
  | 0 => seed
  | n + 1 => next limits select r (chain limits select r seed n)

theorem chain_zero (limits : ∀ J, F J → Handoff.OutputCapacities)
    (select : ∀ J, F J) (r : ℕ) (seed : Stage F) :
    chain limits select r seed 0 = seed := rfl

theorem chain_succ (limits : ∀ J, F J → Handoff.OutputCapacities)
    (select : ∀ J, F J) (r : ℕ) (seed : Stage F) (n : ℕ) :
    chain limits select r seed (n + 1) =
      next limits select r (chain limits select r seed n) := rfl

theorem chain_caps (limits : ∀ J, F J → Handoff.OutputCapacities)
    (select : ∀ J, F J) (r : ℕ) (seed : Stage F) (n : ℕ) :
    let previous := chain limits select r seed n
    let following := chain limits select r seed (n + 1)
    (limits previous.request previous.selected).vacuumRank ≤ following.request.vacuumRankCap ∧
    (limits previous.request previous.selected).packetRank ≤ following.request.inputPacketRankCap ∧
    (limits previous.request previous.selected).packetPower ≤ following.request.inputPacketPowerCap ∧
    r + 2 ≤ following.request.inputPacketPowerCap := by
  exact nextRequest_caps _ _ _

theorem chain_old_caps (limits : ∀ J, F J → Handoff.OutputCapacities)
    (select : ∀ J, F J) (r : ℕ) (seed : Stage F) (n : ℕ) :
    let previous := chain limits select r seed n
    let following := chain limits select r seed (n + 1)
    previous.request.vacuumRankCap ≤ following.request.vacuumRankCap ∧
    previous.request.inputPacketRankCap ≤ following.request.inputPacketRankCap ∧
    previous.request.inputPacketPowerCap ≤ following.request.inputPacketPowerCap := by
  exact nextRequest_old_caps _ _ _

/-- Every other field of the full Request stays literally unchanged at every depth. -/
theorem chain_skeleton (limits : ∀ J, F J → Handoff.OutputCapacities)
    (select : ∀ J, F J) (r : ℕ) (seed : Stage F) (n : ℕ) :
    skeleton (chain limits select r seed n).request = skeleton seed.request := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

end Stage
end YM.Integration.FullQLocal.PreRun.SuccessiveRequests
end
