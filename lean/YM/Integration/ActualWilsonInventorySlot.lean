import YM.Integration.ActualWilsonSpectatorDifference
import YM.Integration.ActualWilsonSpectatorGerm

/-! Full-support reserved Wilson addresses and their exact dressed cofactors. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualWilsonInventorySlot
open Function Set Finset MeasureTheory Lattice Wilson RG Marker Source Labels
open Extra.Histories Relay Bid Trace.Physical Trace.Physical.Germ
open Planned.GuardedAtom MergeProof ActualWilsonSpectatorDifference
variable {G : Gauge} {n : Side} {W : Rep G n}

abbrev Inventory (n : Side) := {I : Support n // I.Nonempty}

def stock (I : Inventory n) : StockTag n :=
  ⟨(Finset.univ,I.1),I.2,Finset.subset_univ _⟩

def address (K : Guard.Keeper W.p W.activities) : Inventory n ↪ ℕ where
  toFun I := cart K (stock I)
  inj' _ _ h := Subtype.ext (congrArg (fun s : StockTag n => s.1.2) ((cart K).injective h))

theorem geometry (K : Guard.Keeper W.p W.activities) (I : Inventory n) :
    (W.activities.forced (address K I)).support = Finset.univ ∧
    (W.activities.forced (address K I)).inventory = I.1 :=
  ⟨K.support (stock I,0),K.inventory (stock I,0)⟩

theorem pass (K : Guard.Keeper W.p W.activities) (I : Inventory n) (U : Config G n)
    (h : flags W.p.threshold U = I.1) :
    (W.activities.forced (address K I)).eligible W.p.threshold U := by
  have hf : (W.activities.forced (address K I)).support ∩ flags W.p.threshold U =
      (W.activities.forced (address K I)).inventory := by simp [geometry, h]
  exact ⟨hf,K.pass (stock I,0) U hf⟩

/-- Disjointness and the nonempty inventory of every partner force a singleton. -/
theorem unique_packet (K : Guard.Keeper W.p W.activities) (I : Inventory n)
    {U : Config G n} {b : Finset ℕ} (hb : W.activities.admissible W.p U b)
    (hi : address K I ∈ b) : b = {address K I} := by
  ext j
  rw [Finset.mem_singleton]
  constructor
  · intro hj
    by_contra hn
    have dis := hb.1 hi hj (Ne.symm hn)
    obtain ⟨s,hs⟩ := (W.activities.forced j).inventory_ne
    exact (Finset.disjoint_left.1 dis)
      (by rw [(geometry K I).1]; exact Finset.mem_univ s) ((W.activities.forced j).inventory_sup hs)
  · rintro rfl
    exact hi

/-- An original full-support slot reads precisely its entire dirty inventory. -/
theorem dressed_slot (K : Guard.Keeper W.p W.activities) (I : Inventory n) (U : Config G n) :
    dressed W (address K I) U = if flags W.p.threshold U = I.1 then 1 else 0 := by
  classical
  unfold dressed
  rw [tsum_eq_single ({address K I} : Finset ℕ)]
  · by_cases h : flags W.p.threshold U = I.1
    · have ha : W.activities.admissible W.p U {address K I} := by
        simp [Activities.admissible, (geometry K I).2, h]
      simp [coat,ha,h]
    · have ha : ¬ W.activities.admissible W.p U {address K I} := by
        intro ha
        exact h (by simpa [(geometry K I).2] using ha.2.symm)
      simp [coat,ha,h]
  · intro b hb
    have hh : ¬ (address K I ∈ b ∧ W.activities.admissible W.p U b) :=
      fun h => hb (unique_packet K I h.2 h.1)
    simp [coat, hh]

def deposit (W : Rep G n) (f : Config G n → ℂ) (I : Inventory n) (U : Config G n) :=
  if flags W.p.threshold U = I.1 then f U else 0

def rows (K : Guard.Keeper W.p W.activities) (f : Config G n → ℂ) :
    ℕ → Config G n → ℂ := extend (address K) (deposit W f) 0

theorem on_slot (K : Guard.Keeper W.p W.activities) (f : Config G n → ℂ) (I : Inventory n) :
    rows K f (address K I) = deposit W f I := (address K).injective.extend_apply ..

theorem off_slot (K : Guard.Keeper W.p W.activities) (f : Config G n → ℂ) {j : ℕ}
    (h : j ∉ range (address K)) : rows K f j = 0 := extend_apply' _ _ _ h

def book {d : ℕ} (F : Frame G d) (o : Site n) (K : Guard.Keeper W.p W.activities)
    (f : Config G n → ℂ) : Coefficient F n :=
  { primary o (0 : F.Coeff) with forced := rows K f }

theorem format {d : ℕ} (F : Frame G d) (o : Site n) (A : Hol G)
    (K : Guard.Keeper W.p W.activities) (f : Config G n → ℂ) (hm : Measurable f)
    (hg : GaugeInvariant f) : (book F o K f).Format o A W := by
  have hb : (primary o (0 : F.Coeff)).Format o A W := primary_format _
  refine ⟨hb.smooth,hb.origin,hb.identity_null,hb.projects,?_,?_,?_,?_,?_⟩
  · intro j U hn
    by_cases h : j ∈ range (address K)
    · obtain ⟨I,rfl⟩ := h
      change rows K f (address K I) U ≠ 0 at hn
      rw [on_slot] at hn
      exact pass K I U (by by_contra h; simp [deposit,h] at hn)
    · exact False.elim (hn (congrFun (off_slot K f h) U))
  · intro j hn
    by_cases h : j ∈ range (address K)
    · obtain ⟨I,rfl⟩ := h
      simp [(geometry K I).1]
    · exact False.elim (hn (off_slot K f h))
  · intro j
    change GaugeInvariant (rows K f j)
    by_cases h : j ∈ range (address K)
    · obtain ⟨I,rfl⟩ := h
      rw [on_slot]
      intro k U
      simp [deposit,gauge_flags,hg k U]
    · rw [off_slot K f h]
      exact fun _ _ => rfl
  · intro j
    change UsesFinal _ _ (rows K f j)
    by_cases h : j ∈ range (address K)
    · obtain ⟨I,rfl⟩ := h
      rw [(geometry K I).1]
      intro U V hUV _
      exact congrArg _ (funext fun e => hUV e (Finset.mem_univ _) (Finset.mem_univ _))
    · rw [off_slot K f h]
      exact fun _ _ _ _ => rfl
  · intro j
    change Measurable (rows K f j)
    by_cases h : j ∈ range (address K)
    · obtain ⟨I,rfl⟩ := h
      rw [on_slot]
      exact hm.ite (flags_measurable_eq _ _) measurable_const
    · rw [off_slot K f h]
      exact measurable_const

end YM.Integration.ActualWilsonInventorySlot
