import YM.Integration.WilsonFactoryHomogeneousPairs
import YM.Integration.WilsonOrdinaryMixedGram
import YM.AllOrder.Leading.Solve

/-! Exact descent to each named field's own original engineering chart in
the separated physical mixed Gram, with the second reflection preserved. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonFactoryOwnHeight
open Function Filter Finset Lattice RG Spec Table OPE SharpGram RG12 RG17 Maxwell
open Trace.Pilot Climb Push.FiniteDetection.Free MS MS.Menus MS.Local.Physical
open scoped Classical BigOperators Topology
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
    (B : Deck G) (F : Final C f S) (J : ℝ → PhysMS.tower S)
set_option quotPrecheck false
local notation "W₀" => Free.scheme C.labels
local notation "W" => F.sector.derivatives

def ground {d : ℕ} (q : Glyph B d) : (Spin.comparator C.book).Field q.1.val :=
  Pert.RawLabels.enroll C.labels q.1.val (FVAAlt2.Shop.seat B q.2.2)

theorem input {d : ℕ} (q : Glyph B d) :
    (W₀).rise (Nat.le_of_lt_succ q.1.isLt) (ground (C:=C) B q) =
    WilsonFactoryPhysicalGlyphs.note (C:=C) B d q :=
  UVNext.FreeStress.rise_embed C.labels W₀ (Free.scheme_filters C.labels) _ _

theorem at_stage {d : ℕ} {r : ℝ} (stage : Pier.Lair.OStage F (J r) d) (q : Glyph B d) :
    J r d (WilsonFactoryPhysicalGlyphs.note (C:=C) B d q) =
    (W).rise (Nat.le_of_lt_succ q.1.isLt) (J r q.1.val (ground (C:=C) B q)) := by
  rw [← input (C:=C) B q]
  exact stage.aligned q.1 (Fin.last d) (Nat.le_of_lt_succ q.1.isLt) _

theorem ports (P : Pier.Lair.Present F J) (d : ℕ) :
    ∀ᶠ r in trail, ∀ q : Glyph B d, J r d (WilsonFactoryPhysicalGlyphs.note (C:=C) B d q) =
      (W).rise (Nat.le_of_lt_succ q.1.isLt) (J r q.1.val (ground (C:=C) B q)) :=
  (P.aligned d).mono fun _ hs q => at_stage B F J hs q

def reflected {h k : ℕ} (p : Points 2) (a : S.Field h) (b : S.Field k) : ℝ :=
  (S.useAt S p (![(⟨h,a⟩ : S.Tag),⟨k,S.adj F.room.kernel.spin k timeAxis b⟩])).re

theorem contracted {h k d : ℕ} (hh : h≤d) (hk : k≤d) (p : Points 2) (legal : p ∈ conf 2)
    (a : S.Field h) (b : S.Field k) :
    glass S F.room.kernel.spin d p ((W).rise hh a) ((W).rise hk b) = reflected F p a b := by
  let ν : Fin 2 → S.Tag := ![⟨h,a⟩,⟨k,S.adj F.room.kernel.spin k timeAxis b⟩]
  let h₀ := fun i : Fin 2 => (ν i).1
  let v := fun i : Fin 2 => (ν i).2
  have inc (i : Fin 2) : h₀ i ≤ d := by fin_cases i; exact hh; exact hk
  have paid := AllOrder.Leading.moment_inclusion (d:=fun _ : Fin 2 => d) (a:=h₀)
    F.room.kernel.laws.toSymmetric F.phase.transport.injection inc legal v
  have cov : S.adj F.room.kernel.spin d timeAxis ((W).rise hk b) =
      (W).rise hk (S.adj F.room.kernel.spin k timeAxis b) := by
    simp [Table.adj,F.phase.transport.rights.realInc,F.phase.transport.rights.mirrorInc]
  rw [glass_reads,cov]
  apply congrArg Complex.re
  change S.useAt S p (fun i => ⟨d,(![(W).rise hh a,(W).rise hk (S.adj F.room.kernel.spin k timeAxis b)]) i⟩) =
    S.useAt S p ν
  have hl : (fun i => (⟨d,(![(W).rise hh a,(W).rise hk (S.adj F.room.kernel.spin k timeAxis b)]) i⟩ : S.Tag)) =
      (fun i => ⟨d,(W).rise (inc i) (v i)⟩) := by
    funext i
    fin_cases i <;> rfl
  rw [hl]
  exact paid

theorem mixed {d : ℕ} (r s : ℝ) (hr : 0<r)
    (current : Pier.Lair.OStage F (J r) d) (other : Pier.Lair.OStage F (J s) d)
    (q t : Glyph B d) :
    WilsonOrdinaryMixedGram.mixed F J d r s
        (WilsonFactoryPhysicalGlyphs.note (C:=C) B d q) (WilsonFactoryPhysicalGlyphs.note (C:=C) B d t) =
      reflected F (r • detectors) (J s q.1.val (ground (C:=C) B q)) (J r t.1.val (ground (C:=C) B t)) := by
  change glass S F.room.kernel.spin d _ (J s d _) (J r d _) = _
  rw [at_stage B F J other q,at_stage B F J current t]
  exact contracted F _ _ _ ((Next.UVStress.enlarged hr _).mp detectors_in) _ _

end YM.Integration.WilsonFactoryOwnHeight
