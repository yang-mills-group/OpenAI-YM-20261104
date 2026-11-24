import YM.Integration.WilsonAllDateHarvestFiledGallery

/-! On the original dated conditional kernel the first merger keeps the
full prior painter, all marked hard partners, and the physical quiet
coefficient. Its regular and intermediate hard bills are issued on
the same walk, with distinct original support exponents. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPhysicalHistoryKioskFirst
open Function Finset Lattice Wilson RG Source Pressure Ac Marker Push.Corrected Push.AbsoluteSums
open PhysicalNext PhysicalNext.Repeat Progress.DirectedRecipe RemainderComparison
open QuadraticLocal QuadraticLocal.Travel QuadraticLocal.Trigger ConnectedActivityE6 Lyric Muse Serif Spire
open Merge Lotus Typeface MeasureTheory WilsonPhysicalHistoryPictureRestore
open scoped Classical BigOperators

variable {I J V : Type} [Countable I] [Countable J] [DecidableEq V] [Fintype V]
  {G : Gauge} {C : Family G} {per i N : ℕ} {L : Side}
  {x e f r s κ w b₀ b₁ z Y Γ K : ℝ} {T : Type*} {A₀ : Teller G}
  {Q : ConnectedActivityE6.Target G A₀} {horizon : ConnectedActivityE6.Target.Order G w}
variable {tube : Pressure.Tube G (C.path.levels.clock.op i per)} (cash : Cash w x κ L Q horizon z tube (C.path.rep N per (i+1)))
  {k : ℕ} (eyes : Eyes cash (C.path.rep N per i) e Γ Y K k) (W : Travel.Walk cash (C.path.rep N per i) e f r s)
  {R : Census V} {o : V → Site (C.side (i+1) per)} (A : Gallery T I o (C.path.rep N per (i+1)) R)
  (previous : Lamps T J G (C.path.rep N per (i+1)).p o R) (weights : V → ℝ)
  (grant : Seal (picture A previous) weights b₀ b₁) (positive : ∀ v, 0 < weights v)
  (slots : HasSlots (C.path.rep N per (i+1)).p (C.path.rep N per (i+1)).activities) (cap : ∀ mode : R.Mode, mode.val.card ≤ k)
  (fits : 2*(b₀+b₁) ≤ K) (pin : T) (ω : V → ℝ) (pos : ∀ v,0 < ω v)
  {a q h : ℝ} (expo : 0 ≤ a) (reg : A.E.Paid ω (C.path.rep N per (i+1)).p.B (a+2) q) (hard : A.K.Paid ω (C.path.rep N per (i+1)).p.B a h)

abbrev regular := Travel.raw cash eyes (picture A previous) weights grant positive slots fits pin
abbrev intermediate := Travel.mid cash W eyes (picture A previous) weights grant positive slots cap fits pin
def source (t : T) (U : Config G (C.side i per)) : Poly R :=
  Poly.pass (WilsonPhysicalHistoryGroupedClear.constant A.E t) * (C.path.levels.clock.op i per).push (C.path.rep N per (i+1)).beta (retained A previous t) U


include cash eyes W positive slots grant cap fits pos expo reg hard in
theorem original (F : Tree.Forest (C.path.levels.clock.op i per).ratio) :
    ((regular cash eyes A previous weights grant positive slots fits pin)).Paid weights (C.path.rep N per i).p.B ((C.path.rep N per i).p.supportExponent+1+1)
        (Spire.fees (C.path.levels.clock.op i per).ratio.count ((C.path.rep N per i).p.supportExponent+1+1)*b₀+Y^k*Γ) ∧
      ((intermediate cash eyes W A previous weights grant positive slots cap fits pin)).Paid weights (C.path.rep N per i).p.B ((C.path.rep N per i).p.supportExponent+1) f ∧
      ReadZone T (C.path.rep N per i).p W.intermediate (intermediate cash eyes W A previous weights grant positive slots cap fits pin) (source (C:=C) (per:=per) (i:=i) (N:=N) A previous) ((regular cash eyes A previous weights grant positive slots fits pin)).log ∧
      ∀ (t : T) U, (source A previous t U).part R.quiet =
        Complex.ofReal ((C.path.levels.clock.op i per).push (C.path.rep N per (i+1)).beta
          (C.path.rep N per (i+1)).eval U) := by
  have bought := Travel.docket cash W eyes (picture A previous) weights grant positive slots cap fits pin F
  have value (t : T) (U : Config G (C.side i per)) :
      (C.path.levels.clock.op i per).push (C.path.rep N per (i+1)).beta ((picture A previous).density t) U = (source (C:=C) (per:=per) (i:=i) (N:=N) A previous) t U :=
    congrFun (WilsonAllDateHarvestFiledGallery.pushed cash eyes A previous weights grant positive slots fits
      ω pos expo reg hard t) U
  refine ⟨bought.1,bought.2.1,?_,?_⟩
  · intro t U
    rw [← value t U]
    exact bought.2.2 t U
  · intro t U
    rw [← value t U]
    exact Travel.tuneQuiet cash eyes (picture A previous) weights grant positive slots cap fits pin t U

end YM.Integration.WilsonPhysicalHistoryKioskFirst
end

