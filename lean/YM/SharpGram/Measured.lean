import YM.SharpGram.InContext
/-! Current endpoint (measuring coordinates, not the fixed-label log result).
With common UV construction and conditional consumer on it. Common
Ultrafilter refinement is allowed by MatrixTicket and its consumer. There are
also separate unconditional MatrixTicket clauses in fixed labels for certain
d,w: see Clauses. -/
set_option autoImplicit false
noncomputable section
namespace YM.SharpGram
open Function Set Filter Lattice RG Wilson Extraction Spec Org
open OPE OPE.Log Next.UVStress Weak
open scoped Topology BigOperators ContDiff
set_option quotPrecheck false
variable {G : Gauge}
section consequence
variable {C : Family G} {T : Table C.book} {f : Extraction.Order} (U : Final C f T) (V : Facilities C f T)
variable {φ : Filter (ℕ×ℕ)} [φ.NeBot] (hf : φ ≤ f.fuse)

def DynamicalCost (φ : Filter (ℕ×ℕ)) : Prop := ∀ d : ℕ,
    ∃ X : Weak.Portfolio C U.room.cutoff d φ,
    ∃ Y : ℕ → ∀ d : ℕ, YM.Spin.change T d,
    FixedPrice U X Y
include V hf
lemma fixed_ticket (h : DynamicalCost U φ) : MatrixTicket (C:=C) T U.sector.derivatives φ := by
  refine ticketClauses.mpr ⟨fun d x=>?_,fun d w L hw hp=>?_⟩
  · obtain ⟨X,Y,h⟩:= h d
    exact access_inlet U X V hf h ⟨d,Nat.lt_succ_self _⟩ x
  obtain ⟨X,Y,h⟩:= h d; exact access_outlet U X V hf h ⟨d,Nat.lt_succ_self _⟩ w L hw hp

lemma reportsFrom (h : DynamicalCost U φ) {P : Prescription U.sector.derivatives} (hp : P.Coherent) : LogTrace U P :=
    tickets_suffice U V hf (fixed_ticket U V hf h) hp
end consequence

/-- Actual joint witness supplying physical matrix/coercivity on every horizon
in the moving coordinates, both interfaces (inlets/outlets), and true
conditional log reports here. No task-completion claim **without discharging
the remaining frame transports** (DynamicalCost).
-/
theorem habitat (hG : G.Simple) {b : ℝ} (hb : 0<b) (f : Extraction.Order) :
    ∃ (C : Family G) (g : Extraction.Order) (T : Table C.book)
      (F : Spec.Final C (f.refine g) T) (L : EveryPhase.Almanac F)
      (P : Prescription F.sector.derivatives),
      C.Makes ∧ Spec.Calibrated C ∧
      C.path.levels.clock.kernel.penalty = b ∧
      UVExtension.Oasis.Floral (hG := hG) C ∧
      (Extraction.Order.mk Extraction.Sequence.full (f.refine g).per).Ordered C T ∧
      (∀ d k : ℕ, ∀ᶠ n in atTop,
        ∀ (r : ℕ) (v : Fin r → C.book.Token), (∀ i, (v i).1 ≤ d) →
          ∃ g, UVExtension.Poppy.Margins C r n k v g) ∧
      Facilities C (f.refine g) T ∧
      (∃ W r D, LogPackage C W r D ∧ TrueSteps C W) ∧
      EveryPhase.Completed F L ∧ AllShapes F P ∧
      Dense.Coverage C F.room.cutoff ∧
      -- all announced horizons, all sublimit choices in coverage on an arbitrary ultra
      (∀ U : Ultrafilter (ℕ×ℕ), (U : Filter _) ≤ (f.refine g).fuse → ∀ D : ℕ,
        Nonempty (Weak.Portfolio C F.room.cutoff D U) ∧
        ∀ X : Weak.Portfolio C F.room.cutoff D U,
          ∃ Y : ℕ → ∀ d : ℕ, YM.Spin.change T d,
          PricedIn F X Y ∧
          ∀ d : Fin (D+1), Tendsto (fun k => Weak.Portfolio.inBasis F X k d (Y k d)) atTop
                    (𝓝 (Weak.Portfolio.model C d))) ∧
      -- Remaining log work, on same construction
      (∀ (φ : Filter (ℕ×ℕ)) [φ.NeBot], φ ≤ (f.refine g).fuse → DynamicalCost F φ →
        MatrixTicket (C:=C) T F.sector.derivatives φ ∧ LogTrace F P) := by
  obtain ⟨C,g,T,F,L,hc,ht,hB,hV,hK,hY,hW,hh,⟨h',hs⟩,hu,P,hP,hN⟩:= common hG hb f
  refine ⟨C,g,T,F,L,P,hc,ht,hB,hV,hK,hY,hW,hh,hu,hP,hs,fun U hf D=>?_,fun φ _ hf h=>?_⟩
  · exact ⟨fromCoverage hs U hf, fun X => attains F X hW hf⟩
  have h:= fixed_ticket F hW hf h; exact ⟨h,hN φ hf h⟩
end YM.SharpGram
