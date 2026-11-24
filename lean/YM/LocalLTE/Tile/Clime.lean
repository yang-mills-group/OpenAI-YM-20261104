import YM.LocalLTE.Tile.Legacy
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Vista
/-! Local LTE high-order representation/compatibility on supported tiles. Adapts
`PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Vista`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Meadow
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F L₀ : Side} {P : Patch} {J₀ M D' : ℕ} {K : Teller G}
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q: KernelChoices} {hC:C.val=c.val*M} {he:2 ≤ c.val} {p a b W U V : ℝ}
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
variable {T : Tube G (stepped Q h)} {T' : Tube G (stepped Q H)} {R:RG.Rep G f} {R':RG.Rep G F}
    {X : ConnectedActivityE6.Target G K} {o : ConnectedActivityE6.Target.Order G W}
    {I : Cash W p a L₀ X o U T R} {I' : Cash W p a L₀ X o V T' R'}
    (hC he)
-- includes length/ground but not val bills
local notation "B" => radiusB p
variable (hp : R'.path= R.path)
include hC he hp I I'
lemma seed_orderN (p:Park C F) (heq:Set.InjOn (verse_down (L)) p) (hh:Set.InjOn ((L).low.cut) (Meadow.ground I' p)) : SeedN I' J₀ p ↔ SeedN I J₀ (wrappers (L) p):= by
  have he' := preheated (verse_down (L)) (I'.supportP ∘ disc (Y)) (I.supportP ∘ disc (S)) p (L).low.cut (fun i=> (contempt hC he (I:=I) (I':=I') hp i).2) heq (by rw [footland] at hh; exact hh)
  have ht := card_image_of_injOn heq
  have hf {c f'} {W₁:StepData c f'} (p: Finset (Music c f')) (g: Head W₁→Support c): Ac.Spark g (hatch W₁ p) ↔Ac.Spark (g ∘ disc W₁) p:= by
    unfold hatch; rw [Finset.map_eq_image]; exact (sparkling _ _ p (Function.Embedding.injective _|>.injOn)).symm
  have ha : Ac.Spark I'.supportP (hatch _ p) ↔Ac.Spark I.supportP (hatch _ (wrappers (L) p)):= (hf p _).trans ((show Ac.Spark (I'.supportP ∘ disc (Y)) p ↔ Ac.Spark (I.supportP ∘ disc (S)) (wrappers (L) p) from (by convert! he' using 2; unfold wrappers; congr; exact Subsingleton.elim _ _)).trans (hf (wrappers (L) p) I.supportP).symm)
  constructor
  · intro h; refine ⟨ha.1 h.hot,ht ▸ h.sizes,fun i hi=>?_⟩; obtain ⟨i,hi,rfl⟩:=mem_image.mp hi; exact (contempt hC he hp (I:=I) (I':=I') i).1 ▸ h.earns _ (by assumption)
  intro h; refine ⟨ha.2 h.hot,ht ▸ h.sizes,fun i hi=> (contempt hC he hp (I:=I) (I':=I') i).1.trans_le (h.earns _ (mem_image_of_mem _ hi))⟩
end YM.PhysicalNext.Repeat.Meadow
