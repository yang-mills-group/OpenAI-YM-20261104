import YM.LocalLTE.Tile.Mantel
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Nil
/-! Local LTE high-order representation/compatibility on supported tiles. Adapts
`PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Nil`.
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
variable {G : Gauge} {c f C F L₀ : Side} {P : Patch} {J₀ M D' m: ℕ} {K : Teller G} {p a W U :ℝ}
section sow
variable {S:StepData c f} {T : Tube G S} {R:RG.Rep G f} {X: ConnectedActivityE6.Target G K} {o:Target.Order G W}
    {H : Cash W p a L₀ X o U T R}
abbrev PoetN (J₀:ℕ) (H:Cash W p a L₀ X o U (c:=c) (f:=f) T R) := {z:Vines _ _ // StirN H J₀ z} -- dep
-- lemma equivalence preimage support Labeling
lemma bakedN {k:ℕ} : { i: Vines c f| i.fst ≤J₀∧∀ j, (i.2 j)⊆Meadow.tuck k}.Finite:= by
  let T: Finset (Music c f):= Meadow.tuck k; let a i:=Fintype.piFinset (fun _j : Option (Fin i)=> T.powerset) -- Fintype
  let Y:Finset (Vines c f):= (Finset.range (J₀+1)).sigma a
  apply Y.finite_toSet.subset; rintro ⟨i,j⟩ ⟨hv,hj⟩; change (Sigma.mk i j)∈Y
  change i≤J₀ at hv; apply mem_sigma.mpr; refine ⟨mem_range.mpr (by change i<J₀+1; omega),?_⟩; simp_rw [a,Fintype.mem_piFinset]; exact fun i=>mem_powerset.mpr (hj i)
lemma tiledN (J₀:ℕ) (H : Cash W p a L₀ X o U T R) (k:ℕ): { i : PoetN J₀ H | ∀ j,i.val.snd j⊆Meadow.tuck k}.Finite := Set.Finite.subset (bakedN.preimage (show Set.InjOn (fun p:PoetN J₀ H=>p.val) _ from Subtype.val_injective.injOn)) (fun i hi=> show i.val.1≤J₀∧∀ j,i.val.snd j⊆ Meadow.tuck k from ⟨i.property.small,hi⟩)
def calendarN (J₀:ℕ) (H:Cash W p a L₀ X o U T R) (k:ℕ) := (tiledN J₀ H k).toFinset
lemma tunesN (i:PoetN J₀ H) (k:ℕ): i∈ Meadow.calendarN J₀ H k↔∀ j,i.val.2 j ⊆ Meadow.tuck k:= Set.Finite.mem_toFinset ..
lemma retiresN (i:PoetN J₀ H) : ∀ᶠ k in atTop,i ∈ Meadow.calendarN J₀ H k:= by
  have hf j : ∀ᶠ k in atTop, i.val.2 j⊆ Meadow.tuck k:= (eventually_all_finset _).mpr fun u _=> (eventually_ge_atTop (held u)).mono (fun _ he=> (pocket ..).mpr he)
  exact (eventually_all.mpr hf).mono fun k h=> (tunesN i k).2 h
end sow
end YM.PhysicalNext.Repeat.Meadow
