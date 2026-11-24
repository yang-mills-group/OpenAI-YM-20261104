import YM.LocalLTE.Moor.Replica
import YM.LocalLTE.Cycles.Day
/-! Extended layout budgets. Adapted FullVolume/C/Clockers.lean. literal indexing. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Meadow
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March Match
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f L₀ : Side} {K : Teller G} {p a W U : ℝ} {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
variable {S:StepData c f} {T:Tube G S} {R R' Q : RG.Rep G f} {H : Cash W p a L₀ X o U T R} {I: Cash W p a L₀ X o U T R'} {χ : Chi} {F : Tree.Forest S.ratio}
variable (P : Match.Alliance H I 1 0) (hz:P.units=Equiv.refl _)
variable (hp:R.path=R'.path) (he:R.activities.reg=R'.activities.reg) (hk:R.activities.forced=R'.activities.forced)
lemma local_unitsN {P A:Match.Alliance H I 1 0} (hh : P.units=A.units) : P=A:=by cases P; cases A; congr
include hp he hk
lemma signageN (r) : Beam.marquee H r= Beam.marquee I r:=by
  obtain ⟨u,c,⟨s,v,e1,k1⟩,p,b,t⟩:=R
  obtain ⟨U,C,⟨S,V,e2,k2⟩,P,B,T₁⟩:=R'
  cases hp; cases he; cases hk; rfl
include P hz
def sheetN : Magazine H ≃ Magazine I := Equiv.sumCongr P.furrow (Equiv.refl _)
lemma migrateN (d ℓ: ℕ) (i:Magazine H) : (Meadow.keepN H ℓ i ↔ Meadow.keepN I ℓ (sheetN P i)) ∧ (i∈ Meadow.bouquetN H ℓ d ↔ sheetN P i ∈ Meadow.bouquetN I ℓ d):=by
  have hK := Match.same_area (J:=I) (H:=H) hp he hk
  rcases i with z|z
  · let V:= firstBatchN (J₀:=ℓ) hp hK
    have hv (i:PoetN ℓ H): i ∈ Meadow.calendarN ℓ H d ↔ V i∈Meadow.calendarN ℓ I d:= by rw [tunesN,tunesN]; rfl
    refine ⟨not_congr (holdingsN P hp hz hK z),?_⟩
    change _↔ Sum.inl (P.furrow z) ∈_
    simp only [Meadow.bouquetN,inl_mem_disjSum,Finset.mem_map]
    constructor
    · rintro ⟨i,hi,rfl⟩; exact ⟨V i,(hv i).1 hi,(identifiesN P hp hz hK i).symm⟩
    rintro ⟨i,hi,hu⟩; obtain ⟨i,rfl⟩:= V.surjective i; exact ⟨i,(hv i).2 hi,P.furrow.injective ((identifiesN P hp hz hK i).trans hu)⟩
  change (Meadow.keepN H ℓ (Sum.inr z) ↔ Meadow.keepN I ℓ (Sum.inr z)) ∧ _
  refine And.intro (show (radiusB p<_) ↔ (radiusB p< arc T.down z) from Iff.rfl) ((Finset.inr_mem_disjSum).trans Finset.inr_mem_disjSum.symm)
lemma flyerN (i:ℕ): (pennant I i).2=sheetN P (pennant H i).2:=by
  obtain ⟨u,c,⟨s,v,e1,k1⟩,p,b,t⟩:=R
  obtain ⟨U,C,⟨S,V,e2,k2⟩,p,B,T₁⟩:=R'
  cases hp; cases he; cases hk; obtain ⟨_,_,_⟩:=P; cases hz
  have hv (i:Magazine H):sheetN (H:=H) (I:=I) (Match.staple rfl rfl rfl) i=(show Magazine I from i):=by rcases i with i|i <;> rfl
  exact (hv (pennant H i).2).symm
omit hz P in
lemma stampedN (d ℓ i: ℕ):debrisN H ℓ d i ↔ debrisN I ℓ d i:=by
  let V := staple (H:=H) (J:=I) hp he hk
  unfold debrisN; rw [flyerN V rfl hp he hk]; obtain ⟨h,hx⟩:= migrateN V rfl hp he hk d ℓ (pennant H i).2; exact and_congr (not_congr h) (not_congr hx)
variable (χ) -- order
lemma upwardN {I': Cash W p a L₀ X o U T R'} (γ:ℝ) : Song.plusone H P χ γ=Song.plusone I' (Match.staple (J:=I) rfl rfl rfl) χ γ:=by
  obtain ⟨u,c,⟨s,v,e1,k1⟩,p,b,t⟩:=R
  obtain ⟨U,C,⟨S,V,e2,k2⟩,p,B,T₁⟩:=R'
  cases hp; cases he; cases hk; obtain ⟨_,_,_⟩:=P; cases hz; rfl

end YM.PhysicalNext.Repeat.Meadow
