import YM.Integration.WilsonReportCitizenRun
import YM.Integration.WilsonFundedMeasuredWindow
import YM.Pier.Scene.Integral

/-! The existing commissioned Wilson history meets every original Pier
startup condition. In particular its actual normalized marked report, with
all the sectors and their signs intact, receives the original physical
coarse integral estimate. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportSamePillars
open Filter Finset Set MeasureTheory Lattice Wilson RG Source Marker Multi Extraction
open Next.Rank MergeProof MergeProof.Ribbons.ManyCopies.Patrol RG17 RG17.Panoramic
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open scoped Topology Classical
universe u
variable {G : Gauge} {R : Run G} {T : Campaign R}

private theorem corridor (hG : G.Simple) (W : Campaign.Pillars R T) : Pier.Corridors R hG W := by
  intro d k
  exact Pier.Mooring.decksBooked R W hG d k

private theorem currency (f : Extraction.Order) (B : ℕ→ℝ)
    (beta : ∀ m : ℕ,f.limits (fun _=>True) (fun N p=>R.family.path.β N p m) (B m)) :
    PertExtension.Running.isLimit R.family f B := by
  intro m
  exact Extraction.Order.along (f:=f) (p:=fun _=>True) (L:=fun N p=>R.family.path.β N p m) (y:=B m) (beta m)

private theorem path (f : Extraction.Order) (S : Table R.family.book)
    (F : Spec.Final R.family f S) (L : EveryPhase.Almanac F)
    (P : OPE.Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (X : Climb.Scaling S) (B : ℕ→ℝ)
    (order : (Extraction.Order.mk Extraction.Sequence.full f.per).Ordered R.family S)
    (pos : FullVolume.PositionsUV R.family Extraction.Sequence.full)
    (phase : EveryPhase.Completed F L) (fac : OPE.Facilities R.family f S)
    (found : OPE.Orbits.Foundation F P) (first : Pert.FirstExtension F X)
    (beta : ∀ m : ℕ,f.limits (fun _=>True) (fun N p=>R.family.path.β N p m) (B m))
    (arch : ∀ U : Ultrafilter (ℕ×ℕ),(U:Filter _)≤f.fuse → Nonempty (SharpGram.Lenses.Mantle F (U:Filter _))) :
    Pier.OnePath R f := by
  refine ⟨S,?_⟩
  refine ⟨F,order,pos,?_⟩
  refine ⟨L,P,X,B,?_⟩
  exact ⟨phase,fac.toServices,found,first,beta,currency f B beta,arch⟩

private theorem limits {Δ : PhysicalNext.Repeat.Daisy.Charity.RG12.Decal G} (hG : G.Simple) (W : Campaign.Pillars R T)
    (broad : R2IGoals.Broad.{u} Δ W hG) (f : Extraction.Order) : Pier.LimitRoom R f := by
  obtain ⟨g,B,S,F,X,L,P,beta,order,pos,first,phase,_,fac,found,_,_,arch⟩ := broad.refine f
  exact ⟨g,path _ S F L P X B order pos phase fac found first beta arch⟩

theorem original (hG : G.Simple) (W : Campaign.Pillars R T) {δ : ℝ}
    (funding : FundedOriginalProperties.{u} hG δ W) (subsidy : WilsonReportColumnSubsidy.Eligible R.kit)
    (pace : WilsonWindowReportingPace.Slow R.kit) : Pier.Starter R hG T W := by
  refine {
    uv := funding.2.1.jewel
    pillar := funding.2.1.coverage
    flick := ⟨WilsonFundedMeasuredWindow.paced R pace⟩
    thresholds := (WilsonReportCitizenRun.on_run hG W funding subsidy).1
    corridor := corridor hG W
    limits := limits hG W funding.2.1
    reserve := ?_ }
  intro m N p d hm he x
  exact Campaign.fitsPier W hG hm he x

/-- The entire signed old fine numerator divided by its measured coarse
vacuum, minus the product of its real regular output fields on that very
same gauge sample. The conclusion bounds its full integral before all
cutoffs and periods and after all disconnected subsets are retained. -/
theorem signed (hG : G.Simple) (W : Campaign.Pillars R T) {δ : ℝ}
    (funding : FundedOriginalProperties.{u} hG δ W) (subsidy : WilsonReportColumnSubsidy.Eligible R.kit)
    (pace : WilsonWindowReportingPace.Slow R.kit) {n : ℕ} (Γ : Census (Fin n)) (d : Fin n→ℕ)
    (c e t wide : ℕ) (hw : 1≤wide) :
    ∀ᶠ k : ℕ in atTop,∀ l : ℕ,(R.family.path.levels.budget k).B^8≤l →
      (l:ℝ)≤R.family.path.levels.clock.hatBeta k^t → ∀ N p : ℕ,k<N →
      ∀ x : Fin n→Site (R.family.side k p),(∀ i j,separation (x i) (x j)≤wide*l) →
        (∀ i j,i≠j → l ≤ separation (x i) (x j)) →
      ∀ v : (j:Fin n)→R.family.label (d j),
        (∀ j,Spindle.paid R.family (d j) k N p (v j)≤R.family.path.levels.clock.hatBeta k^c) →
      ∀ s : Γ.Mode,Integrable (gapTag R N s x (recordS R d v)) (OPE.Therm.scene R.family.path N p k) ∧
        ‖∫ U,gapTag R N s x (recordS R d v) U ∂(OPE.Therm.scene R.family.path N p k)‖≤
          2^e*Pert.Asymptotics.regulatorRun R.family N p k^(2*e) :=
  RG17.Panoramic.allScenes R d (original hG W funding subsidy pace) c e t wide hw

end YM.Integration.WilsonReportSamePillars
end

