import YM.OPE.Compatible.Grout.Marl
/-!
# E activities ignored at patch-relative wage
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Work.F03
open Bloch Laurent Progress.DirectedRecipe Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat Matter
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Gas Ursell Trees Animals Corona Daisy Leaf
open Planned.GuardedAtom.Guard
open Next.Scheduling (decay decay_summable)
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : BudgetPoint} {m : ℕ} {W a r t σ E Λ μ x κ w C s ε: ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable {X:Support f}{J:Seats F}
lemma childhood (hh: FoldsGrip F J X) (he:R.Lawful σ C Λ E w) (hε:0<ε)(ha:a+ε ≤ R.p.supportExponent) : Sable R S X a (tweak J (R.activities.additive R.p)) (2*((X.card:ℝ)*(est R.p ε*E))):=by
   obtain ⟨b,hb,h⟩:= he.labels.boundE; have hs := he.labels.regular
   let v:= R.activities.regularOccurrence R.p
   have hB i : Paced R (R.activities.reg i).support S (v i) (b i):=by
      have hp:=hs.smooth i; have hv:=hb i
      let X:=(R.activities.reg i).support; let T:= R.p.threshold
      refine ⟨fun U V ht H=>?_,masked_measurable _ _ _ hp.borel,fun k hh U=>?_,fun U=>?_⟩
      · have he : Healthy T X U ↔ Healthy T X V := by unfold Healthy; rw [Finset.disjoint_iff_inter_eq_empty,show X ∩_=X∩ RG.flags T V from H,Finset.disjoint_iff_inter_eq_empty]
        unfold v Activities.regularOccurrence; by_cases h:Healthy T X U
        · rw [masked_eq _ _ _ _ h,masked_eq _ _ _ _ (he.mp h)]; exact hp.sites U V ht
        exact (masked_ne _ _ _ _ h).trans (masked_ne _ _ _ _ (mt he.mpr h)).symm
      · unfold v Activities.regularOccurrence masked Set.indicator; simp [Healthy, hp.symmetry k U]
      unfold v Activities.regularOccurrence; by_cases h:Healthy T X U
      · rw [masked_eq _ _ _ _ h]; exact hv.2 U h [] (Nat.zero_le _) (by simp)
      rw [masked_ne _ _ _ _ h,norm_zero]; exact hv.1
   exact one_collection hh hB ((Activities.ESeries he.labels).summable) (perceive hε ha (fun i=>(hb i).1) h)
end YM.PhysicalNext.Repeat.Aroma
