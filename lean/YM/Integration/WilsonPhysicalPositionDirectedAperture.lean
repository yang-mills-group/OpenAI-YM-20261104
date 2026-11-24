import YM.Integration.WilsonPhysicalPositionDirectedGrid
import YM.Integration.WilsonPhysicalPositionDirectedTest
import YM.Integration.WilsonOriginalPublicRelativeGramAddresses

/-! Uniform removal of the common reporting mesh for the genuine directed
two-home detector on its whole compact interval of scale ratios. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalPositionDirectedAperture
open Function Filter Set Finset Spec Table Extraction Maxwell Maxwell.Free OPE OPE.Orbits Climb Trace.Pilot PhysMS XSpace XSpace.Normalize
open WilsonPhysicalPositionReflectedReturn (ports sites)
open WilsonPhysicalPositionDirectedReturn (cross)
open WilsonPhysicalPositionUniformBranches (change)
open WilsonOriginalPublicRelativeGramAddresses (shape)
open private overInterval evaluated from YM.Integration.WilsonPhysicalPositionDirectedTest
open scoped Classical Topology BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
variable (F:Final C f S)(J:ℝ→tower S){d:ℕ}(v:(Bel C.book).Field d)(avoid:Finset E4)

def reading (step r t:ℝ):ℝ:=∑s:Signed,(WilsonPhysicalPositionMixedRead.value F J
  (fun i:Fin 2=>decide (i=0)) (ports (C:=C) v s) (shape avoid sites step) r t).re

theorem original (lead:Leading F J)(mesh:ℝ→ℝ→ℝ)(ceiling:ℝ→ℝ)(positive:∀ᶠr in trail,0 < ceiling r)
    (small:Tendsto ceiling trail (𝓝 0))
    (h:∀ᶠr in trail,∀t∈Icc (1/2:ℝ) 1,0 < mesh r t ∧ mesh r t ≤ ceiling (t*r))
    {ε:ℝ}(ep:0<ε):
    ∀ᶠr in trail,∀t∈Icc (1/2:ℝ) 1,|reading F J v avoid (mesh r t) r t-cross F J v r t|<ε:=by
  let X:=(Bel C.book).Field d
  letI : NormedAddCommGroup (X→L[ℂ]X):=ContinuousLinearMap.toNormedAddCommGroup
  letI : ProperSpace (X→L[ℂ]X):=FiniteDimensional.proper ℂ _
  obtain ⟨B,hB,price⟩:= Frame.comparison F d J lead
  let safe(r t:ℝ):ℝ:=if t∈Icc (1/2:ℝ) 1 then mesh r t else ceiling (t*r)
  let loss(r t:ℝ):ℝ:=reading F J v avoid (safe r t) r t-cross F J v r t
  have ok:=overInterval (E:=X→L[ℂ]X) (B:=B) (change J d) loss (show (0:ℝ)<1/2 by norm_num) ep
  have stamped:∀ᶠr in trail,∀t∈Icc (1/2:ℝ) 1,|loss r t|<ε:=by
    apply ok
    · filter_upwards [price (1/2) (by norm_num)] with r paid
      exact fun t hi=>ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans hB) (paid t hi).1
    intro r t u hr hu ht pos Z hz
    have base:Tendsto (fun i=>t i*r i) atTop trail:=by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨?_,?_⟩
      · simpa only [mul_zero] using ht.mul (hr.mono_right nhdsWithin_le_nhds)
      filter_upwards [hr.eventually self_mem_nhdsWithin] with i hi using mul_pos (pos i) hi
    have financed:∀ᶠi in atTop,0 < safe (r i) (t i) ∧ safe (r i) (t i) ≤ ceiling (t i*r i):=by
      filter_upwards [hr.eventually h,base.eventually positive] with i paid keep
      by_cases hi:t i∈Icc (1/2:ℝ) 1
      · simpa only [safe,if_pos hi] using paid (t i) hi
      · simpa only [safe,if_neg hi,le_refl,and_true] using keep
    have vanishes:Tendsto (fun i=>safe (r i) (t i)) atTop (𝓝 0):=
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (small.comp base)
        (financed.mono fun _ p=>p.1.le) (financed.mono fun _ p=>p.2)
    have shapeLimit:=WilsonOriginalPublicRelativeGramAddresses.limit avoid sites (financed.mono fun _ p=>p.1) vanishes
    have acts (w:X):Tendsto (fun i=>Frame.cocycle d J (r i) (t i) (pos i) w) atTop (𝓝 (Z w)):=
      evaluated (E:=X) (A:=fun i=>change J d (r i) (t i) (pos i)) (T:=Z) hz w
    exact WilsonPhysicalPositionDirectedGrid.original F J lead hr hu ht pos Z.toLinearMap acts v _ shapeLimit
  filter_upwards [stamped] with r paid
  exact fun t ht=>by simpa only [loss,safe,if_pos ht] using paid t ht

end YM.Integration.WilsonPhysicalPositionDirectedAperture
end
