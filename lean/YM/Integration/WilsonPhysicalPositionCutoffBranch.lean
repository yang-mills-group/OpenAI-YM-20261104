import YM.Integration.WilsonPhysicalPositionDirectedAperture
import YM.Integration.WilsonPhysicalPositionDirectedPins

/-! A fixed tolerance for a single directed overlap on the actual unconditioned
cutoff fields selects the identity branch throughout every bounded interval of
radius ratios. The regulator limit is taken first at each pair of radii. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalPositionCutoffBranch
open Function Set
open Filter Function Set Finset Lattice Wilson RG Cells Extraction Spec Table PhysicalNext.Repeat.Legato Climb
open OPE OPE.Orbits Maxwell MS Trace.Target Trace Trace.Pilot Extra PhysMS PhysMS.Frame XSpace XSpace.Normalize
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonPhysicalPositionDirectedPins (ruler cutoff)
open WilsonPhysicalPositionDirectedTest (baseline)
open scoped Classical BigOperators Topology
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family f S)(J:ℝ→tower S){ℓ:Ultrafilter (ℕ×ℕ)}
    {H:(Bel R.family.book).Hierarchy}{arch:Trace.Terrace.Arch R.family}{D T:ℕ}
set_option quotPrecheck false
local notation "X" => (Bel R.family.book).Field

theorem original (simple:G.Simple)(below:(ℓ:Filter (ℕ×ℕ))≤f.fuse)
    (lead:Leading F J)(V:Store G)(k:Fin (D+1))
    (avoid:Finset E4)
    (j:ℝ→ℝ→ℕ)(ceiling:ℝ→ℝ)(pos:∀ᶠs in trail,0<ceiling s)(small:Tendsto ceiling trail (𝓝 0))
    (mesh:∀ᶠr in trail,∀t∈Icc (1/2:ℝ) 1,
      0<R.family.S.a (j r t)/(t*r) ∧ R.family.S.a (j r t)/(t*r)≤ceiling (t*r)):
    ∃v:X k.val,WilsonPhysicalPositionAdmissible.real R.family k.val v=v ∧ ∃a:ℝ,0<a ∧
      ((∀ᶠr in trail,∀t∈Icc (1/2:ℝ) 1,
         ∃B:(i:Fin 2)→Book F (l:=ℓ) H arch D T (ruler r t i),
         ∀ᶠ z in (ℓ:Filter (ℕ×ℕ)),baseline v-a≤cutoff F J k r t B v avoid (j r t) z)→
       ∀c:ℝ,0<c→WilsonPhysicalPositionHalfRange.uniform J k.val c):=by
  obtain ⟨v,hv,a,ha,branch⟩:=WilsonPhysicalPositionDirectedTest.original F J lead V k.val
  have ep:0<a/3:=by linarith only [ha]
  refine ⟨v,hv,a/3,ep,?_⟩
  intro measured
  apply branch
  let step(r t:ℝ):ℝ:=R.family.S.a (j r t)/(t*r)
  have uniform:=WilsonPhysicalPositionDirectedAperture.original F J v avoid lead step ceiling pos small mesh ep
  filter_upwards [measured,uniform,self_mem_nhdsWithin] with r received error hr
  intro t ht
  have positive:0<t*r:=mul_pos ((show (0:ℝ)<1/2 by norm_num).trans_le ht.1) hr
  obtain ⟨B,observed⟩:=received t ht
  have full:=WilsonPhysicalPositionDirectedPins.original F J k r t B v avoid (j r t) simple below positive
  have lower:baseline v-a/3≤WilsonPhysicalPositionDirectedAperture.reading F J v avoid (step r t) r t:=
    ge_of_tendsto full observed
  have upper:=(abs_lt.mp (error t ht)).2
  linarith only [lower,upper,ha]

end YM.Integration.WilsonPhysicalPositionCutoffBranch
end
