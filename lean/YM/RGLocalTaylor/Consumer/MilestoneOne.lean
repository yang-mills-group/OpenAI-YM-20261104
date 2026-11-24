import YM.RGLocalTaylor.Consumer.Early
import YM.RG12.Budget.Report
import YM.RG12.Canonical.Paired
import YM.RG12.Canonical.Before
import YM.RG12.Joint.Outcome
import YM.RG12.Burst.Fair
import YM.RG12.Orifice.Friend
import YM.RG12.Spins.Catacomb
import YM.RG12.Alidade.Contract
import YM.RG12.Joint.MeasureLimit
import YM.RG12.Tavern.Enjoy

/-!
# Uniform Taylor estimates at a Wilson cutoff

`AtCutoff` pairs the Taylor estimate for the supported interaction
logarithms with the exact coarse reconstruction on the same Wilson family.
`assembled1` puts that estimate on a construction carrying phase and OPE
data.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor.Consumer
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration RG.Shoot Push.SectorMeasure Supply Input Testing Push.PriceCompiler Org
open ConnectedActivityE6.Blaze Blaze.March Captain Silica PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Height Refrain Song
open PhysicalNext.Repeat.Greenbelt Match Roof Roost Geo Time Opera PhysicalNext.Repeat.Legato
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open RG01 RG01.Survive Daisy.Charity.RG12
open Progress.DirectedRecipe UVExtension Spire Orchard Mast Oasis
variable {G : Gauge} {X : Metals G} {D:Rolls X.p}{A:Alloy X D}{R:Roost.Factor A}
   {hG:G.Simple}

-- Quantified consumer before altering any of Family/P/her stencils. State
-- at actual vacuum transfer: same family, arbitrary other request paired in it.
-- Use through data refinements, not by identifying an older existence output with it.
structure AtCutoff (S : Uses R hG) (C : Family G) : Prop where
  itinerary (M p j:ℕ) (hp:8*p ≤ 7*(M+1)):
    ∃ c:ℝ,0≤c ∧ ∀ (N m n : ℕ),m<N→ M ≤ A.B.a.clock.J (m+1) →
      let u:=(S.realBeat 0 N n (m+1))
      let g:=Pert.Asymptotics.regulatorRun C N n (m+1)
      0<g ∧ g=(Real.sqrt u.beta)⁻¹ ∧ C.beta N n=(S.realBeat 0 N n N).beta ∧
      A.B.a.clock.hatBeta (m+1)^j * ((A.B.a.clock.forcedAllowance m) / Real.sqrt (A.B.a.clock.forcedAllowance m)) ≤ c*g^p ∧
      (∃ H: Guide A.B R.shape N m n u, Opera.Price A.B R.shape N m n u H) ∧
      ∀ O:Return.Wood A.B m n,∀ H:Guide A.B R.shape N m n u,Opera.Price A.B R.shape N m n u H →
        Issued01 H O M (c*g^p) ∧
          (S.realBeat 0 N n m).eval = coarse H O (truncated H M)*Vacuum.exponentialShare (standard H)
            (A.B.a.budget m) (remainder H M)

lemma milestone1 {w₀:Bid.Worth} {t:ℕ→ℕ} {K:ℕ→ℝ} {Q:Bandage R K w₀} {S:Uses R hG}
    (ht:Mallow.RG12.Earned (Mayer.decal G) R.shape A.delay) {C: Family G}
    (L:Cellar S t Q) (hC : C=Cellar.yard (roseA S) L) (hw:C.Makes) : AtCutoff S C := by
  subst C
  refine ⟨fun M p j hp=> ?_⟩
  obtain ⟨c,hc,h⟩:= calendar R hG ht M p j hp; refine ⟨c,hc,fun N m n hi hj=>?_⟩
  intro u g; obtain ⟨hv,hb⟩ := (S.ticking N n (Uses.centerP _)).prices (m+1) (Nat.zero_le _) hi
  obtain ⟨A,hA,hU,hH⟩:= h N m n hi hj u hv hb
  have hg:= A.laws.intake.positive; have ht:0<g:= inv_pos.mpr (Real.sqrt_pos.mpr hg)
  refine ⟨ht,rfl,rfl,hU,⟨A,hA⟩,fun i H h=>⟨hH i H h,?_⟩⟩
  exact (hw.wilson.steps N n m hi).1.trans (hH i H h).value

open OPE
/-- A single Wilson construction supports the paired `Decal` and uniform Taylor bounds for the supported pre-reset interaction logarithms. The bounds hold at sufficiently active levels, at every cutoff beyond the step and every admitted period. The reconstructed density uses the entire configuration domain. -/
theorem assembled1 (G:Gauge) (hG:G.Simple) (δ:Daisy.Charity.RG12.Decal G)
    (penalty:ℝ) (hp:0<penalty)(order:Extraction.Order) :
    ∃ (C:Family G)(f:Extraction.Order)(T:Table C.book)(U:Spec.Final C (order.refine f) T)
      (Y:EveryPhase.Almanac U)(P:OPE.Prescription U.sector.derivatives)
      (_hq:P.Coherent)(W:Couture C hG ((Mayer.decal G).paired δ)),
      C.Makes ∧ Spec.Calibrated C ∧
      C.path.levels.clock.kernel.penalty=penalty ∧
      UVExtension.Oasis.Floral (hG:=hG) C ∧
      EveryPhase.Completed U Y ∧ OPE.Facilities C (order.refine f) T ∧ OPE.AllShapes U P ∧
      C=Cellar.yard (roseA W.uses) W.cellar ∧ Mallow.RG12.Earned δ W.factor.shape W.cost.delay ∧
      AtCutoff W.uses C := by
  obtain ⟨C,f,T,U,L,hM,hC,hpen,hUV,_hF,_hV,hP,hA,⟨W⟩,Q,hQ,hAll,h⟩ :=
    YM.RG12.fashions G ((Mayer.decal G).paired δ) hG penalty hp order
  exact ⟨C,f,T,U,L,Q,hQ,W,hM,hC,hpen,hUV,hP,hA,hAll,W.belongs,
    fun i x hx j hj=> (W.couture i x hx j hj).2,
    milestone1 (fun i x hx j hj=> (W.couture i x hx j hj).1) W.cellar W.belongs hM⟩

end YM.RGLocalTaylor.Consumer
