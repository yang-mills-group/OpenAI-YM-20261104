import YM.RGLocalTaylor.Consumer.MilestoneTwo
import YM.RGLocalTaylor.Laminate.State
import YM.UVExtension.Pier.Haven

/-!
# Complete marks budget alongside unmarked on post-reset density.

Same constructed objects as previous stages (with strengthened delay purchase。
NOT same output as any arbitrary old Couture). See scoped ledger. Quantitative
local effective PAID interaction Taylor after supported post-E/K allocation, all
positive sources in Scope Trip.Price. Not yet full LOCAL request.
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
open RG01 RG01.Survive Daisy.Charity.RG12 Post Post.Worker
open Progress.DirectedRecipe UVExtension Spire Orchard Mast Oasis
variable {G : Gauge} {X : Metals G} {D : Rolls X.p}{A:Alloy X D}{R:Roost.Factor A}{L : Side}
    {hG:G.Simple} {δ:Decal G}

open OPE Mallow Laminate MergeProof Merge Blush
set_option quotPrecheck false
/-- Read gateway on the ACTUAL Family. cutoff-limited uniform as specified through
`κ≤ clock.J (m+1)+1`. Real beta/g at finest incoming step (Pert.Asymptotics).
Molecules include all Cream and Dilution. Uniform also across `Rose`, though
not asserting that a calibrated UV Flotilla chooses THIS Rose other than zero.
Keep support delta ≥ as specified in Funds & Knot.
-/
structure Obligates3 (S: Uses R hG) : Prop where
  enrolls (p d j:ℕ)(h:8*p≤7*d) : ∃ c : ℝ, 0 ≤ c ∧ ∀ (m N n : ℕ) (hm : m<N) (_hM : d+2 ≤ A.B.a.clock.J (m+1)) (b : Rose S),
     let U:= S.realBeat b.val N n m; let V:= S.realBeat b.val N n (m+1); let t:= (Real.sqrt V.beta)⁻¹
     let x:= (Orchard.ray S N n m b hm).body
     let κ:= straw (R.shape.μ (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) (D.L (A.B.a.clock.J (m+1))) G (A.B.a.clock.hatBeta m)
     let w:= A.B.a.clock.forcedAllowance m; let v:= Real.sqrt w
     0<V.beta ∧ 0<t ∧ 0<v ∧ U=x.result Orchard.beam0 ∧
     StepCosts x Orchard.beam0 (d+2) (c*t^p) ∧
     UseMarks x (d+2) Orchard.beam0 ∧
     ∀ k≤A.B.a.clock.J (m+1)+1, A.B.a.clock.hatBeta (m+1)^j*(w/v) ≤ c*t^p ∧ A.B.a.clock.hatBeta (m+1)^k*(κ/v) ≤ c*t^p

lemma enroll {C':ℕ→ℝ}{w':Bid.Worth} (W : Bandage R C' w') {S:Uses R hG} (hz: Mallow.RG12.Earned (decals G) R.shape A.delay) (hx:Obligates S) (hyX:∀ i,100≤(A.B.a.budget i).supportExponent): Obligates3 S := by -- replace vars
  constructor
  intro p d K hp
  obtain ⟨c,hc,h⟩:=hx.commits p d K hp
  let c':= Real.sqrt 2^p; have hc':0≤ c':=by unfold c'; positivity
  refine ⟨c+c',add_nonneg hc hc',fun m N n hm hM b=> ?_⟩; intro U V t x κ w v
  obtain ⟨hv,he,hh,hk,hW⟩:=h m N n hm hM b
  have ht :0≤ t^p:=pow_nonneg he.le _
  have hy := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (a:=c) hc') ht
  have ha:UseMarks x (d+2) Orchard.beam0:=by
     have htV : V.p=(A.B.a.budget (m+1)) := ((S.ticking N n b.2).prices (m+1) (Nat.zero_le _) hm).1.point
     apply markUsed hG hm x Orchard.beam0 _ (show 100 ≤ (A.B.a.budget m).supportExponent from hyX m) W.r hz (d+2) hM (UVExtension.Pier.poss S N n (m+1) b hm) -- args
     change 100 ≤ V.p.supportExponent; rw [htV]; exact hyX _
  refine ⟨hv,he,(Real.sqrt_pos.mpr (Real.exp_pos _)),hh,(hW.weaken hy),ha,fun k hhK => ⟨hk.trans hy,(UseMarks.tars _ ha k d p hhK (by omega) hp).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hc) ht)⟩⟩

-- retains StepCosts (native & compressed) through Use. Any stronger
-- diagonal/exponent laser WILL require new Deco. See Aims.
variable {C:Family G} (L : Couture C hG δ)
lemma allowancePrice {F:Extraction.Order}{T:Table C.book}(hC:Facilities C F T) (i:ℕ) : (L.cost.B.a.budget i).supportExponent=100:=by
    obtain ⟨W,r,D,h⟩:=hC.costlier; have hp:= h.support i
    change (C.path.levels.budget i).supportExponent=100 at hp
    -- rewrite only C with proof.growth keep L.cellar via change
    rw [L.belongs] at hp; exact hp
variable (G hG δ)
theorem assembled3 (penalty:ℝ)(hp:0<penalty)(order:Extraction.Order):
    ∃ (C: Family G)(f:Extraction.Order)(T:Table C.book)(U:Spec.Final C (order.refine f) T)
      (Y:EveryPhase.Almanac U)(P:OPE.Prescription U.sector.derivatives)
      (_hq:P.Coherent)(W:Couture C hG ((Mayer.decal G).paired ((Leasing.dial G).paired ((decals G).paired δ)))),
      C.Makes ∧ Spec.Calibrated C ∧
      C.path.levels.clock.kernel.penalty=penalty ∧
      UVExtension.Oasis.Floral (hG:=hG) C ∧
      EveryPhase.Completed U Y ∧ OPE.Facilities C (order.refine f) T ∧ OPE.AllShapes U P ∧
      C=Cellar.yard (roseA W.uses) W.cellar ∧ Mallow.RG12.Earned δ W.factor.shape W.cost.delay ∧
      AtCutoff W.uses C ∧ Obligates W.uses ∧ Obligates3 W.uses := by
  obtain ⟨C,f,T,U,L,Q,hQ,W,hM,hC,hF,hUV,hP,hA,hAll,ht,hw,hZ,h2⟩ := assembled2 G hG ((decals G).paired δ) penalty hp order
  exact ⟨C,f,T,U,L,Q,hQ,W,hM,hC,hF,hUV,hP,hA,hAll,ht,
    fun i x hx j hj=> (hw i x hx j hj).2,hZ,h2,enroll W.bandage (fun i x hx j hj=>(hw i x hx j hj).1) h2 (fun i=>(allowancePrice W hA i).ge)⟩
end YM.RGLocalTaylor.Consumer
