import YM.RGLocalTaylor.Consumer.After
import YM.RG01.Kernel.Caliber
/-!
# Consume the joint receipt on the common actual objects

Unmarked clause: same linked family all topology, K and denominator. Startup
and finite horizon supplies can be reused via the indicated itinerary. It's NOT a
consumer of hypothetical Wilson perturbative predictions (see status ledger).
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

-- compose nonzero/spelled-out probe. Reuse construction exact `belong`.
set_option maxHeartbeats 1000000 in
lemma witnessDenominator (S: Uses R hG) (h: Obligates S) {u:ℕ→ℕ}{w:ℕ→ℝ}{p:Bid.Worth}{b:Bandage R w p} (F:Cellar S u b)
    (hC : (Cellar.yard (roseA S) F).Makes) (q t K:ℕ) (he:8*q ≤ 7*t) :
    let C:= (Cellar.yard (roseA S) F)
    ∃ v:ℝ,0≤ v ∧
    ∀ (N m n:ℕ) (hm:m<N) (_:t+2≤ C.path.levels.clock.J (m+1)),
      let x:= S.realBeat 0 N n m
      let r:= (Orchard.ray S N n m (rose0 S) hm).body
      let g:= Pert.Asymptotics.regulatorRun C N n (m+1)
      StepCosts r Orchard.beam0 (t+2) (v*g^q) ∧
        C.path.rep N n m=x ∧ C.path.rep N n m=r.result Orchard.beam0 ∧
        g=(Real.sqrt (S.realBeat 0 N n (m+1)).beta)⁻¹ ∧ C.beta N n=(S.realBeat 0 N n N).beta ∧
        A.B.a.clock.hatBeta (m+1)^K*(A.B.a.clock.forcedAllowance m/Real.sqrt (A.B.a.clock.forcedAllowance m)) ≤ v*g^q ∧
        (∫ U,(C.path.rep N n m).eval U ∂prior G (A.B.a.S.side m n))= Wilson.partition G (C.side N n) (C.beta N n) ∧
        ∀ V: Config G (C.side m n),
          let m' := sculpture r Orchard.beam0 (t+2); let e':= effigy r Orchard.beam0 (t+2)
          let b:= estimateBeta r Orchard.beam0 (t+2); let v:= estimateScalar r Orchard.beam0 (t+2)
          0<x.eval V ∧ 0<(template x m' b v).eval V ∧
          x.eval V=Real.exp (descending x e' b v V)*(template x m' b v).eval V ∧
          Kernel.Caliber (Kernel.expense C.path N m n V) (Wilson.prior G (C.path.S.side (m+1) n)):= by
  intro C; obtain ⟨v,hv,h⟩:=h.commits q t K he
  refine ⟨v,hv,fun N m n hm he=>?_⟩; intro x r g
  obtain ⟨_,hj,hQ,hV,hy⟩:= h m N n hm he (rose0 S)
  change x=r.result Orchard.beam0 at hQ
  have he : C.path.rep N n m=x:=rfl
  refine ⟨hy,he,he.trans hQ,rfl,rfl,hV, (C.path.partition_eq hC.wilson N n m hm.le),fun V=>?_⟩
  let d:=(effigy r Orchard.beam0 (t+2))
  let b:= (estimateBeta r Orchard.beam0 (t+2)); let y:= (estimateScalar r Orchard.beam0 (t+2))
  let g':= (template x (sculpture r Orchard.beam0 (t+2)) b y).eval V
  have hp : 0 < x.eval V:= Extra.Histories.Tour.bright C.path hC.wilson N n m hm.le V
  have hx : x.eval V = Real.exp (descending x d b y V)*g' := by unfold g'; rw [hQ]; exact hy.evaluation.2 V
  exact ⟨hp,pos_of_mul_pos_right (hp.trans_eq hx) (Real.exp_pos _).le, hx, Kernel.actual N _ hC.wilson V hm⟩

open OPE
set_option quotPrecheck false
/-- Uniform all-budget AFTER kinetic re-expression of vacuum plus pre-reset
relation to the unmarked RG01.Survive pipeline. K still used unchanged, with
ALL addresses carried to both readings. Only extra power loss THREE units plus
nominal oversampling of 8/7 after all final re-expression in THIS convention.
No magic equality with a Family you've already chosen.
-/
theorem assembled2 (G:Gauge)(hG:G.Simple)(δ:Daisy.Charity.RG12.Decal G)
    (penalty:ℝ)(hp:0<penalty)(order:Extraction.Order):
    ∃ (C:Family G)(f:Extraction.Order)(T:Table C.book)(U:Spec.Final C (order.refine f) T)
      (Y:EveryPhase.Almanac U)(P:OPE.Prescription U.sector.derivatives)
      (_hq:P.Coherent)(W:Couture C hG ((Mayer.decal G).paired ((Leasing.dial G).paired δ))),
      C.Makes ∧ Spec.Calibrated C ∧
      C.path.levels.clock.kernel.penalty=penalty ∧
      UVExtension.Oasis.Floral (hG:=hG) C ∧
      EveryPhase.Completed U Y ∧ OPE.Facilities C (order.refine f) T ∧ OPE.AllShapes U P ∧
      C=Cellar.yard (roseA W.uses) W.cellar ∧ Mallow.RG12.Earned δ W.factor.shape W.cost.delay ∧
      AtCutoff W.uses C ∧ Obligates W.uses := by
  obtain ⟨C,f,T,U,L,Q,hQ,W,hM,hC,hF,hUV,hP,hA,hAll,ht,hw,hZ⟩ := assembled1 G hG ((Leasing.dial G).paired δ) penalty hp order
  exact ⟨C,f,T,U,L,Q,hQ,W,hM,hC,hF,hUV,hP,hA,hAll,ht,
    fun i x hx j hj=> (hw i x hx j hj).2,hZ,
    constructed _ (fun i x hx j hj=> ⟨(W.couture i x hx j hj).1,(hw i x hx j hj).1⟩)⟩
end YM.RGLocalTaylor.Consumer
