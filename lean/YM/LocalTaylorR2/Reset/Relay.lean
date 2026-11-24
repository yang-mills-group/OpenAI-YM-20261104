import YM.LocalTaylorR2.Reset.Docket
/-!
# Final predicate here for R2 re-expression bills, reaches physical β in a superpolynomial (in χ) mesh accuracy
 -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Recoil
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Gas Ursell Trees Multiple OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection UVNext Next.Scheduling Ovens Quotes
open Extra.Iteration RG.Shoot Push.SectorMeasure Supply Input Testing Push.PriceCompiler Org UVExtension
open ConnectedActivityE6 PhysicalNext PhysicalNext.Repeat Song Spire Orchard Mast Oasis PhysicalNext.Repeat.Legato
open Pert Pert.Kinetic Tail
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Progress.DirectedRecipe Roost Opera
variable {G:Gauge} {M: Metals G} {D:Rolls M.p} {A : Alloy M D} {m j N n:ℕ} (R:Factor A) (hp:Mallow.RG12.Earned (railD G) R.shape A.delay) {hG:G.Simple} (S : Uses R hG) {t':ℕ→ℕ}{B:Bid.Worth}{P':ℕ→ℝ}{Q:Bandage R P' B}(L:Cellar S t' Q)
    (hC:(Cellar.yard (roseA S) L).Makes)
open CalendarStep

include hp hC
lemma timely (hk:Mallow.RG12.Earned (ticketD G) R.shape A.delay) (p l r:ℕ)(ε:ℝ) (hf:ε ≤1)(he:0<ε): ∀ᶠ m:ℕ in atTop,
    r ≤ (A.B.a.budget m).order ∧ r ≤ (A.B.a.budget m).power ∧ ∀ (N n:ℕ), m<N → let g:=Pert.Asymptotics.regulatorRun (Cellar.yard (roseA S) L) N n (m+1); let δ:= (A.B.a.clock.hatBeta (m+1)^p)⁻¹
      ∀ H, RG01.Vacuum.delivered S N m n H → ∀ O:Return.Wood A.B m n, Took R S L H l ε ((Real.sqrt 2*g)^((l+1:ℝ)-ε)) O ∧ Knee R S H l δ ((Real.sqrt 2*g)^((l+1:ℝ)-ε)) O := by
  filter_upwards [lasts R S L l r (ε/2) (half_pos he),corridors R S L p] with m hF hK
  refine ⟨hF.2.2.2.1,hF.2.2.2.2,?_⟩; intro N n hm g δ H hu O
  obtain ⟨ha,hb,h⟩:= hK.2 n
  exact ⟨weighs R S L hC H hk l ε O hm hf hF.1 (hF.2.1.trans (by linarith)) hu, readback R hp S L hC H O hk p l ε _ hF.1 he hf hF.2.1 hm hu (priceBoundActual R S L l hm ε hf) hK.1 ha hb h⟩

omit hp hC
open Daisy.Charity.RG12
structure UsesRail {C:Family G}{hG:G.Simple} {Δ:Decal G}(U:Couture C hG ((ticketD G).paired ((railD G).paired Δ))):Prop where
    through : Coin U
    assay : ∀ (p l r:ℕ)(ε:ℝ), 0<ε → ε ≤1 → ∀ᶠ m:ℕ in atTop,
      let A:= U.cost.B.a; let J:= U.uses
      r ≤ (A.budget m).order ∧ r ≤ (A.budget m).power ∧ ∀ (N n:ℕ), m<N →
        let t:=Pert.Asymptotics.regulatorRun C N n (m+1)
        let δ:= (A.clock.hatBeta (m+1)^p)⁻¹
        let u:=(Real.sqrt 2*t)^((l+1:ℝ)-ε)
        Nonempty (Return.Wood U.cost.B m n) ∧ (∃ H, RG01.Vacuum.delivered J N m n H) ∧ ∀ H, RG01.Vacuum.delivered J N m n H → ∀ O:Return.Wood U.cost.B m n, Took U.factor J U.cellar H l ε u O ∧ Knee U.factor J H l δ u O

lemma usesRail {C:Family G}{hG:G.Simple} {Δ:Decal G}(U:Couture C hG ((ticketD G).paired ((railD G).paired Δ)))(hC:C.Makes): UsesRail U := by
  refine ⟨coin hC U,fun p l r ε he hf => ?_⟩
  let Y:= Cellar.yard (roseA U.uses) U.cellar
  have hu : C=Y:=U.belongs
  have hP : Mallow.RG12.Earned (railD G) U.factor.shape U.cost.delay:=fun j x hx i hi => U.couture _ _ hx _ hi |>.2.1
  have hL : Mallow.RG12.Earned (ticketD G) U.factor.shape U.cost.delay:=fun j x hx i hi => U.couture _ _ hx _ hi |>.1
  filter_upwards [timely U.factor hP U.uses U.cellar ((congr_arg Family.Makes hu).mp hC) hL p l r ε hf he] with m hh
  exact ⟨hh.1,hh.2.1, fun N n hm=>by
    have hx:=hh.2.2 N n hm
    obtain ⟨H,hH⟩:=RG01.Vacuum.hasGuide U.uses (n:=n) hm
    dsimp only at hx ⊢
    refine ⟨Tree.select _ (U.cost.B.a.clock.op m n).patch.odd_side, ⟨H,hH⟩,?_⟩
    rw [show Pert.Asymptotics.regulatorRun C N n (m+1)=_ from congrArg (fun c=> Pert.Asymptotics.regulatorRun c N n (m+1)) hu]
    exact hx ⟩

/-- Keep transfer and output Shape identity tied to all-orders witness,
  refining rather than asserting unbuilt universal trajectory price. -/
theorem relay (g:G.Simple)(κ:ℝ)(hκ:0<κ)(δ:Decal G)(F:Extraction.Order) :
    ∃ (C:Family G)(f:Extraction.Order)(T:Table C.book)(W:Spec.Final C (F.refine f) T) (L:EveryPhase.Almanac W) (A:Couture C g ((ticketD G).paired ((railD G).paired δ))),
    C.Makes ∧ Spec.Calibrated C ∧ C.path.levels.clock.kernel.penalty=κ ∧ UVExtension.Oasis.Floral (hG:=g) C ∧ (Extraction.Order.mk Extraction.Sequence.full (F.refine f).per).Ordered C T ∧ EveryPhase.Completed W L ∧ OPE.Facilities C (F.refine f) T ∧ UsesRail A:= by
  obtain ⟨C,f,T,W,L,A,h₁,h₂,h₃,h₄,h₅,h₆,h₇,-⟩:= common ((railD G).paired δ) g κ hκ F
  exact ⟨C,f,T,W,L,A,h₁,h₂,h₃,h₄,h₅,h₆,h₇,usesRail A h₁⟩

set_option maxHeartbeats 800000 in
lemma delivered_step {C:Family G}{hG:G.Simple}{Δ:Decal G}(U:Couture C hG ((ticketD G).paired ((railD G).paired Δ)))(hC:C.Makes)(p l:ℕ)(ε:ℝ) (he:0<ε)(hf:ε≤1) : ∀ᶠ m:ℕ in atTop, ∀ (N n:ℕ), m<N →
        let u:=U.uses.realBeat 0 N n (m+1); let v:=U.uses.realBeat 0 N n m; let T:=(U.cost.B.a.budget m)
        let g:=Pert.Asymptotics.regulatorRun C N n (m+1); let α:= U.cost.B.kin.alpha N m
        let e:=(Real.sqrt 2*g)^((l+1:ℝ)-ε)
        ∃ H, ∃ (O:Return.Wood U.cost.B m n), RG01.Vacuum.delivered U.uses N m n H ∧
          let Q₀ := interpret U.factor H l true; let X:= Song.posting T H
          Took U.factor U.uses U.cellar H l ε e O ∧ |v.v-Collection.vac Q₀ (Song.weighty H Chi.canonical O)| ≤ e ∧
            |v.beta-(u.beta + α + Averaging.delta (X.read Q₀))| ≤ e/T.threshold^2+(U.cost.B.a.clock.hatBeta (m+1)^p)⁻¹ := by
  filter_upwards [(usesRail U hC).assay p l 0 ε he hf] with m hx N n hm u v T g α e
  obtain ⟨⟨O⟩,⟨H,hH⟩,hi⟩:= hx.2.2 N n hm
  obtain ⟨hr,hf'⟩:=hi H hH O
  obtain ⟨_,_,ha,-,hb,-⟩:=hf'.main
  refine ⟨H,O,hH,hr,hb,?_⟩
  rw [abs_le]; exact ⟨by simp only [le_sub_iff_add_le]; linarith only [ha.1],ha.2⟩

end YM.LocalTaylorR2.Recoil
