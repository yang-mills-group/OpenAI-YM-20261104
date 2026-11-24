import YM.LocalTaylorR2.Earned
import YM.LocalTaylorR2.ShortRoute
import YM.RG12.Joint.MeasureLimit
/-!
# Pre-kinetic-reset Taylor (interaction expansion) on the same construction
for all orders + all finite real field derivative budgets at Posting (E6).
Actual normalized Family. See documentation for why this does not
claim all-order physical matching or the stronger marker/correlation
statements. This milestone prices the vacuum.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.CalendarStep
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Gas Ursell Trees Multiple OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open ConnectedActivityE6 Shell Coat SliceRows Control Pulse Mask Raw Matter Pond
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration RG.Shoot Push.SectorMeasure Supply Input Testing Push.PriceCompiler Org
open ConnectedActivityE6.Blaze Blaze.March Captain Silica PhysicalNext PhysicalNext.Repeat Height Refrain Song
open PhysicalNext.Repeat.Greenbelt Match Roof Roost Geo Time Opera
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Progress.DirectedRecipe RG01.Vacuum Tail RG01.Survive
variable {G : Gauge}
open UVExtension Spire Orchard Mast Oasis PhysicalNext.Repeat.Legato

-- Coin theorem kept for any additional Decal demand. This keeps compatibility
-- with any further f756 witness that CHOOSES both requests together.
structure Coin {C:Family G}{g:G.Simple}{δ: Daisy.Charity.RG12.Decal G}(U:Couture C g ((ticketD G).paired δ)):Prop where
    path : C=Cellar.yard (roseA U.uses) U.cellar
    makes : C.Makes
    chronicles : C.path = spine U.factor U.uses
    heat : ∀ (l r K p : ℕ) (ε:ℝ),0<ε → ε≤1 → ∃ B:ℝ, 0≤B ∧ ∀ᶠ m:ℕ in atTop,
      let A:= U.cost.B.a; let J:= U.uses
      r ≤ (A.budget m).order ∧ r ≤ (A.budget m).power ∧ ∀ (N n:ℕ), m<N →
        let t:=Pert.Asymptotics.regulatorRun C N n (m+1)
        let w:=A.clock.forcedAllowance m
        (0<t ∧ A.clock.hatBeta (m+1)^K*(w/Real.sqrt w) ≤ B*t^p) ∧
        Nonempty (Return.Wood U.cost.B m n) ∧ (∃ H, RG01.Vacuum.delivered J N m n H) ∧ ∀ H, RG01.Vacuum.delivered J N m n H → ∀ O:Return.Wood U.cost.B m n, Took U.factor J U.cellar H l ε ((Real.sqrt 2*t)^((l+1:ℝ)-ε)) O

lemma coin {C:Family G} (hC:C.Makes) {g:G.Simple} {δ: Daisy.Charity.RG12.Decal G} (U:Couture C g ((ticketD G).paired δ)): Coin U:= by
   let Y:= Cellar.yard (roseA U.uses) U.cellar
   have he:C=Y:=U.belongs
   -- dependent: U itself defined with C. no subst!
   have hp : C.path = spine U.factor U.uses:= (congr_arg Family.path he).trans (path_eq U.factor U.uses U.cellar)
   have hY : Y.Makes:= (congr_arg Family.Makes he).mp hC
   refine ⟨he,hC,hp,?_⟩
   have h : Mallow.RG12.Earned (ticketD G) U.factor.shape U.cost.delay:=fun j x hx i hi=> U.couture j x hx i hi |>.1
   intro l r K p ε hv hε; obtain ⟨B,hB,hX⟩:= redeemed U.factor U.uses U.cellar hY h l r K p ε hv hε
   refine ⟨B,hB,hX.mono ?_⟩; intro m hm A J
   refine ⟨hm.1,hm.2.1,fun N n hv=>?_⟩
   have hr: Pert.Asymptotics.regulatorRun C N n (m+1)=Pert.Asymptotics.regulatorRun Y N n (m+1):= congr_arg (fun C=> Pert.Asymptotics.regulatorRun C N n (m+1)) he
   rw [hr]; exact hm.2.2 _ _ hv

/-- Simultaneously with the full-cutoff UV and prescribed ordinary OPE
 facilities at **this** family's supported domain (exact as in fashions),
 the E6 early-log expansion estimates. -/
theorem common (δ:Daisy.Charity.RG12.Decal G)(g:G.Simple) (κ:ℝ)(hk:0<κ)(F:Extraction.Order) :
    ∃ (C:Family G)(f:Extraction.Order)(T:Table C.book)(W:Spec.Final C (F.refine f) T) (L:EveryPhase.Almanac W) (A:Couture C g ((ticketD G).paired δ)),
      C.Makes ∧ Spec.Calibrated C ∧ C.path.levels.clock.kernel.penalty=κ ∧ UVExtension.Oasis.Floral (hG:=g) C ∧ (Extraction.Order.mk Extraction.Sequence.full (F.refine f).per).Ordered C T ∧ EveryPhase.Completed W L ∧ OPE.Facilities C (F.refine f) T ∧ Coin A:=by
   obtain ⟨C,f,T,W,L,h₁,h₂,h₃,h₄,h₅,-,h₆,h₇,⟨A⟩, -⟩:= RG12.fashions G ((ticketD G).paired δ) g κ hk F
   exact ⟨C,f,T,W,L,A,h₁,h₂,h₃,h₄,h₅,h₆,h₇,coin h₁ A⟩

set_option maxHeartbeats 600000 in
/-- Strict also instantiate at one arbitrary horizon and derivative and verify K
and quadratic costs after conversion to the stated power. -/
lemma sample {C:Family G}{g:G.Simple} {Δ:Daisy.Charity.RG12.Decal G}(U:Couture C g ((ticketD G).paired Δ))(hC:C.Makes)(l r:ℕ) (ε:ℝ)(hv:0<ε)(hh:ε≤1) : ∀ᶠ m:ℕ in atTop,
      let b:=U.cost.B.a.budget m
      r ≤ b.order ∧ ∀ (N n:ℕ), m<N →
        let R:= U.uses.realBeat 0 N n m
        let t:= Pert.Asymptotics.regulatorRun C N n (m+1); let E:=(Real.sqrt 2*t)^((l+1:ℝ)-ε)
        let w:=U.cost.B.a.clock.forcedAllowance m
        ∃ (H: Guide U.cost.B U.factor.shape N m n (U.uses.realBeat 0 N n (m+1))) (O: Return.Wood U.cost.B m n), RG01.Vacuum.delivered U.uses N m n H ∧
          let x:= interpret U.factor H l true; let y:= interpret U.factor H l false; let J:=Song.posting b H
          R.eval=coarse H O x*exponentialShare J b y ∧ (∀ V,0<R.eval V) ∧
            (∫ V,R.eval V∂prior G (U.cost.B.a.S.side m n)) = Wilson.partition G (U.cost.B.a.S.side N n) (U.uses.realBeat 0 N n N).beta ∧
            (J.read y).EBound b E ∧ y.hardRead=x.hardRead ∧ (J.read x).KBound b w ∧
            b.threshold^2 *|Averaging.delta (J.read y)| ≤ E := by
   obtain ⟨_,_,hk⟩:= (coin hC U).heat l r 1 1 ε hv hh; filter_upwards [hk] with m h b
   dsimp only at h; refine ⟨h.1,fun N n hv=>?_⟩; obtain ⟨-,⟨O⟩,⟨H,hH⟩,hK⟩:= h.2.2 N n hv
   have hp:= hK H hH O; obtain ⟨_,ha,hb,hX,_,hr,hF,_,_,_,ht⟩:=hp.parts
   refine ⟨H,O,hH,hp.den.trans hX,hp.pos,?_,hr.unweighted,hb.symm.trans ha,localK hF,ht⟩
   rw [hp.den]; exact hp.norm
end YM.LocalTaylorR2.CalendarStep
