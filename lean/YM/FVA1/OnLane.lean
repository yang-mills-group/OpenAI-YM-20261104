import YM.FVA1.Receive
import YM.FVA1.Broaden
set_option autoImplicit false
noncomputable section
namespace YM.FVA1
open Function Filter Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Control Window Coat Footprint Raw Matter
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Stained Shield
open PhysicalNext PhysicalNext.Repeat Height Greenbelt
open Gas Ursell Trees RG.Supply Org Roost Opera
open Input Testing PriceCompiler
open AnalyticBridge VerifiedReset Collection Extra.Iteration Match Song Refrain Geo Quotes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat.Daisy.Charity.RG12
open YM.RG01.Survive
open YM.ConnectedActivityE6.Blaze.Thermal1020
open YM.ConnectedActivityE6.Blaze.Thermal1020.Shared
open UVExtension Spire Orchard Mast Oasis Progress.DirectedRecipe Mallow YM.RG12 OPE
open GridApprox.Nil Marker Merge MergeProof Accent
open YM.Overlay.GapsLocal GapsLocal Full Menu
open UVNext.CouplingReset
section receipt
variable {G:Gauge}(B:Family G)(m n N:ℕ)
set_option quotPrecheck false
local notation "E0"=> B.path.rep N n m
local notation "E1"=> B.path.rep N n (m+1)
local notation "T'"=> B.path.levels.clock.op m n

def radius := B.path.levels.clock.hatBeta (m+1)^Thermal1020.ray
local notation "Z"=>radius B m
local notation "gain" a => Z^(a+5:ℕ)
local notation "q̂" => Real.sqrt (B.path.levels.clock.forcedAllowance m)
local notation "gP" d => (Real.sqrt 2 * Pert.Asymptotics.regulatorRun B N n (m+1))^(d+1:ℕ)
-- no alias to implicit recursive witnesses in this family-facing conclusion.
-- D.whole has the full tested bin/label norm at kappa times **all** K, including zero marker.
structure StageStep (a b d:ℕ): Prop where
   coupons {T I V:Type} [Fintype I][Fintype V][Nonempty I][Nonempty V][DecidableEq V][AddCommGroup T][Module ℂ T]
     (Γ:Marker.Census V)(q:I→Menu.Hat Γ E1)(X:Controls V T)(x:Positions V (B.side (m+1) n))(w:V→ℝ)(f:I→(V→T)→ℂ)(header:V→(V→T)→ℂ)
     (hl:∀ i,SlotLinear (q i).s.val (f i)) (hu:∀ i,SlotLinear ({i}:Finset V) (header i)) (hp:∀ i y,X.Admits y→‖f i y‖≤ 1)(kX:ℝ)(hm:∀ i y,X.Admits y→w i*‖header i y‖≤ kX) (hA:∀ i,∀ j∈(q i).s.val,x.stub j⊆ (q i).M.crest)
     (hO:Extra.Multi.Occupancy ((T').ratio.parent ∘ x.origin) (B.path.levels.clock.J (m+1))) (hF:Menu.Offer x.origin q w (E1).p.B ((E1).p.supportExponent-4) (Z^a))(he:∀ i,0<w i):
     let u:=gain a; let α:=u⁻¹; let t:=u^b; let k:=q̂; let J:=Full.target a b d; let s:=(E0).p.supportExponent+1
     0<k∧ k≤1∧0<α∧ α≤1∧∃ (K:Type)(_ct:Countable K)(Δ:Coil K T Γ E0), Δ.Checks header (project T' x) ∧
       Δ.Invoice X (fun i=>α*w i) s (α*kX) 1 (k^J * (Z^(J+1))⁻¹) ((Z^(J+1))⁻¹) k ∧
       ((∀ i:Γ.Mode,i.val.card ≤ b)→ Δ.Invoice X w s (t*α*kX) t (k^J * gP d) (gP d) k) ∧
       ∀ y,(T').push (E1).beta (MenuBridge.offered q f header y)=Δ.whole.density y ∧ (∀ U,(Δ.whole.density y U).part Γ.quiet= (E0|>.eval U:ℂ))

end receipt
section producer
variable {G:Gauge}{hG:G.Simple} {X:Metals G}{D:Rolls X.p}{A:Alloy X D}{R:Factor A}{m n N:ℕ}
local notation "j0" => A.B.a.clock.J m
local notation "i0" => A.B.a.clock.J (m+1)
local notation "s0" => A.B.a.clock.hatBeta m
set_option quotPrecheck false
variable {δ:Bid.Worth}{Q:ℕ→ℝ}{p:Legato.Bandage R Q δ} {t:ℕ→ℕ}(S:Spire.Uses R hG) (K:Cellar S t p)
local notation "X*" => Cellar.yard (roseA S) K
local notation "C0" => (X*).path.rep N n m
local notation "C1" => (X*).path.rep N n (m+1)
local notation "R!" => Pert.Asymptotics.regulatorRun (X*) N n (m+1)
variable (h:m<N)
local notation "E0" => (Orchard.ray S N n m (Orchard.rose0 S) h).body
local notation "z₀"=> Orchard.beam0
local notation "W0" => Mallow.houseS E0 z₀
variable (hg:(Cellar.yard (roseA S) K).Makes)
    (hp:Mallow.RG12.Earned (PhysicalNext.Repeat.FVA1.garrison G) R.shape A.delay)(hu:Mallow.RG12.Earned (Mallow.orbitD G) R.shape A.delay)(he:Mallow.RG12.Earned (markerBudget G) R.shape A.delay)
    (hd:∀ m,(Cellar.yard (roseA S) K|>.path.levels.budget m).supportExponent≥100)
include K h hp hu he hd hg
set_option maxHeartbeats 860000 in
set_option maxRecDepth 2048 in
-- uses exact C1 & C0 throughout; supports still aligned to fixed torus, not lifted distances.
theorem stipend {a b d:ℕ} (hM:Full.target a b d+1≤ i0): StageStep (X*) m n N a b d:=by
    constructor; intro T I V _ _ _ _ _ _ _ Γ q C o w f header hL hT hq kX hm' hA hw hQ hE
    let B:= (X*)
    intro gain α bill k l cost
    have hI'(i:ℕ) (h':i≤N): B.path.Conv N n i:= hg.wilson.represents N n i h' -- spec
    have hQ' : (C0).p=A.B.a.budget m:= (hI' m h.le).vac
    have hx:= (Orchard.ponds S N n m (Orchard.rose0 S) h)
    change C0=(E0).result z₀ at hx
    let Z:= horizonRadius G (D.L i0) s0; have hz: Z=radius B m:=by
      unfold radius Z horizonRadius; refine congrArg (fun b:ℝ=> b ^ Thermal1020.ray) ?_; exact (Push.PriceCompiler.beta_eq A.B.valid m).symm
    unfold Z at hz
    have hs:= uncap hG (Q:=fun _=> S.realBeat (0:ℝ) N n (m+1)) E0 z₀ q w o f header (a:=a) (b:=b) (d:=d) C hL hT hq kX hm' hA he (minted_same R.shape hu).hold hp h p.r (hd _) (hd m) hM hw (by rw [hz]; exact hQ) hE
    dsimp only at hs; obtain ⟨ha,hb,hc,hD,hchecks,hi,hi',hF⟩:=hs
    change 0 < k at ha; change k ≤ 1 at hb
    -- shadowRadius = Z^..., exact path via ponds
    unfold Full.shadowFactor at hc hD hchecks hi hi' hF
    rw [hz] at hc hD hchecks hi hi' hF
    let J:= (W0).fragrances
    haveI : Countable J:= by unfold J Cash.fragrances Clusters Cash.ThinP; infer_instance
    refine ⟨ha,hb,hc,hD,J,inferInstance, ?_⟩
    have hC0:= (hI' m h.le).good.labels
    clear hI'
    unfold cost; rw [hx] at hC0 hQ' ⊢
    refine ⟨_,hchecks,hi,fun h=> hi' h,fun y=> ⟨hF y,fun U=>?_⟩⟩
    exact Film.quiet hi.format.1 hi.dossier hC0 y U

end producer
section
variable {G:Gauge} {g:G.Simple}{C:Family G}{δ δ':Daisy.Charity.RG12.Decal G}
abbrev prices (G:Gauge)(δ:Daisy.Charity.RG12.Decal G): Daisy.Charity.RG12.Decal G:= (PhysicalNext.Repeat.Mallow.orbitD G).paired ((PhysicalNext.Repeat.FVA1.garrison G).paired ((markerBudget G).paired δ))
-- on any aligned Couture funded these, e.g. more requests than just StageStep
lemma ofCouture (x:Couture C g δ)(hC:C.Makes)(hd:∀ m,(C.path.levels.budget m).supportExponent ≥ 100)
    (he:Mallow.RG12.Earned (prices G δ') x.factor.shape x.cost.delay) -- δ' implicit declare
    (a b d k:ℕ):
    ∀ᶠ m:ℕ in atTop, b ≤ C.path.levels.clock.J (m+1) ∧ k ≤ (C.path.levels.budget m).order ∧ k ≤ (C.path.levels.budget m).power ∧
      k ≤ (C.path.levels.budget (m+1)).order ∧ k ≤ (C.path.levels.budget (m+1)).power ∧ ∀ N p,m<N→ StageStep C m p N a b d:=by
    let B:=x.cost.B.a
    have hF:=x.belongs
    rw [hF] at hd
    have hp : Mallow.RG12.Earned (PhysicalNext.Repeat.FVA1.garrison G) x.factor.shape x.cost.delay:= fun _ _ h _ hv=> he _ _ h _ hv|>.2.1
    have hu : Mallow.RG12.Earned (Mallow.orbitD G) x.factor.shape x.cost.delay:= fun _ _ h _ hv=> he _ _ h _ hv|>.1
    have hQ : Mallow.RG12.Earned (markerBudget G) x.factor.shape x.cost.delay:= fun _ _ h _ hv=> he _ _ h _ hv|>.2.2.1
    filter_upwards [B.fits.deep.eventually_ge_atTop (max (Full.target a b d+1) b), eventually_ge_atTop (C.ref k)] with m hm hk
    have hV(m) (h:C.ref k ≤ m) : k ≤ (C.path.levels.budget m).order ∧ k ≤ (C.path.levels.budget m).power:= (by obtain ⟨he,hf⟩:=(hC.stages k).2 m h; exact ⟨(Nat.le_succ k).trans he,hf⟩)
    obtain ⟨hq,hΨ⟩:=hV _ hk; obtain ⟨hv,hz⟩:=hV _ (hk.trans (Nat.le_succ _))
    have hl:max _ _ ≤ B.clock.J (m+1):=hm.trans (step_paid B m).1
    refine ⟨?_,hq,hΨ,hv,hz,?_⟩
    · rw [hF]; exact (le_max_right ..).trans hl
    intro N n h; rw [hF]; refine stipend x.uses x.cellar (n:=n) h (hF ▸ hC) hp hu hQ hd ?_
    exact (le_max_left ..).trans hl

-- paired price coexists e.g. on Marigold.violine (need extract nested .couture).
set_option maxRecDepth 4096 in
/-- Fixed-order thermal/all-test forced supplier on an actual family and its trajectory.
All finite periods and UV cutoffs after one entrance in the observing scale. -/
theorem reserve (G:Gauge) (g:G.Simple) (penalty:ℝ)(hp:0<penalty)(F:Extraction.Order)(δ:Daisy.Charity.RG12.Decal G):
    ∃ (C:Family G)(U:Couture C g (prices G δ))(f:Extraction.Order)(T:Table C.book)(W:Spec.Final C (F.refine f) T)(L:EveryPhase.Almanac W),
    C.Makes∧Spec.Calibrated C ∧ C.path.levels.clock.kernel.penalty=penalty ∧ UVExtension.Oasis.Floral (hG:=g) C ∧ EveryPhase.Completed W L ∧ OPE.Facilities C (F.refine f) T ∧
    (Mallow.RG12.Earned δ U.factor.shape U.cost.delay) ∧
    ∀ a b d k, ∀ᶠ m:ℕ in atTop,b ≤ C.path.levels.clock.J (m+1)∧ k ≤ (C.path.levels.budget m).order ∧ k ≤ (C.path.levels.budget m).power ∧ k ≤ (C.path.levels.budget (m+1)).order ∧ k ≤ (C.path.levels.budget (m+1)).power ∧ ∀ N p,m<N→ StageStep C m p N a b d:=by
    obtain ⟨C,f,T,W,L,hM,hC,hpen,hF,_,_,hP,hU,⟨N⟩,_⟩:=YM.RG12.fashions G (prices G δ) g penalty hp F
    have ht:=N.couture
    refine ⟨C,N,f,T,W,L,hM,hC,hpen,hF,hP,hU,fun i x hx j h=> (ht i x hx j h).2.2.2, ofCouture N hM ?_ ht⟩
    obtain ⟨W,r,D,h⟩:=hU.costlier; exact fun _=> (h.support _).ge
end
end YM.FVA1
