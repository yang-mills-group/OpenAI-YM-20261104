import YM.RGLocalTaylor.Laminate.Gallery

/-!
# Execute with BOTH real/switch motion on Spring. Post-output Hat lottery &
single histories may request additional capacity of input weight. No limiting the
number of kernels/labels, ONLY the origin-hits as specified. All actual geometry
including phase decisions and paid Reserve preserved. This is the SAME
convention as Volant/Photo and reaches their marks exponent.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor.Laminate
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration
open PhysicalNext PhysicalNext.Repeat Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost Lotus
open UVNext.CouplingReset Animals Marlin Progress.DirectedRecipe Ovens Ovens.Pipes Mallow Mallow.Many
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} (g:G.Simple) {X:Metals G} {D: Rolls X.p} {A : Alloy X D}
    {R: Factor A} {l v:ℝ} {N m n:ℕ}(hm:m<N) {Q: In A.B.a m n} (H: Spring R N m n l v Q)
local notation "I" => Icc l v
local notation "βₛ"=> A.B.a.clock.hatBeta (m+1)
local notation "L" => D.L (A.B.a.clock.J (m+1))
local notation "Θ" => A.B.a.S
local notation "J" => A.B.a.clock.J (m+1)
local notation "Jp" => A.B.a.clock.J m
local notation "K" => A.B.a.params m
local notation "wT" => radiusB (A.B.a.clock.hatBeta m)
local notation "k" => Rain.lint R.target A m
local notation "e" => Trio.base k wT
local notation "gV" => A.B.kin.alpha N m
local notation "B" => A.B.a.budget m
local notation "d" => H.ordinal
local notation "Y" => R.target J Jp
local notation "Ze" => R.expense J Jp
local notation "Cμ" => (R.shape.μ J Jp)
local notation "y" => A.B.a.clock.hatBeta m
local notation "O" => Chi.canonical
local notation "X₀" => H.H.base
local notation "S" => A.B.a.clock.op m n
variable (x: Icc l v)
local notation "hx" => x.property
local notation "W" => houseS H x
open YM.Merge
open MergeProof Menu Accent GridApprox.Nil
open Marker
variable (hE : (Q x).p.supportExponent≥100)(hN : 100≤(H.result x).p.supportExponent) (hS: Arrives R.shape A.delay) (hF : Mallow.RG12.Earned (decals G) R.shape A.delay)
local notation "ζ" => Mayer.arcRadius G L y
set_option quotPrecheck false
variable (M : ℕ)
variable (hM:M ≤ A.B.a.clock.J (m+1))

-- same Spring. output y real currency. predicate `ρ pages at that price`. No assumption on unmarked kernel path other than Garden.Proven.
structure Travels (H: Spring R N m n l v Q)(M:ℕ)(x:Icc l v):Prop where
   sails : ∀ {τ ι : Type} [_I:DecidableEq τ] [_V:Fintype τ] [_F:Fintype ι]{Cen: Marker.Census τ} (o : τ→Site (A.B.a.S.side m n))(p:ι→ Leaf (Q x)) (z:ι→ℝ) (u:τ→ℝ) (t:ι→Poly Cen),
       Month p z o t u (houseS H x) → SignedPage (houseS H x) p z o t u (pupilK H x p z) (H.result x) O M ζ (straw Cμ L G y)
   connects (m' p:ℕ) : m' ≤ J+1→ p≤J+1 → βₛ^m'*(straw Cμ L G y/Real.sqrt (A.B.a.clock.forcedAllowance m)) ≤ (ζ^p)⁻¹
   fares : Palette.shipPrice L Y y (J+1) (station βₛ)
   realStrong : 1 ≤ ζ

include g hm hF hS hM
lemma portrait : Travels H M x:=by -- include g
    have hC:=hS _ _ (A.B.valid.pays m) _ (step_paid A.B.a m)
    let a:= Ze; let p:= K; let j:= (B).order; let D':=(B).power
    have ht: Needs _ Y a L _ _ _ (X.p.profile (Jp)) J y:=(hF _ _ (A.B.valid.pays m) _ (step_paid A.B.a m)).1
    have hx0 : βₛ=betaF G y L:= PriceCompiler.beta_eq A.B.valid m
    have hv:= show Assets _ _ _ _ _ _ from (hF _ _ (A.B.valid.pays m) _ (step_paid A.B.a m)).2
    
    have hp' : J≤ J:=le_rfl
    obtain ⟨z,hZ⟩:=ht M hM
    have he : Stamp (ships A.B N m n):= Opera.protocol A.B hm R.pledging.conducts.full
    have ha:=hZ _ _ _ _ he _ _ (houseS H x)
    have hk : (X.p.profile (Jp)).order=(H.result x).p.order:=by rw [← params_eq A.B.valid]; rfl
    have hg : (X.p.profile (Jp)).power=(H.result x).p.power:=by rw [← params_eq A.B.valid]; rfl
    rw [hk,hg] at ha
    constructor
    · intro V ι _ _ _ Cen o p a u t hΘ
      have h' : (B).supportExponent+3 ≤ (Ze).earn:= by
        have he':= R.pledging.agenda _ _ (step_paid A.B.a m)|>.1; rw [Rain.jersey (A:=A) (m:=m)|>.2.2.1]; linarith
      obtain ⟨A₀,ba,q,t',z,F'₀,t₃,t₄,t₅,t₆,k',hB,hX,N₀,hN'⟩:=hC.1.2 _ _ _ _ he (Q x) _ (houseS H x)
      apply SignedPage.supplied hΘ (Many.usable g hm H x p a N₀ hS hB hΘ.graph) _ ha rfl (by change (B).supportExponent+1≤ _; linarith only [h']) (Height.asset_pos _)
      have hf := Many.crowd2 g hm H x p a N₀ (fullBudget R.shape A.delay (fun i x hQQ j hj=> (hF i x hQQ j hj).2)|>.hold) hB hΘ.graph
      exact ⟨raiser B,rfl,hf⟩
    · intro m' p hr hs; rw [hx0,Blush.glyph_eq]; exact hv.small _ _ hr hs
    · rw [hx0]; exact hv.shipped.shipping
    · obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hw,-⟩:= ha; exact hw.scale

variable {ι τ:Type} [Fintype τ][DecidableEq τ][Fintype ι]{Cen:Marker.Census τ}(o:τ→Site (A.B.a.S.side (m+1) n)) (u:τ→ℝ)(p:ι→Menu.Hat Cen (Q x))
local notation "M₀"=> fun i=> (p i).M
local notation "o0" => (S).ratio.parent ∘ o
local notation "b'"=> (B).supportExponent
local notation "T₀"=>pupilK H x M₀ (fun i=>Menu.sumFee (p i) u)
variable {U':ℝ} {N':ℕ} (hu:∀ i,0 < u i)(he':0≤U')(hU: Palette.shipPrice (D.L (A.B.a.clock.J (m+1))) (R.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) (A.B.a.clock.hatBeta m) N' U')(hi:Extra.Multi.Occupancy ((A.B.a.clock.op m n).ratio.parent ∘ o) N')
    (hq: Menu.Offer o p u (Q x).p.B ((Q x).p.supportExponent-4) U')
omit g hF hM
include hE hN hi hq hu hU he'
lemma visible : Month (fun i=>(p i).M) (fun i=>Menu.sumFee (p i) u) o0 (fun i=>Menu.sing (p i) u) u (houseS H x):=by
   have he : (B).supportExponent+3 ≤ (Ze).earn :=by
      have he':= R.pledging.agenda _ _ (step_paid A.B.a m)|>.1; rw [Rain.jersey (A:=A) (m:=m)|>.2.2.1]; linarith
   have hC:=hS _ _ (A.B.valid.pays m) _ (step_paid A.B.a m)
   let Y':= houseS H x
   obtain ⟨A₀,ba,q,t',z,F'₀,t₃,t₄,t₅,t₆,k',hB,hX,h⟩:=hC.1.2 _ _ _ _ (Opera.protocol A.B hm R.pledging.conducts.full) (Q x) _ (houseS H x)
   have hh:Palette.Plot (fun i=>(p i).M) Y' (fun i=>Menu.sumFee (p i) u):= Photo.bidding _ Cen u hu p o hC.1.1 (by rw [Y'.laws.intake.sizes, Y'.laws.data.funds.length_eq]; exact hB.covers) (by
        change 4 ≤ (Y).exp+_+_; change 100 ≤ b' at hN; linarith only [he,hN,(Ze).worth,(Ze).first,(Ze).second,(Y).usable,(Y).pos]) hE he' hq hi hU
   refine ⟨fun i=>(Menu.virtue _ _).1,fun i=>(Menu.virtue _ _).2,fun i=> ?_,hh,hu,fun i=> Menu.paid (p i) hu⟩
   have hw:(p i).s.val.image o0 ⊆ (p i).M.crest.image (S).ratio.parent:= by
      intro j hj; obtain ⟨i',hi,hj⟩:= mem_image.mp hj; subst j; exact mem_image_of_mem _ (hq.sites _ (mem_image_of_mem _ hi))
   exact scope_send _ _ _ ((Accent.room _ _ _).2 hw)
local notation "wζ" => straw Cμ L G y
open YM.Push.Local
include hF g hM
lemma season (hO : HasSlots ((Q x).p) ((Q x).activities)) : let p' := (Q x).p; let t:= fun i=>Menu.sumFee (p i) u; let r:= fun i=>Menu.sing (p i) u
       Volant (S) (sandboxK H x) N' (p'.supportExponent-4) U' (b'+1/2) (b'+1) 1 wζ ∧ Month M₀ t o0 r u W ∧ SignedPage W M₀ t o0 r u T₀ (H.result x) O M ζ wζ := by
     intro a t r; have hv:= visible hm H x hE hN hS o u p hu he' hU hi hq -- arg
     exact ⟨Many.ripe g hm H x hE hN hS (fullBudget R.shape A.delay (fun i x hQQ j hj=> (hF i x hQQ j hj).2)|>.hold) hO he' hU,hv,(portrait g hm H x hS hF M hM).sails _ _ _ _ _ hv⟩
end YM.RGLocalTaylor.Laminate
