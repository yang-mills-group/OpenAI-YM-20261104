import YM.RGLocalTaylor.Consumer.After
import YM.RGLocalTaylor.Laminate.Compact

/-!
# Mark/scalar/full identities at A.Purchase. Engine edition only.

After request can pay `ρ^(p)` actual-coupling, with all mask/height
cuts quotes overhead, preserving full contour through sign grammar into Volant
at REAL station. Carries unmarked Step evaluation & post allocation.Respect
number of clocks and occupancy/cap horizon. This is THE labelled Canopy
witness carrying Taylor germs prior compression (on the spine).
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
local notation "gV" => A.B.kin.alpha N m
local notation "B" => A.B.a.budget m
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

open Post Post.Worker
-- at fine beta
local notation "μ!" => (Real.sqrt (Q x).beta)⁻¹
local notation "w'" => straw Cμ L G y

include H in
lemma valueLease (K₁ r:ℕ)(hr:8*r≤7*K₁) : (ζ^K₁)⁻¹ ≤ Real.sqrt 2^r*μ!^r:= by
   have hv : βₛ= betaF G y L := PriceCompiler.beta_eq A.B.valid m; have ht : 1 < βₛ:= A.B.a.fits.delayed _
   unfold Mayer.arcRadius; rw [←hv]; have hp:= (H.knows _ hx).2; exact Mayer.pay_extra ht.le (by linarith [hp.1]) hp.2 hr
variable {α:Type}{ι τ:Type} [Fintype τ][DecidableEq τ][Fintype ι]{Cen:Marker.Census τ}(o:τ→Site (A.B.a.S.side (m+1) n)) (u:τ→ℝ)(p:ι→Menu.Hat Cen (Q x))
local notation "T0"=> fun i=> (p i).M
local notation "Y0" => fun i=> Menu.sumFee (p i) u
local notation "o!" => (S).ratio.parent ∘ o
local notation "b'"=> (B).supportExponent
local notation "q'"=> sandboxK H x
local notation "f!"=>pupilK H x T0 Y0
local notation "p₁"=> fun i=>Menu.sing (p i) u

structure UseMarks (H: Spring R N m n l v Q) (M:ℕ) (x:Icc l v) : Prop where
    slots : HasSlots (Q x).p (Q x).activities
    oracle : Volant (S) (sandboxK H x) (J+1) ((Q x).p.supportExponent-4) (station βₛ) (b'+1/2) (b'+1) 1 w'
    history : Travels H M x
    bridge : ∀ {τ ι : Type} [_I:DecidableEq τ] [_V:Fintype τ] [_F:Fintype ι]{Cen: Marker.Census τ} (o : τ→Site (A.B.a.S.side (m+1) n))(p:ι→ Menu.Hat Cen (Q x)) (u:τ→ℝ), (∀ i,0<u i) → Extra.Multi.Occupancy ((S).ratio.parent ∘ o) (J+1) → Menu.Offer o p u (Q x).p.B ((Q x).p.supportExponent-4) (station βₛ) →
       let C:=pupilK H x (fun i=> (p i).M) (fun i=>sumFee (p i) u); let t:=fun i=>Menu.sing (p i) u; let W':= houseS H x-- local notation W hygiene?
       Month (fun i=> (p i).M) (fun i=>Menu.sumFee (p i) u) ((S).ratio.parent ∘ o) t u W' ∧ SignedPage.Publishes p (sandboxK H x) ((S).ratio.parent ∘ o) u (b'+1) 1 (b'+1) w' (Photo.spine (fun i=>(p i).M) W' O (fun i=>sumFee (p i) u) Cen t) (Photo.chain (H.result x) C Cen t) (S)

variable (hh:HasSlots (Q x).p (Q x).activities)
include g hm hE hN hS hF hM hh
set_option maxHeartbeats 400000 in
lemma markUsed : UseMarks H M x:=by
   let t:= station βₛ; have hp:0<t:= Real.rpow_pos_of_pos (zero_lt_one.trans (A.B.a.fits.delayed _)) _
   have ht := portrait g hm H x hS hF M hM
   have ho:=Many.ripe g hm H x hE hN hS (fullBudget R.shape A.delay (fun i x hr j hj=> (hF i x hr j hj).2)|>.hold) hh hp.le ht.fares
   refine ⟨hh,ho,ht,fun o p u hu hf hh=>?_⟩; intro C t W'
   rename_i Cen; let s:= (fun i=> (p i).M); let f₀:=(fun i=>Menu.sumFee (p i) u)
   have he:= visible hm H x hE hN hS o u p hu hp.le ht.fares hf hh; have hh': SignedPage W s f₀ _ t u C (H.result x) O M ζ w':=ht.sails _ _ _ _ _ he
   refine ⟨he,hh'.canopyTape he p (sandboxK H x) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) ho.propagate ?_⟩
   intro U i j; obtain ⟨a,b,hr⟩:=hh'.old; obtain ⟨v,h,_⟩:=hr.gas.bought; exact Many.live H x s f₀ i U (((h i).works U).choose_spec)

omit g hm hE hN hS hF hM hh
variable {V : Rep G (A.B.a.S.side m n)} {c:ℝ} {f f':glyph G (A.B.a.S.side m n)} {a a':ℝ}
local notation "P!" => H.result x
local notation "S'!" => Real.sqrt (A.B.a.clock.forcedAllowance m)

namespace UseMarks
variable {M x} {z c : ℝ}(h:UseMarks H M x) (hc: Post.Worker.StepCosts H x M c)
include h
lemma tars (Z k d:ℕ) (hz:Z≤A.B.a.clock.J (m+1)+1) (hk:k≤A.B.a.clock.J (m+1)+1)(hd:8*d≤7*k) :
      A.B.a.clock.hatBeta (m+1)^Z * (w' / S'!) ≤ Real.sqrt 2^d * μ!^d:=
   (h.history.connects Z k hz hk).trans (valueLease H x k d hd)
omit h in
lemma readyStation : 0 < station βₛ := Real.rpow_pos_of_pos (zero_lt_one.trans (A.B.a.fits.delayed _)) _ -- omit h
local notation "Z!" => tally (Reach W)
variable (keep:(houseS H x).fragrances→ℕ→Prop)
-- use on any accepted PERIOD histogram before taking limits
lemma commuted (hu:∀ i,0 < u i)(he:Extra.Multi.Occupancy ((S).ratio.parent ∘ o) (J+1))(hp: Menu.Offer o p u (Q x).p.B ((Q x).p.supportExponent-4) (station βₛ)) (D0 E:ℕ)(ht:8*D0≤ 7*E)(hj:∀ i j,keep i j→ E≤j):
    let R:=H.result x; let X:= SignedPage.tallyTag W T0 p₁ Y0
    Towed u id (X keep O M) (B).B (b'+1) ((Real.sqrt 2)^D0*μ!^D0) ∧
    Swing o! B u (Reach W) (fun i=> stained T0 Y0 p₁ i (χ:=O) keep M) (b'+1) ((Real.sqrt 2)^D0 * μ!^D0) ∧
    Towed u (fun i=>(R.activities.forced i).support) (Photo.Fleece f! Cen p₁) (B).B (b'+1) w' ∧ Canopy (S) (sandboxK H x) o! u (b'+1) (b'+1) 1 w' p ∧ SignedPage W T0 Y0 o! p₁ u f! R O M ζ w' ∧
    ∀ i, Photo.spine T0 W O Y0 Cen p₁ i=X keep O M i + X (fun i n=>¬keep i n) O M i := by
   intro R' X; obtain ⟨ha,hp⟩:=h.bridge o p u hu he hp; have hg:= h.history.sails _ _ _ _ _ ha
   refine ⟨Towed.shrink (h:= (hg.compressed ha keep hj).1) le_rfl (valueLease H x E D0 ht) hu,((hg.exp' keep _ hj).larger (valueLease H x E D0 ht)),hg.all, hp.canopy,hg,fun i=>?_⟩
   exact funext fun V=> (hg.spinPull ha keep i V).trans (add_comm ..)

-- taking in exponent of unmarked model AFTER all. No estimate on difference of playsOut with template (relative denominator) under aesthetically changed marks -- just restore.
def coupledLog (H : Spring R N m n l v Q)(x:Icc l v)(M:ℕ)(U:Config G (A.B.a.S.side m n)) :ℝ := descending (H.result x) (effigy H x M) (estimateBeta H x M) (estimateScalar H x M) U+(template (H.result x) (sculpture H x M) (estimateBeta H x M) (estimateScalar H x M)).exponent U
omit h
-- proof from Combine.lean internal
include hc
lemma exactLocal (U:Config G (A.B.a.S.side m n)): (P!).exponent U=coupledLog H x M U:=by
   let X:= P!; let f:=sculpture H x M; let e':=effigy H x M
   have hr:= hc.link.bundle.point
   have he:(imprint X.activities e').Valid X.p _ _:= hr.symm ▸ hc.acceptsTail
   have hm:(imprint X.activities f).Valid X.p _ _:=hr.symm ▸ hc.acceptsMain
   let Φ:= (estimateScalar H x M); let F:=estimateBeta H x M
   have hi : X.activities.additive X.p U= (imprint X.activities e').additive X.p U+(imprint X.activities f).additive X.p U:= by
      simp only [Activities.additive]; rw [← Summable.tsum_add ((Activities.ESeries he).summable U) ((Activities.ESeries hm).summable U)]
      apply tsum_congr; intro i
      let T := X.p.threshold; let S0:= (X.activities.reg i).support
      change masked T S0 (X.activities.E i) U= masked T S0 (e' i) U + masked T S0 (f i) U
      rw [show X.activities.E=f+e' from hc.assembled]; by_cases hp:Healthy T S0 U <;> simp [masked_eq,masked_ne,hp,add_comm]
   change X.exponent U=descending X e' F Φ U+(template X f F Φ).exponent U
   unfold Rep.exponent descending template; simp only [hi]; rw [BetaTransport.channels_split,BetaTransport.channels_split (b:=F)]; ring

include h
lemma holdsMarks (hu:∀ i,0<u i)(he:Extra.Multi.Occupancy ((S).ratio.parent ∘ o) (J+1))(hp: Menu.Offer o p u (Q x).p.B ((Q x).p.supportExponent-4) (station βₛ)) (U: Config G (A.B.a.S.side m n)): let t:= renter W T0 Y0 p₁ O; let f:= fun i=>Photo.Fleece f! Cen p₁ i U
      (S).push (Q x).beta (Menu.Expense p u S) U=(↑(Real.exp (coupledLog H x M U)):ℂ) • (Poly.pass (∑' i,(t (fun i k=>¬keep i k) M i U+t keep M i U))*∑' i,Photo.fronts (P!).activities f U (P!).p i):=by
   intro t f; have hg:= h.history.sails _ _ _ _ _ ((h.bridge o p u hu he hp).1); rw [← exactLocal H hc U]; exact congr_fun (hg.holds keep) U
end UseMarks
end YM.RGLocalTaylor.Laminate
