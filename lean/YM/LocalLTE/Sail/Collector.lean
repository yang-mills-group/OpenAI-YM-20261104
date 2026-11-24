import YM.LocalLTE.Sail.Forecourt
import YM.LocalLTE.Sail.Gallery
import YM.MergeProof.South.Window
/-!
# Bank collected at epoch. staging API; interprets `Trial` through the arc table.

Single and mixed proof purchases at the same *interleaved glyphs*. Supplies
actual closed input expansion for plant. Includes representation of current M panel
with all required costs under Π pricing.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Bandage Mallow Coterie
open YM.MergeProof YM.LocalLTE.Vinca YM.LocalLTE LocalLTE.Ticket LocalLTE.River LocalLTE.Sail
open MergeProof Menu Accent MeasureTheory
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{X:Metals G}{D:Rolls X.p}{A:Alloy X D}{P:Bolt A}{R:Factor A}
variable {C:ℕ→ℝ}{W:Bid.Worth}{l:ℕ}(U:Harmonics R C W P l)
local notation "H"=> Issue.trail P
variable {N n m:ℕ}(V:∀ d,Extra.Histories.Music ((Labels.frames G).level d) (Issue.trail P) N n)
    (r0:ℕ→ℕ)(hV:∀ d,d+3 ≤ (Issue.trail P).levels.clock.J (r0 d))
open Spiral Pressure ConnectedActivityE6
variable {M p0 r q TT K P0 :ℕ}{κ ζ ε:ℝ}{AX: Almanac}(hr: Spiral.Chronicles R.shape M κ q l r p0 TT ε A.delay AX)(hp: Market M K P0 p0 TT l G ζ A.delay)
variable (hκ:∀ N m n:ℕ,∀ hm:m<N, (U.port N m n hm).ac=M ∧ (U.port N m n hm).ranch.allocation.κ=κ)
variable (hG:G.Simple)(hL:∀ i j,(R.target i j).halo=500)(hl:East.stagnate q 500<l) (he:0<ζ)
variable {I:Type} [DecidableEq I][Fintype I]
    (B:Marker.Census I)(Y:Batch (Issue.trail P) N n I)(v₀:I)
    (h:Y.Roles V m W r0 K)
variable (hR:∀ d, r0 d ≤ N → Registers U V d (r0 d))
variable {i:ℕ}(hm:i<N)
set_option quotPrecheck false
local notation "T"=> (U.port N i n hm)
local notation "D'"=> (U.deed N n i hm)
local notation "I'"=> A.B.a.clock.J i
local notation "J'"=> A.B.a.clock.J (i+1)
local notation "X'"=> X.p.profile J'
local notation "P₀"=> X.p.profile I'
local notation "x"=> A.B.a.clock.hatBeta i
local notation "y"=> A.B.a.clock.hatBeta (i+1)
local notation "u"=> N-(i+1)
local notation "L"=> D.L J'
local notation "Pt"=> y^(grantZ p0 TT u)
local notation "t"=> intakeWeight u y
local notation "rV"=> fun _:I=>t
local notation "o"=> Y.origin (i+1)
local notation "F"=> (Y.requested V (i+1))
local notation "F'"=> (Y.requested V i)
local notation "Xτ"=> (T).houseB
local notation "P'"=> A.B.a.S.side (i+1) n
local notation "s₀"=> (Issue.trail P).rep N n (i+1)
local notation "s"=> (Issue.trail P).rep N n i
local notation "Q"=> A.B.a.clock.op i n
-- Basis ports.R. Π unchanged for customer input proofs. Does NOT require same Lag Y at each request.W.Ed.
variable {z: GuideF}{Tt:ℕ→Mallow.ConcertZ R.target M ζ}(hU: Mobility AX R.shape A.delay z Tt K l TT κ)
-- chosen alphabet before Honor.ALL legal requests even arbitrary pilots.
variable (π:Y.steering i) (π':Y.steering (i+1))
local notation "K'"=> (fun j=> (Y.named V π j).forced)
local notation "Kℓ"=> (fun j=> (Y.named V π' j).forced)
local notation "g"=> (Z0)
local notation "e₀"=> z J' I' u
local notation "level"=> salesD z K u J' I'
local notation "Pz"=> allocationK y ζ
local notation "κ₁"=> Real.sqrt (A.B.a.clock.forcedAllowance (i+1))
local notation "L'"=> ((D.L J').val)* Pressure.radiusB x
variable (q':Appendix B ((Issue.trail P).rep N n (i+1)))
local notation "X₀"=> gust (H) N n N (Batch.raw Y B) (i+1) hm
structure Armed (z:GuideF) (e κ:ℝ):Prop where
   portrait: Appendix.Prepared B s₀ q' o F (fun j=> (Y.named V π' j).forced) X₀
   floor: Appendix.Budget B s₀ q' rV (allocationF y) (allocationK y e) (allocationK y e) (allocationF y) κ₁
   cap: Port.Shine B q'.model (z J' I' u) L' κ
-- capsule usage.Plant independent.Ac accounting.
variable {J:Type}[Fintype J](Pζ:J→Menu.Hat B (U.port N i n hm).inPort) (φ:J→ Config G (A.B.a.S.side (i+1) n)→ℝ)(v:I→ℂ)(φx:I→ YM.MergeProof.Response G (A.B.a.S.side i n))(Yx:J→Prop)
local notation "µ"=> (y^aust)
local notation "υ"=> (y^ (-(1:ℝ)))
-- issue heads.L.Atomic. τ in w=m.Demand.
noncomputable abbrev Serum (κ ζ:ℝ)(K:ℕ)(z:GuideF): Prop := Capsule I B (T).inPort (T).output (T).door Q X₀ o rV µ υ κ (y^ζ) K (salesD z K u J' I') L' v F' K' Pζ φ Yx φx
-- cast Binder.Display.charge
local notation "sK"=> (fun h:I=> profile (s₀).activities (Kℓ h))
local notation "sX"=> (fun h:I=> profile (s).activities (K' h))
-- challenge eligibility does not give output replies!
variable (Xθ:∀ i:ℕ, FrameBox.Grove (0:Site (A.B.a.S.side i n)))
  (Xf:∀ (j:I) (i:ℕ), ((Labels.frames G).level (Y.demand j)).Coeff → Coefficient ((Labels.frames G).level (Y.demand j)) ((Issue.trail P).S.side i n))
  (hh:∀ j, GalaC U hr hl hL (Y.demand j) (V (Y.demand j)) (Xf j) Xθ m)
local notation "Xv"=> capStone X.p I' TT
local notation "b1"=> chanT
include hr h he hp hV hG hκ hh hU v₀ hR
set_option maxHeartbeats 500000 in
lemma serialize (hi:m ≤ i)(hN:N-m≤TT+1) (ht: Armed V B Y hm π' q' z ζ κ) : ∃ (J:Type) (_: Fintype J)(Pζ:J→ Menu.Hat B (U.port N i n hm).inPort) (φ:J→ Config G (A.B.a.S.side (i+1) n)→ℝ) (v:I→ℂ) (φx:I→ YM.MergeProof.Response G (A.B.a.S.side i n))(Yx:J→Prop), Serum U V B Y hm π Pζ φ v φx Yx κ ζ K z
    :=by
    let ξ:=(T).door; let Pα:= s₀; let Iθ:=q'.truth; let e:= y^ζ
    have hS:=step_paid A.B.a i; have hP:N-(i+1) ≤TT:=by omega
    have ha:= hp.terms J' I' hS x (A.B.valid.pays i)|>.2 u hP
    have hA:=hκ N i n hm; have hx:y=betaF G x L:= beta_eq A.B.valid i
    have hv' (p:I) : r0 (Y.demand p) ≤ i:= (h.phase.registered _).trans hi
    have hxQ(p:I): Y.demand p+3 ≤ A.B.a.clock.J i:= (hV _).trans (A.B.a.fits.mono (hv' p))
    have hd(p:I): Y.demand p ≤ I':= (Nat.le_add_right ..).trans (hxQ p)
    have h₀(p):= hR (Y.demand p) ((hv' p).trans hm.le)
    let c:= capStone X.p I' TT
    let f1(p:I):=chanT G (Y.demand p) X' l L P₀ Xv y Pt; let g1(p:I):=chanF G (Y.demand p) X' l L P₀ Xv Pt; let k1(p:I):=chanK G (Y.demand p) X' Xv Pt
    have hM(p:I):∃ v:ℂ,∃ Λ:Set Lotus.Wing, Λ.Finite ∧ XPre.Circuit Λ D' (Y.demand p) κ (AX.demand J' I' u) L' (o p) ((A.B.a.clock.op i n).ratio.parent (o p)) 1 (F p) (sK p) (sX p) v (f1 p) (g1 p) (k1 p):=by
        obtain ⟨a,γ,hγ,hc⟩:= U.tender (V (Y.demand p)) (Y.voice p) (h₀ p).contract hr hκ hG (h.phase.marks p) (Y.motion p) (fun i=>Y.origin i p) hm (h.phase.taps i p hi hm) (hv' p) (by omega) (hxQ p) ((h₀ p).motion _ (le_trans (hv' p) i.le_succ) hm) ((h₀ p).pattern i (hv' p) hm) (Xf p (i+1)) ((hh p).deeds _ (by omega) hm) -- args
        rw [←hx,Sail.sunny_color H N n _ _ _ _ (π' p),Sail.sunny_color H N n _ _ _ _ (π p)] at hc; exact ⟨a,γ,hγ,hc⟩
    let X₁:= Y.origin i; choose v hM using hM
    have hI₀: Iθ.origins=o:= ht.portrait.pins; have hy(x':I):∃ Λ:Set Lotus.Wing,Λ.Finite ∧ XPre.Circuit Λ D' (Y.demand x') κ (AX.demand J' I' u) L' (q'.truth.origins x') ((A.B.a.clock.op i n).ratio.parent (q'.truth.origins x')) 1 (F x') (sK x') (sX x') (v x') (f1 x') (g1 x') (k1 x'):=by rw [ht.portrait.pins]; exact hM x'
    have hY: 1≤ y:= (A.B.a.fits.delayed _).le; have hz: 0 <y:= zero_lt_one.trans_le hY; have hξ : 0 ≤waterline y:= Real.rpow_nonneg hz.le _
    let w:= rV; let Kx:= Y.origin (i+1); let Pν := X₀
    let T0 :ℝ:= wound y; have ha' := ha.1.ceiling; dsimp only at ha'
    have hπ(p):= (ha.2 (Y.demand p) (hd p)); have hc': q'.truth.origins= Kx:=ht.portrait.pins
    have hU' : AX.demand J' I' (u) ≤ z J' I' u:= hU.room.spans _ _ (u) hP hS; have hrhoV(p:I):Y.demand p ≤ AX.demand J' I' u:= (hd p).trans (AX.order.wide _ _ _ hS)
    have hb0(p): w p *g1 p≤ µ:=by unfold w g1; rw [hx]; exact (hπ p).q
    have hwU(p):0<w p:= Real.rpow_pos_of_pos hz _
    have huU : (∑ p:I,w p*f1 p)+(y^ζ)*(∑ p:I,2*w p*(k1 p+Pt))+ Port.capacity Pα.p I (allocationF y) (Pz) κ₁ Pz (y^ζ) L' ≤ T0:=by
        let w0:= waterline y; have h'(p:I):w p * f1 p≤w0:= by unfold w f1 w0; rw [hx]; exact (hπ p).h
        have h₁(p:I): y^ζ*(2*w p*(k1 p+Pt)) ≤ w0:=by unfold w w0 k1; rw [hx]; exact (hπ p).z
        have hlx: (∑ _:I,w0)≤ (K:ℝ)*waterline y:=by rw [Finset.sum_const, Finset.card_univ,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr h.phase.lines) hξ
        have hp:Pα.p=(A.B.a.budget (i+1)):= (P.choice.represents _ _ _ hm).vac; rw [← hx] at ha'; rw [Finset.mul_sum]; refine le_trans (add_le_add (add_le_add ((Finset.sum_le_sum fun i _=> h' i).trans hlx) ((Finset.sum_le_sum fun i _=> h₁ i).trans hlx)) (?_)) ha'
        have hq:= ha.1.repaint I h.phase.lines Pα.p (hp ▸ Rain.jersey (A:=A) (m:=i+1)|>.1) (hp ▸ Rain.jersey (A:=A) (m:=i+1)|>.2.1)
        rw [← hx] at hq; exact hq -- Urns.div κN
    have hm':0≤ z J' I' u := Nat.zero_le _
    obtain ⟨J,hhU,C,Φ,g',Y',hV',hY,hE,hJ,hX,hK⟩:= Sail.supply B q'.truth q'.model q'.remainder q'.H q'.K (hc'.symm ▸ ht.portrait.plate) ht.portrait.headings ht.portrait.flow w ht.portrait.shelf ht.portrait.printed ht.floor.cope ht.floor.rented ht.portrait.trial ht.cap (U.samples N (i+1) n hm) (F) (sK) (sX) v Q D' hrhoV (fun p=>hU') h.phase.lines (Real.one_le_rpow hY he.le) hb0 (show e₀ ≤ level from by unfold salesD; nlinarith) (show K ≤ level from by unfold salesD; nlinarith) (show K*e₀≤ level from by unfold salesD; nlinarith) (P.choice.represents N n (i+1) hm).good (U.purses hG (n:=n) hm (hxQ v₀)|>.honest) (U.preQtunes hm) hy (fun p=> Real.rpow_pos_of_pos hz _) huU
    rw [ht.portrait.pins] at hV' hE; have hT := ha.1.stamp; rw [← hx] at hT
    have ht' : Capsule I B s₀ s D' Q X₀ o w µ υ κ (y^ζ) K (salesD z K u J' I') L' v F' K' C Φ Y' g':=by
        have hZ(U'): X₀ U'= Marker.Poly.pass (Mach B v) * Expense C w Q U':=by rw [ht.portrait.density]; exact hX _
        have hf:MeasureTheory.Integrable X₀ (prior G P'):=by
           rw [show X₀= _ from funext hZ]; let m':= Marker.Poly.pass (Mach B v)
           let Fv: Marker.Poly B →ₗ[ℂ] Marker.Poly B := {toFun:=(m'*·), map_add':= fun uℓ vV=>mul_add m' uℓ vV, map_smul':=fun tℓ x₁=> mul_smul_comm ..}
           exact (Fv.restrictScalars ℝ).toContinuousLinearMap.integrable_comp (heat C Q w (P.choice.represents N n (i+1) hm).good)
        refine ⟨hV',hY,fun x'=> (Finset.card_le_univ _).trans h.phase.lines,hE,hZ,hJ,hK.trans hT,hf,?_⟩
        intro v' U'; apply (congr_fun (Accent.push_get («B»:=B) («x»:=(s₀).beta) (Ss:=Q) ((Issue.trail P).levels.transition_mass i n _) hf (B.fire v')) U').trans; erw [show (fun U'=>(X₀ U').part (B.fire v'))=Accent.coin s₀ _ _ from funext (ht.portrait.coins _)] ; exact congr_fun (Y.transfers V π h π' P.choice hi hm v').symm U' -- h shadows hi
    obtain ⟨hA1,hκ⟩:= hA
    refine ⟨J,hhU,Harmonics.relent H N i n (U.charged _ _ _ hm) C,Φ,v,g',Y',?_⟩
    exact shroudP H N i n (U.charged N i n hm) (U.baptism N i n hm) («D»:=(U.port N i n hm).door) ht' -- κ equals if needed
end YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics
