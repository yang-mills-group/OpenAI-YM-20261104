import YM.LocalLTE.Sail.Ratio
/-!
# The numerical survey of conditional strokes
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics
open Function Filter Set Lattice RG RG.Shoot Pressure Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Bandage MergeProof
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Mallow ConnectedActivityE6 Push.AbsoluteSums LocalLTE LocalLTE.Vinca VoucherB LocalLTE.Fan
open Next.Scheduling.Clock Next.Scheduling.Instrument Progress.DirectedRecipe Pressure
open Legato.Spool LocalLTE.Sail MergeProof Menu Accent Spiral
section poly
variable {V:Type}[DecidableEq V][Fintype V](B:Marker.Census V)
open Marker
-- recost.V.Correct.
lemma repriced (x:Poly B) (p:ℕ)(ht:Fintype.card V≤ p)(a y:ℝ)(h:1 ≤ y)(hp:0≤a): Poly.price (fun _=>1) x ≤ y^(a*p)*Poly.price (fun _=> y^(-a)) x:=by
    let v:= y^a; let w:V→ℝ:=fun _=>y^(-a); have hz:0<y:=zero_lt_one.trans_le h; have hx:1≤v:=Real.one_le_rpow h hp; have hw i:0<w i:=Real.rpow_pos_of_pos hz _; have he:y^(a*p)=v^p:=Real.rpow_mul_natCast hz.le a p
    have hi(i): (1:ℝ) ≤ v*w i:= by unfold v w; rw [← Real.rpow_add hz, add_neg_cancel, Real.rpow_zero]
    have hV(i:B.Mode): Marker.Poly.toll (fun _=>1) i ≤ v^p* Marker.Poly.toll w i:=by
       apply le_trans (Finset.prod_le_prod (fun _ (_:_∈i.val)=>zero_le_one) (fun j _=> hi j));rw [Finset.prod_mul_distrib, Finset.prod_const]; exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hx ((Finset.card_le_univ _).trans ht)) (Marker.Poly.worth hw _).le
    rw [he,Poly.price,Poly.price, Finset.mul_sum]; refine Finset.sum_le_sum fun i _=>?_ ; rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (hV i) (norm_nonneg _)
end poly
variable {G:Gauge}{X:Metals G}{D:Rolls X.p}{A:Alloy X D}{P:Bolt A}{R:Factor A}
variable {C:ℕ→ℝ}{W:Bid.Worth}{l:ℕ}(U:Harmonics R C W P l)
local notation "H"=> Issue.trail P
variable {N n m i:ℕ}(V:∀ d,Extra.Histories.Music ((Labels.frames G).level d) (Issue.trail P) N n)
    (r0:ℕ→ℕ)(hV:∀ d,d+3 ≤ (Issue.trail P).levels.clock.J (r0 d))
open Spiral Pressure ConnectedActivityE6 Planned.GuardedAtom
variable {M p0 r q TT K P0 p' :ℕ}{κ ζ ε:ℝ}{AX: Almanac}(hr: Spiral.Chronicles R.shape M κ q l r p0 TT ε A.delay AX)(hp: Market M K P0 p0 TT l G ζ A.delay) (hD: Patronage K P0 p' p0 TT ζ A.delay)
variable (hκ:∀ N m n:ℕ,∀ hm:m<N, (U.port N m n hm).ac=M ∧ (U.port N m n hm).ranch.allocation.κ=κ)
variable (hG:G.Simple)(hL:∀ i j,(R.target i j).halo=500)(hl:East.stagnate q 500<l) (he:0<ζ)
variable {I:Type} [DecidableEq I][Fintype I]
    (B:Marker.Census I)(Y:Batch (Issue.trail P) N n I)(v₀:I)
    (h:Y.Roles V m W r0 K)
variable (hR:∀ d, r0 d ≤ N → Registers U V d (r0 d))
variable {z: GuideF}{Tt:ℕ→Mallow.ConcertZ R.target M ζ}(hU: Mobility AX R.shape A.delay z Tt K l TT κ)
-- work at current Mark.Log & price
variable (π:∀ i:ℕ,i≤N→Y.steering i)
variable (Xθ:∀ i:ℕ, FrameBox.Grove (0:Site (A.B.a.S.side i n)))
  (Xf:∀ (j:I) (i:ℕ), ((Labels.frames G).level (Y.demand j)).Coeff → Coefficient ((Labels.frames G).level (Y.demand j)) ((Issue.trail P).S.side i n))
  (hh:∀ j, GalaC U hr hl hL (Y.demand j) (V (Y.demand j)) (Xf j) Xθ m)
-- sanity.A to lift label transport directly in paid pricing. There's no cancellation with derivative aliases.S.ALL.
variable (hm:i<N)
set_option quotPrecheck false
local notation "x"=> A.B.a.clock.hatBeta i
local notation "y"=> A.B.a.clock.hatBeta (i+1)
local notation "u"=> N-(i+1)
local notation "pκ"=> Real.sqrt (A.B.a.clock.forcedAllowance i)
local notation "I'"=> A.B.a.clock.J i
local notation "J'"=> A.B.a.clock.J (i+1)
local notation "T'"=> (U.port N i n hm)
local notation "S"=> (Issue.trail P).rep N n i
local notation "Q'"=> (Issue.trail P).rep N n (i+1)
local notation "Ω"=> ((A.B.a.clock.op i n).push (Q').beta)
set_option quotPrecheck false -- P.P syntax.Move earlier
local notation "Φr"=> (Coat.gStep ((Issue.trail P).rep N n (i+1)).beta)
local notation "P1"=> (Φr^((P0:ℝ)+1))
local notation "Y'"=> (Y.requested V i)
local notation "g1"=> (X.p.profile I')
local notation "Γ'"=> (Φr^((p':ℝ)+1))
local notation "w₁"=> Spiral.intakeWeight u y
local notation "r₁"=> fun _:I=> Spiral.intakeWeight u y
local notation "a"=> y^(chronicleShift u*K)
local notation "op"=> (Y.origin i)
local notation "k"=> (π i hm.le)
local notation "K'"=> (fun j=> (Y.named V k j).forced)
-- keep these audited names.Pe coupled.Mark stencil coherent.One horizon.Validator uses THIS Family identity.
variable (T: ∀ d N p:ℕ,TransferData ((Labels.frames G).level d) (Issue.trail P) N p)
-- actual.Makes param avoid family notation var.
variable (hC: (Family.mk (Issue.trail P) (hol G) (Labels.frames G) (localSection G) r0 T).Makes)
include hm
noncomputable abbrev pointF (v:I):= stampField H N n (Y.motion v) (fun i=>Y.origin i v) (π i hm.le v) (Xf v i (Y.voice v))
local notation "F"=> pointF Y π Xf hm
noncomputable def spectralValue (v:I): Config G (A.B.a.S.side i n)→ℂ:= (F v|>.exponentialEntry (op v) (localSection G (Y.demand v)) (S)) -- F. Lean order inspect
local notation "E"=> spectralValue Y π Xf hm
local notation "X₀"=> gust H N n N (Y.raw B) i hm.le
variable (O: Appendix B ((Issue.trail P).rep N n i))
structure FinePrint (p':ℕ)(K:ℕ) (v:Config G (A.B.a.S.side i n)):Prop where
    volume: let q:= Ω (Q').eval v; 0< q
    vote: let l:= (Sail.receipt B O Y' v); let l':= (Sail.forecast B O E v); l.part B.quiet=0 ∧ l'.part B.quiet=0
    log: let l:= (Sail.receipt B O Y' v); let l':=(Sail.forecast B O E v); Marker.Poly.price (fun _=>1) (l-l') ≤ (2*K)* (Φr ^ ((p':ℝ)+1))
    sightings: let q:= Ω (Q').eval v; let l:= Sail.receipt B O Y' v; let l':= Sail.forecast B O E v; let a':= q⁻¹ • (X₀ v); flags (S).p.threshold v=∅→ a'=Marker.Poly.pass l ∧ Marker.Poly.price (fun _=>1) (a' - Marker.Poly.pass l') ≤ (margin K*2)*(Φr^((p':ℝ)+1))
-- clarify `log`: outside clip L only interpreted as regular tape, not log of scalar-ratio.Sharp.
local notation "hK"=> (allocationK y ζ)
local notation "l'"=> (y^(-ζ))
include hp h hr hD hC hh U hU -- Used? hU for κ? just Frame
variable (hi:m≤ i)(hN:N-m≤TT+1)
include hi hN
omit hU
local notation "C0"=> ((X.p.profile I').columns)
local notation "s0"=> capStone X.p I' TT
local notation "p'β"=> β
include hV
omit hp hh hr [DecidableEq I] in
lemma signalCosts (d: I) (v:Config G (A.B.a.S.side i n)) (hh0: FrameReport S (op d) (Y.named V k d) (F d) (hol G) pκ P1): w₁ * ‖Y' d v‖ ≤1 ∧ w₁ * ‖Y' d v-E d v‖≤ P1:=by
    have h₀:r0 (Y.demand d) ≤ i:= (h.phase.registered d).trans hi
    let P':=S; let t:= C0; let f:= (Y.voice d); let Q:=(V (Y.demand d)); let zp:=(Q.tone i); let c:= Y.demand d; let Yt:=(Labels.frames G).level c; let z₀:= Sail.sampleNorm H N c i
    have he:= step_paid A.B.a i; have hε:y= betaF G x (D.L J'):= beta_eq A.B.valid i
    have hc:P'.p= A.B.a.budget i:= (P.choice.represents _ _ _ hm.le).vac
    have hx:(X.p.profile I')= (H).levels.params i:= (params_eq A.B.valid i).symm
    have hB(o:Site ((Issue.trail P).S.side i n)) (j : Yt.Index): P'.p.Regular ((localSection G c).footprint o) ((localSection G c).places (Pi.single j 1) o) ∧ P'.p.supBounds o ((localSection G c).footprint o) ((localSection G c).places (Pi.single j 1) o) (t*P'.p.threshold^(Yt.grades j).2):=by
       rw [hc, show t= ((Issue.trail P).levels.params i).columns from congr_arg Stage.columns hx]; exact hC.priced c i n h₀ o j
    have hz:= zero_lt_one.trans_le (A.B.a.fits.delayed (i+1)|>.le); have hc':1 ≤ t:=(X.p.profile I').columns_ge; have hπ := h.text d|>.earned i h₀ hm.le; have hd0:c ≤ I':= (Nat.le_add_right c 3).trans (show Y.demand d+3 ≤ A.B.a.clock.J i from ?_) -- hV missing add
    swap
    · exact (hV (Y.demand d)).trans (A.B.a.fits.mono h₀)
    have hP := hD.frames _ _ he _ (A.B.valid.pays i) _ hd0 u (by omega)
    let Xr:= zp.plays f; have hp(t :ℝ):0 < y^t:= Real.rpow_pos_of_pos hz t
    have hw:0 ≤ w₁:= Real.rpow_nonneg hz.le _
    have hp1:= h.text
    obtain ⟨hS,hq⟩:= (hπ.earns f); have hk:= Graces.glyphBound (A.B.a) i
    constructor
    · let q:= Yt.coeffSize (zp.index f)
      let u':=pull (Y.motion d).1 (Y.origin i d) v; have h₄ := Accent.hull (localSection G c) P' 0 Xr u' (hB (0:Site ((Issue.trail P).S.side i n))) hq hk.2 (zero_le_one.trans hc') -- H.M macro
      have he:= hπ.cone f; rw [← hx] at he; have hz':zp.charge f ≤ t*q:=he.trans (mul_le_mul_of_nonneg_left (Work.G08.size_core ..) (zero_le_one.trans hc')); rw [show Xr.x=zp.index f from hπ.currents f] at h₄
      have hy0: ‖z₀‖*q ≤ s0:= U.cornerstone Q f (h.text d) (h.phase.marks d) i h₀ hm.le TT (by omega) i (Nat.le_refl _) hm.le -- h shadow
      have he:‖Y' d v‖ ≤ (1+2*t)*(s0):=by
          change ‖z₀ * Motion.scalar _ _‖ ≤ _; rw [norm_mul,Motion.norm_scalar]
          calc
             _ ≤ ‖z₀‖*((1+t)*q + t*q):= mul_le_mul_of_nonneg_left (h₄.trans (add_le_add le_rfl hz')) (norm_nonneg _)
             _ = (1+2*t)*(‖z₀‖*q):=by ring
             _ ≤ _:= mul_le_mul_of_nonneg_left hy0 (by linarith only [hc'])
      apply le_trans (mul_le_mul_of_nonneg_left he hw) _; rw [hε]; exact hP.tracks
    · obtain ⟨z,q',hQ',-⟩:= rem_tabs.mp hq
      obtain ⟨he,hT,hv⟩:= audition_turn (Y.motion d) (Y.origin i d) (π i hm.le d) ((by decide:2≤4).trans (actual_side_ge (Issue.trail P|>.S) i n)) (sound G c) hS hQ'
      rw [show affine (Y.motion d).1 (Y.origin i d) 0= Y.origin i d from by simp [affine] ] at hT
      let p:= Sail.readPrice (localSection G c) hh0 (stretch_rem z₀ (hT.bound le_rfl)) (hB (Y.origin i d)) v hc' hk.2 -- order check
      unfold spectralValue; rw [show Y' d=(Y.named V k d).exponentialEntry (op d) (localSection G c) P' from Batch.labels_equal ..] -- QF type
      apply le_trans (mul_le_mul_of_nonneg_left p hw) _; rw [← mul_assoc]; have hv' : w₁*(3+t)≤ 1:=by rw [hε]; exact hP.author
      have he:0 ≤P1:= by -- GKstep positive
         exact Real.rpow_nonneg (show 0 ≤Coat.gStep (Q').beta from inv_nonneg.mpr (Real.sqrt_nonneg _)) _
      exact mul_le_of_le_one_left he hv'
end YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics
