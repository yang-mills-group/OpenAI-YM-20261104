import YM.LocalLTE.Sail.Tasks
/-! Work in complete analytic call with arbitrary serialized calendars. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics
open Function Filter Set Lattice RG RG.Shoot Pressure Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Bandage
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Mallow ConnectedActivityE6 Push.AbsoluteSums LocalLTE LocalLTE.Vinca VoucherB LocalLTE.Fan
open Next.Scheduling.Clock Next.Scheduling.Instrument Progress.DirectedRecipe Pressure
open Legato.Spool LocalLTE.Sail MergeProof Menu Accent Spiral
variable {G:Gauge}{X:Metals G}{D:Rolls X.p}{A:Alloy X D}{P:Bolt A}{R:Factor A}
variable {C:ℕ→ℝ}{W:Bid.Worth}{l:ℕ}(U:Harmonics R C W P l)
local notation "H"=> Issue.trail P
variable {N n m i :ℕ}(V:∀ d,Extra.Histories.Music ((Labels.frames G).level d) (Issue.trail P) N n)
    (r0:ℕ→ℕ)(hV:∀ d,d+3 ≤ (Issue.trail P).levels.clock.J (r0 d))
open Spiral Pressure ConnectedActivityE6
variable {M p0 r q TT K P0 p' :ℕ}{κ ζ ε:ℝ}{AX: Almanac}(hr: Spiral.Chronicles R.shape M κ q l r p0 TT ε A.delay AX)(hp: Market M K P0 p0 TT l G ζ A.delay) (hD: Patronage K P0 p' p0 TT ζ A.delay)
variable (hκ:∀ N m n:ℕ,∀ hm:m<N, (U.port N m n hm).ac=M ∧ (U.port N m n hm).ranch.allocation.κ=κ)
variable (hG:G.Simple)(hL:∀ i j,(R.target i j).halo=500)(hl:East.stagnate q 500<l) (he:0<ζ)
variable {I:Type} [DecidableEq I][Fintype I]
    (B:Marker.Census I)(Y:Batch (Issue.trail P) N n I)(v₀:I)
    (h:Y.Roles V m W r0 K)
variable (hR:∀ d, r0 d ≤ N → Registers U V d (r0 d))
variable {z: GuideF}{Tt:ℕ→Mallow.ConcertZ R.target M ζ}(hU: Mobility AX R.shape A.delay z Tt K l TT κ)
-- Rendering
variable (π:∀ i:ℕ,i≤N→Y.steering i)
variable (Xθ:∀ i:ℕ, FrameBox.Grove (0:Site (A.B.a.S.side i n)))
  (Xf:∀ (j:I) (i:ℕ), ((Labels.frames G).level (Y.demand j)).Coeff → Coefficient ((Labels.frames G).level (Y.demand j)) ((Issue.trail P).S.side i n))
  (hh:∀ j, GalaC U hr hl hL (Y.demand j) (V (Y.demand j)) (Xf j) Xθ m)
variable (T: ∀ d N p:ℕ,TransferData ((Labels.frames G).level d) (Issue.trail P) N p)
variable (hC: (Family.mk (Issue.trail P) (hol G) (Labels.frames G) (localSection G) r0 T).Makes)
-- compute printer bounds
variable (O:∀ i:ℕ,Appendix B ((Issue.trail P).rep N n i))(hm:i<N)(hx:N-(i+1)≤ TT)
set_option quotPrecheck false
local notation "S"=> (Issue.trail P).rep N n i
local notation "Q'"=> (Issue.trail P).rep N n (i+1)
local notation "Pζ"=> (P.history N n i)
local notation "Y'"=> A.B.a.clock.hatBeta (i+1)
local notation "T₀"=> (U.port N i n hm)
local notation "u"=> N-(i+1)
local notation "g"=> (Coat.gStep ((Issue.trail P).rep N n (i+1)).beta)
local notation "b"=> (g^((P0:ℝ)+1))
local notation "b'"=> (g^((p':ℝ)+1))
local notation "θ"=> Real.sqrt (A.B.a.clock.forcedAllowance i)
local notation "Z'"=> (Y'^(chronicleShift u*K))
include hh hp hU hκ hx h hD hC hV
local notation "hE"=> AuditPanel U V hκ B Y v₀ hU π hm hx P0 (O i) (O (i+1))
local notation "ΣE"=>pointF Y π Xf hm
local notation "Ω"=> ((A.B.a.clock.op i n).push (Q').beta (Q').eval)
local notation "K'"=> (fun j=>(Y.named V (π i hm.le) j).forced)
local notation "t₀"=> (A.B.a.clock.hatBeta i)
local notation "w₁"=> intakeWeight u Y'
lemma publish (hi:m≤ i)(hN:N-m≤ TT+1) (ht:hE): (∀ j:I, FrameReport S (Y.origin i j) (Y.named V (π i hm.le) j) (pointF Y π Xf hm j) (hol G) θ b) ∧ (∀ v: Config G (A.B.a.S.side i n), FinePrint V B Y π Xf hm (O i) p' K v) :=by
    let R:= S
    have hi' (j:I):r0 (Y.demand j) ≤ i:= (h.phase.registered _).trans hi
    have hd(j):Y.demand j≤ A.B.a.clock.J i:= (Nat.le_add_right (Y.demand j) 3).trans ((hV _).trans (A.B.a.fits.mono (hi' j)))
    let k:= θ
    have hf(j:I): FrameReport R (Y.origin i j) (Y.named V (π i hm.le) j) (pointF Y π Xf hm j) (hol G) k b:= U.calibratedPrice (V (Y.demand j)) (Y.voice j) (h.text j) hp (h.phase.marks j) (Y.motion j) (fun i=>Y.origin i j) hm (π i hm.le j) (Xf j i) (hi' j) (hd j) (by omega) ((hh j).deeds i hi hm.le)
    refine ⟨hf,fun v=>?_⟩
    obtain ⟨J,hJ,p,f,v',ζ',A',β,hP,hQ⟩:= ht.permits
    -- surveys independently. Use hP books for θ and currencies
    let X':= O i; let w:I→ℝ:=fun _=>w₁
    have hX:= hP.exactQ; have hXb:= hP.trueB; have hXa:= hP.auditX; rw [← hQ] at hX hXb hXa
    have hy:= hD.frames _ _ (step_paid A.B.a i) _ (A.B.valid.pays i) _ (hd v₀) u hx
    have he:= (T₀).senses.2; unfold RG.Shoot.band at he; simp only [Set.mem_Icc] at he; rw [← U.charged _ _ _ hm] at he
    have ht : Y'= betaF G t₀ (D.L (A.B.a.clock.J (i+1))):= beta_eq A.B.valid i
    have hr:= h.phase.lines; have hDq:= hy.stamp; rw [← ht] at hDq; obtain ⟨he0,hQt,hζ,hM⟩:=hDq (Q').beta he.1 he.2
    have ht':1 ≤ Y':= A.B.a.fits.delayed _|>.le; have hx':0< Y':=zero_lt_one.trans_le ht'; let Kt:=chronicleShift u; let ticket := b; have ht:0≤ b:= Real.rpow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _
    have hx:0 ≤ chronicleShift u:=by unfold chronicleShift; linarith only [Nat.cast_nonneg (α:=ℝ) (N-(i+1))]
    let Xr:= Accent.gust H N n N (Y.raw B) i hm.le; let F j:=spectralValue Y π Xf hm j; let F0:= Y.requested V i
    have hu(j:I):= U.signalCosts V r0 hV hD Y h π Xf hm T hC hi hN j v (hf j) -- edit shadow hD
    obtain ⟨hx1,hm1,hPt,hW⟩:= Sail.comparisonPrice B X' F0 F w (Y.origin i) K' Xr hX v ht he0 (Real.rpow_le_one_of_one_le_of_nonpos ht' (by norm_num [Mallow.aust])) hXb hXa (fun i=> Real.rpow_le_one_of_one_le_of_nonpos ht' (neg_nonpos.mpr hx)) hr (fun j=> (hu j).1) (fun j=>(hu j).2)
    let P':= Sail.receipt B X' F0 v; let Hu:= Sail.forecast B X' F v
    have hv: (S).eval=Ω:= (P.choice.steps N n i hm).1 -- macro
    refine ⟨show 0<(Ω v) from by rw [← hv]; exact Tour.bright (H) P.choice N n i hm.le v,⟨hx1,hm1⟩,?_,?_⟩
    · intro l l'; change Marker.Poly.price _ (P'-Hu)≤ (2*K)*b'
      refine (repriced B (P'-Hu) K hr (chronicleShift u) Y' ht' hx).trans ((mul_le_mul_of_nonneg_left hPt (Real.rpow_nonneg hx'.le _)).trans (?_)) -- edit
      let a:= Z'; suffices h : (2*(K:ℝ))*(Z'*b) ≤ (2*(K:ℝ))*b' by refine Eq.trans_le ?_ h; ring
      exact mul_le_mul_of_nonneg_left hM (by positivity)
    intro pX l t uX hBg -- u notation parser?
    have ht:= Sail.allclear B X' F0 (Y.origin i) K' Xr hX v hBg; rw [hv] at ht -- rewrite eval only
    let A':=Sail.margin K; have hu:0≤ A':=by unfold A' Sail.margin; positivity
    refine ⟨ht.2,?_⟩
    change Marker.Poly.price (fun _=>(1:ℝ)) (pX⁻¹ • Xr v-Marker.Poly.pass Hu) ≤ _
    rw [show pX⁻¹ • Xr v= Marker.Poly.pass P' from ht.2]
    refine (repriced B (P'.pass-Hu.pass) K hr (chronicleShift u) Y' ht' hx).trans ((mul_le_mul_of_nonneg_left hW (Real.rpow_nonneg hx'.le _)).trans (?_))
    refine le_trans (le_of_eq (show Z'*(A'*(2*b))= (A'*2)*(Z'*b) from by ring)) (mul_le_mul_of_nonneg_left hM (mul_nonneg hu zero_le_two)) -- local name p' collision
end YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics
