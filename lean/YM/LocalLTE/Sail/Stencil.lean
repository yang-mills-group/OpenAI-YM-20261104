import YM.LocalLTE.Sail.Winding
import YM.LocalLTE.Sail.Agenda
/-!
# All arity-one forecasts aligned at the physical layout

Precise reported `t` is an appointment in the SAME basis at OUT. Purchased for full stamp
and primary. Price of further projection keep separately.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom
open Bandage Mallow Coterie
open YM.MergeProof YM.LocalLTE.Vinca YM.LocalLTE LocalLTE.Ticket LocalLTE.River LocalLTE.Sail
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{X:Metals G}{D:Rolls X.p}{A:Alloy X D}{P:Bolt A}{R:Factor A}
section
variable {p:Side}{d:ℕ} {Z:Rep G p}{a t l k ρ e:ℝ}{i j:ℕ}
    {F:Labels.Frame G d}(B : SectionData F) {A:Hol G} {P Q:Coefficient F p}
    {s:Site p}(M:Motion)(T:Z.activities.Moves M.1 s)(w:ℂ)
-- This theorem also used for accounting on ACTUAL side not estimator masks. Need decide if positivity divide asserted.
noncomputable abbrev newton (P:Coefficient F p):= Extra.Histories.stretch w (audition T P)
local notation "W"=> newton M T w
include M
open Motion Push.Local
private lemma auditionP (P:Coefficient F p) (i:ℕ): (audition («z»:=M) T P).support i=(P.support i).image (turnSites M.1 s) ∧ (audition («z»:=M) T P).x=Motion.patch F M P.x:=by
    rcases M with ⟨u,M⟩; cases M <;> exact ⟨rfl,rfl⟩
omit M in
private lemma rotatedBudget (D:Coefficient F p)(o:Site p)(h:Tab D o Z ρ t l): Tab (Extra.Histories.stretch w D) o Z ρ (‖w‖*t) (‖w‖*l):=by
    obtain ⟨a,ha,hp⟩:= h.regular; obtain ⟨b,hb,hq⟩:=h.forced
    refine ⟨h.divisor,mul_nonneg (norm_nonneg _) h.first,mul_nonneg (norm_nonneg _) h.second,⟨(fun i=> ‖w‖*a i),?_, fun i=> Next.Foundations.bound_smul w (hp i)⟩, (fun i=> ‖w‖*b i),?_,fun i=> ⟨mul_nonneg (norm_nonneg _) (hq i|>.1),fun U=> (norm_smul w (D.forced i U)).trans_le (mul_le_mul_of_nonneg_left ((hq i).2 U) (norm_nonneg _))⟩⟩
    · simp_rw [Extra.Histories.mass_scale]; exact Push.Local.sumBudget_mul_left ha (norm_nonneg _)
    simp_rw [Extra.Histories.mass_scale,mul_left_comm ρ ‖w‖ l]; exact Push.Local.sumBudget_mul_left hb (norm_nonneg _)
private lemma rotate_dec (P Q:Coefficient F p) : Vinca.decrement (W P) (W Q)= W (Vinca.decrement P Q):=by
    have ht': decrement (audition T P) (audition T Q)= audition T (decrement P Q):=by
        rcases M with ⟨m,ri⟩; cases ri
        · unfold audition; simp [Vinca.decrement,reorient]; exact ⟨rfl,rfl⟩
        unfold audition; simp [Vinca.decrement,reorient,barAll]; constructor <;> funext i v<;> simp
    unfold newton; rw [← ht']; simp [Extra.Histories.stretch,decrement,smul_sub]
-- People evaluation.S.Full.Path.Mask tests.Support spans.Native Γ.
structure FrameReport (Z: Rep G p) (s:Site p)(P Q:Coefficient F p)(A:Hol G)(ρ e:ℝ):Prop where
     alignment:P.support=Q.support
     receipt: Q.Format s A Z
     stocks: Q.forced=0
     trade: (Vinca.decrement P Q).Format s A Z
     earns: Tab (Vinca.decrement P Q) s Z ρ e e
     monte:F.coeffSize (Vinca.decrement P Q).x ≤ e
set_option quotPrecheck false
local notation "rp"=> rotationP F Z.p.order Z.p.power
include M
lemma auditor {Y:ℝ}(h: Exhibition B k i j A Z P Q ρ t a)(hb:B.Sound A)(hn:2 ≤p.val)(hp: ‖w‖*(rotationP F Z.p.order Z.p.power*a) ≤ Y): FrameReport Z s (W P) (W Q) A ρ Y:=by
    obtain ⟨hv,hQ,hG⟩:= audition_turn M s T hn hb h.trade h.fee
    obtain ⟨hc,h₀,h₁⟩:= audition_turn M s T hn hb h.format (h.stock.bill h.fee.divisor)
    have he:affine M.1 s 0=s:=(by simp [affine]); rw [he] at hv hQ hc; let i:=Vinca.decrement P Q; let l:= rotationP F Z.p.order Z.p.power; have hL:0≤l:=zero_le_one.trans (River.rotation_one ..)
    have hV:= stretch_format w hv; change (W (Vinca.decrement P Q)).Format _ _ _ at hV; rw [← rotate_dec M T] at hV -- maybe delta fail
    have hf:= h.stock.forced; have hz:(W Q).forced=0:=by
        unfold newton Extra.Histories.stretch audition; split; next=> funext i v; simp [barAll,reorient,hf]
        next=> funext i v; simp [reorient,hf]
    refine ⟨funext fun n=>(auditionP M T P n).1.trans ((h.layout ▸ (auditionP M T Q n).1.symm)),stretch_format _ hc,hz,hV, ?_,?_⟩
    · rw [rotate_dec]; refine tabWeaken (rotatedBudget w _ s hQ) ?_ ?_; exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (River.rotation_price ..|>.1) h.fee.first) (norm_nonneg w)).trans hp; exact (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left h.fee.first (River.rotation_one ..)) (norm_nonneg w)).trans hp
    rw [rotate_dec,newton,Extra.Histories.stretch, (auditionP M T i 0).2, Size.smul]; exact (mul_le_mul_of_nonneg_left (le_trans (Motion.patch_cost ..) (mul_le_mul (rotation_price .. |>.2) h.canon (Work.G08.size_nonneg ..) (zero_le_one.trans (rotation_one ..)))) (norm_nonneg w)).trans hp
end
section
variable {C:ℕ→ℝ}{W:Bid.Worth}{l:ℕ}(U:Harmonics R C W P l)
local notation "H"=> Issue.trail P
variable {N n d:ℕ} (V:Extra.Histories.Music ((Labels.frames G).level d) (Issue.trail P) N n) (f:((Labels.frames G).level d).Coeff)
    {r0:ℕ}(hv:Sung (localSection G d) (Issue.trail P) N n (hol G) W r0 V)
local notation "T₀"=> localSection G d
set_option quotPrecheck false
local notation "F"=> ((Labels.frames G).level d)
local notation "T"=> A.B.a
local notation "c" i=> (Issue.trail P).S.block i
local notation "σ" i=> Sail.sampleNorm H N d i
local notation "J'" i=> A.B.a.clock.J i
local notation "Z"=> A.B.a.clock
variable {m:ℕ}
local notation "I'"=> J' m
local notation "J"=> J' (m+1)
local notation "x"=> (Z).hatBeta m
local notation "y"=> (Z).hatBeta (m+1)
local notation "b"=> D.L J
open Spiral Pressure ConnectedActivityE6
variable {M p0 r q TT K P0 :ℕ}{κ ζ ε:ℝ}{AX: Almanac}(hr: Spiral.Chronicles R.shape M κ q l r p0 TT ε A.delay AX)(hp: Market M K P0 p0 TT l G ζ A.delay)
variable (he:((Labels.frames G).level d).coeffSize f ≤ 1)
variable (M':Motion) (o:∀ i,Site ((Issue.trail P).S.side i n))(hm:m<N)
variable (π:((Issue.trail P).rep N n m).activities.Moves M'.1 (o m))
local notation "A'"=> (Issue.trail P).rep N n m
variable (Q: ((Labels.frames G).level d).Coeff→ Coefficient ((Labels.frames G).level d) ((Issue.trail P).S.side m n))
include hp he hv U hm
lemma calibratedPrice (hd:r0 ≤ m)(hδ:d≤ A.B.a.clock.J m)(hz:N-m≤ TT+1)(hQ:ShellDate (AX:=AX) (l:=l) (p0:=p0) (TT:=TT) (κ:=κ) d V m Q): FrameReport A' (o m) (imprint H N n f M' o V π) (stampField H N n M' o π (Q f)) (hol G) (Real.sqrt (A.B.a.clock.forcedAllowance m)) ((Coat.gStep ((Issue.trail P).rep N n (m+1)|>.beta))^((P0:ℝ)+1)):=by
    let W':= U.port N m n hm; let k:= N-(m+1); let e:= (x)^(grantZ p0 TT (k+1)); have hh:N-m=k+1:=by unfold k;omega
    let S:= (A').p; have hψ:S=(T).budget m:= (P.choice.represents _ _ _ hm.le).vac
    have hL: rotationP F S.order S.power= rotationP F (X.p.profile (I')).order (X.p.profile (I')).power:=by rw [hψ,Rain.jersey (A:=A) (m:=m)|>.1,Rain.jersey (A:=A) (m:=m)|>.2.1]
    have hv':= hp.terms J I' (step_paid _ _) _ (A.B.valid.pays m)|>.2 k (by omega)|>.2 d hδ
    obtain ⟨hβ,hq⟩:= W'.senses.2
    have ht:(Issue.trail P).rep N n (m+1)=W'.inPort:= U.charged N m n hm
    rw [← ht,beta_eq A.B.valid] at hβ hq
    let s:= (F).coeffSize ((V.tone m).index f)
    have hw:0≤ rotationP F S.order S.power:= zero_le_one.trans (rotation_one ..); have hx:0 ≤ e:=Real.rpow_nonneg ((T).fits.delayed m|>.le|>zero_le_one.trans) _
    have hp0:‖(σ m)‖ * s≤ capStone X.p (I') TT:= cornerstone U V f hv he m hd hm.le TT hz _ le_rfl hm.le
    have hxZ:= hQ.l f; rw [hh] at hxZ
    apply auditor T₀ M' π (σ m) hxZ (sound G d) ((by decide: 2≤ 4).trans (Next.Foundations.actual_side_ge (Issue.trail P|>.S) m n)) _
    let r:= rotationP F S.order S.power;
    change ‖(σ m)‖* (r*(e*s)) ≤ _
    refine Eq.trans_le (show ‖(σ m)‖* (r*(e*s))=r*(‖(σ m)‖*s)*e from by ring) ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp0 hw) hx).trans ?_)
    rw [hL]; exact hv'.price _ hβ hq
end
end YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics
