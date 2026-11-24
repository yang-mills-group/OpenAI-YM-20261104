import YM.FVAAlt2.Periodic.Primary
import YM.FVAAlt2.Rocket.Splice
import YM.Integration.RunFormalChain
/-!
# Bound Hessian and projection data of the *actual* Run and smoothing history

Works also for general circuits. Does not require strengthening to served.Clock.`
-/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Period.Field
open Function Set Filter MeasureTheory Topology Real Finset Lattice Tree RG Precision Gauge Pressure
open Oracle Epoch Calibration Rocket Uniform Binding Diagram Ledger Taping Atlas
open PhysicalNext.Repeat.Legato Family Run
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius Matrix
open Comparison.RG02 Comparison.RG02.Bulk Integration RunFormalChain
open YM.FVAAlt2.Period YM.FVAAlt2.Period.Rent
variable {X:Type} {n: X→ℕ} {m: Page n→Side} {Q:KernelChoices} {G:Gauge} (Y:Oracle.Program Q) (S:Circuit n m) (Γ:History G)(C: Comparison.RG02.Bulk.Chain Γ)
structure SeriesT (S:Circuit n m)(Q: KernelChoices) (Γ:History G) where
   vol:Page n→ℕ
   links (i:Flap n):vol i.prev=vol i.next+1
   pact i (p:ℕ): (Γ.levels.clock.op (vol (Flap.next i)) p).patch=S.pactP i
   creed i (p:ℕ): (Γ.levels.clock.op (vol (Flap.next i)) p).kernel=Q
-- formal Kernel abbreviation common. no claim Notebook reset=Calib from actual.
namespace SeriesT
variable (B:SeriesT S Q Γ)
def start (i:X):= B.vol (Page.opening n i)
local notation:max "V_" i:max=> B.vol i
lemma high(z: Page n): V_ z≤ B.start S Γ z.bindW:=by
   apply Page.proves (g:=fun z=>_) _ _ z
   · exact fun _=>le_rfl
   intro w hp; have ht:= B.links w; rw [ht] at hp; exact le_trans (Nat.le_succ _) hp
lemma fresh (i:Flap n): V_ i.next < B.start S Γ i.volW:= by have hw:= B.high S Γ i.prev; rw [B.links] at hw; exact hw
lemma length (z:Page n): V_ z+ z.downW= B.start S Γ z.bindW:=by
 apply Page.proves (g:=fun z=>_) _ _ z
 · exact fun _=> rfl
 intro w hw; rw [B.links] at hw; rw [← Nat.add_right_comm] at hw -- issue
 exact hw -- adjust
-- no implicit B.Epoch
section Ports
open Bloch Matrix Exterior
variable (p:ℕ)
abbrev stepData (i:Flap n) := Γ.levels.clock.op (B.vol i.next) p
abbrev records (w:Page n):= Γ.rep (B.start S Γ w.bindW) p (B.vol w)
abbrev readyKin (i:Flap n):= C.step (B.start S Γ i.volW) (B.vol i.next) p (B.fresh S Γ i)
local notation:max "Z_" i:max=> ( S.tables Y i )
-- Inputs transport statement
lemma receipt {c f: Side} (W: StepData c f)(T:Cross W.patch.L (TypeFace 1) (TypeFace 1))(D D':Bed) (hp: Precision.Inputs (avenue W.patch W.kernel c) (installed (tileB W.patch.L c) T) (D.metric.acts (c*W.patch.L)) (D'.metric.acts c)) : Precision.Inputs W (installed W.ratio T) (D.metric.acts f) (D'.metric.acts c) := by
    rcases W with ⟨W,Q,hc⟩; have he:f=c*W.L:=Subtype.ext hc; subst f; exact hp
include Y
lemma service (i:Flap n): ∃ T:Matrix (Body 1 (Γ.S.side (B.vol i.next +1) p)) (Body 1 (Γ.S.side (B.vol i.next) p)) ℝ, Precision.Inputs (SeriesT.stepData S Γ B p i) T ((Z_ i.prev).metric.acts (Γ.S.side (B.vol i.next+1) p)) ((Z_ i.next).metric.acts (Γ.S.side (B.vol i.next) p)):=by
    let P:=(S.pactP i); let W:=SeriesT.stepData S Γ B p i; have he:= S.predicted Y i
    have hm: ∃ T:Cross W.patch.L (TypeFace 1) (TypeFace 1), BidP W.patch W.kernel (Z_ i.prev) (Z_ i.next) T (Y.receipt.α (S.J i.prev)) (lesser (Y.receipt.Ω (S.J i.prev)) (S.sizeL i)):=by rw [show W.patch=_ from B.pact i p,show W.kernel=Q from B.creed i p]; exact ⟨_,he⟩
    obtain ⟨T,hT⟩:= hm; exact ⟨_,receipt W T _ _ (hT.motion _)⟩
include C
lemma brilliance (i: Page n) : let R:= B.records S Γ p i; Right R.clip R.path (Γ.S.side (B.vol i) p) (S.tables Y i):=by
    intro R
    apply Page.proves (g:=fun i=> let R:= B.records S Γ p i; Right R.clip R.path (Γ.S.side (B.vol i) p) (S.tables Y i)) ?_ ?_ i
    · intro w T; let x:=Page.opening n w; let i:=B.vol x;let A:=S.tables Y x; have hm:= S.honored Y x; exact control_top A _ (C.peak i p 2 (by decide)) (hm.top_s rfl _) (hm.card.floorP _)
    intro z he; unfold records at *; rw [ B.links z] at he; set U:= z.next; let E:= V_ U
    let P:= Γ.rep (B.start S Γ z.volW) p (E+1)
    have h: Right P.clip P.path (Γ.S.side (E+1) p) (Z_ z.prev):=he
    let F:= Halo.bios ( B.stepData S Γ p z )
    let K:= C.step (B.start S Γ z.volW) E p (B.fresh S Γ z)
    obtain ⟨T,hT⟩:= B.service Y S Γ p z
    exact Rent.cruise K (Z_ z.prev) (Z_ z.next) h T hT F (C.keeps (B.start S Γ z.volW) E p (B.fresh S Γ z) F)
-- packaged also in step units for port usage
lemma upstream (i:Flap n): let R:= Γ.rep (B.start S Γ i.volW) p (B.vol i.next+1); Right R.clip R.path (Γ.S.side (B.vol i.next+1) p) (S.tables Y i.prev):=by
    have hr:= B.brilliance Y S Γ C p i.prev; unfold records at hr; rw [B.links] at hr; exact hr
end Ports
end SeriesT
namespace LodgeT
def instance_real (Z:∀ P:Patch,P.Branches Q G)(C:Run G)(T:Lodge.Contract C Y Z)
    (t:X→ℕ)(ht:∀ x,T.floor Y Z C ≤ t x): SeriesT (T.profile Y Z C t ht).desk Q C.family.path where
   vol:= T.atLevel Y Z C t ht
   links i:= T.vert_j Y Z C t ht i
   pact i p:= ( T.paid_level Y Z C t ht i p |>.1 ).symm
   creed i p:= ( T.paid_level Y Z C t ht i p |>.2 ).symm
end LodgeT
end YM.RegulatorIR.FVAAlt2.Period.Field
