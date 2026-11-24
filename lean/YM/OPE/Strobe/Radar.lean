import YM.OPE.Strobe.Twain
/-! # Temporal specifications near the stencil. No lower occupation blow.Just dist. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Strobe
open Yarn
open Function Filter Set MeasureTheory Finset Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Overlay
open MergeProof Accent Ribbons ManyCopies MergeProof.Float PhysicalNext.Repeat Lotus Legato Mallow Bandage Patrol Loom
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {I J:Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J]{G:Gauge}{n: Side} {C:Family G} {k z i j l m p N d:ℕ}
variable {W r D}{σ χ:ℕ→ℝ} (H:Tune C W r D σ χ)
set_option quotPrecheck false
local notation "P" => C.path
local notation "T" => C.path.levels
local notation "δ" => renal C.path.levels
local notation "η" => near C.path.levels
local notation "ζ" => fly C.path.levels
local notation "ψ" => waybill C.path.levels
local notation "R" => C.path.rep N p
local notation "V" => Site (C.side m p)
local notation "Z" => royal C m p
local notation "r*" => stepUp
open Yarn.SitePlan Next.Rank.Station
structure Passage (C:Family G) (d j k n m z b:ℕ)(r:ℕ→ℕ)(a t:ℕ): Prop where
    notch : C.ref 0< z
    scroll : z<j
    next : j<k
    tall : Barrow C r m b z
    mount : 8*(2*C.S.a k *(n:ℝ))≤ C.S.a m
    price : j= arch 100 C (C.S.a k*n/4)
    fine : C.S.a k*n/4 ≤ threshold C 100 0
    paid : (C.path.levels.budget k).B^8≤ n
    gain : 2*muzzle C.path.levels k (omen C d k a) < (C.path.levels.budget k).B^8
    stride : Loom.stride C t k-4 ≤ (C.path.levels.budget k).B^8
    porch : GridApprox.room C.path.levels m k (n+omen C d k a)
    rank : C.ref d≤k
    seats (N:ℕ) (hNu:k ≤ N) : ∀ p,∀ b':Site (C.side N p),8*‖C.S.place b'‖≤ C.S.a m →∀ v:C.label d, Interior ((center C.S p (tall.hbar.trans (scroll.le.trans (next.le.trans hNu))) 0).chamber 0) (C.O N p v b') -- `by assumption`? arrow not in context? binder anonymous
local notation "B" i => (C.path.levels.budget (i)).B
local notation "s" i => C.S.a (i)
variable {n t b a:ℕ}{x:I→Site (C.side k p)} (i₀:I) (he:Habits C k p n x i₀) (A:Passage C d j k n m z b r a t)
    (hf:Fintype.card I ≤ b)
local notation "y" => ((loops C k p) ∘ x)
local notation "U'" i => ((Z (i)).place (fun j=>(y j) (i)))
include A
lemma living : 0<n:= (pow_pos (C.path.levels.budget k|>.B_pos) (8:ℕ)).trans_le A.paid
lemma begins (hp:k ≤ i) (j:I) : (y j) (i+1)=(C.path.levels.clock.op i p).ratio.embed (y j i):= Function.const _ (Function.const _ (by rw [show (T|>.clock.op i p).ratio=C.S.toDepth i.le_succ p from ratio_same ..]; exact sails (x j) hp (Nat.le_succ i)) A) (‹Fintype I›, ‹DecidableEq I›)
lemma Habitat_root (hb:1≤b) : Band C (p:=p) (fun _:Unit=>fun i=>(0:Site (C.side i p))) r z j m:=by
    let x'(_:Unit): Site (C.side k p):=0; have hc(i):8*‖C.S.place (x' i)‖ ≤ C.S.a m:=by unfold x'; rw [latzero,norm_zero,mul_zero]; exact (C.S.a_pos m).le -- edit
    -- use inertia across copy.
    let o':= fun (_:Unit) i=> (0:Site (C.side i p)); have hx:Habits C k p n x' ():=⟨rfl,fun i=>by simp [x',separation_self],fun i j h=>False.elim (h (Subsingleton.elim ..))⟩; have h:o'= loops C k p ∘ x':= by funext u' i; exact loops_id (C:=C) i|>.symm
    change Band C o' _ _ _ _; refine ⟨fun i hi hp v=>?_,fun i hi _=>?_,?_⟩
    · rw [h]; rw [show (T|>.clock.op i p).ratio=C.S.toDepth i.le_succ p from ratio_same ..]; exact sails_parent (x' v) i.le_succ
    · rw [h]; exact Habitat () hx A.mount A.tall (by simpa using hb) hi
    intro i hi hp; rw [h]; exact corners () hx A.mount A.tall hi.le ((A.tall.apron i hi.le).1.trans (pow_le_pow_right₀ (C.path.levels.budget i|>.B_pos) (by decide:2≤8))) (fun i j ht=> False.elim (ht (Subsingleton.elim ..))) -- check x binder
omit A in
lemma there (x:Site (C.side k p)) : loops C k p x k=x:= same ..
def writeF (C:Family G)(v:C.label d)(N k p:ℕ)(a:ℕ) (x:Site (C.side k p))(hk:k ≤ N)(frozen:Bool):= C.O N p v (GridApprox.anchor C.S p hk x) + GridApprox.backTo C.path N p hk (betaDrop C d k N p a v x frozen)
include H he
variable (x₁:I→ C.label d)(ice:I→Bool)(t':ℝ) (hk:k<N)
local notation "N*" => center C.S p (A.tall.hbar.trans (A.scroll.le.trans (A.next.le.trans hk.le))) 0
local notation "F'" => (fun i=>writeF C (x₁ i) N k p a (x i) hk.le (ice i))
include hk
-- locality
lemma canopy (i:I) : Interior ((N*).chamber 0) (F' i):=by
    --
    let hp:= A.tall.hbar.trans (A.scroll.le.trans A.next.le); let v:= x₁ i; let X:= GridApprox.anchor C.S p hk.le (x i); unfold writeF; refine Interior.plus (A.seats N hk.le p X ?_ v) ((Safe.seen (h:=hp) (u:=(0:Site (C.side m p))) A.porch ?_).owns N hk.le le_rfl)
    · rw [show X=(C.S.toDepth hk.le p).embed (x i) from rfl,C.S.embeds_place]; exact (mul_le_mul_of_nonneg_left (Habits.tops i₀ he i |>.2) (by norm_num)).trans A.mount
    have hx:= dropped H (x i) v A.rank hk.le a (ice i); apply hx.enlarges; intro v hv; rw [show GridApprox.anchor C.S p hp 0=0 from (C.S.toDepth hp p).root.map_zero]; refine sparrow.mpr ((separation_triangle _ (x i) _).trans (Nat.add_le_add ?_ (sparrow.mp hv))); rw [separation_comm]; exact he.close i
-- numeric cost. simple generic weights; use count chosen.Inspect.A leg needs Bar cum >=b not n.Act.
include hf
lemma decayF (T₀:Citizen C W r D) {w:ℝ} {f:I→ℝ} (ht:0<t)(hv:∀ i, Spindle.paid C d k N p (x₁ i)≤ t')(hw:0<w)(hh:w*t' ≤ (ζ d k)) (hL:∀ i,0<f i)(hD:∀ i,payment C k a t' (ice i) ≤4*(1/f i))(hm: ∀ i,f i ≤ δ k*(η k*w)*Real.exp ((Loom.count C t k:ℝ)/24)) : ‖moment (C.beta N p) (fineJob (fun i=>writeF C (x₁ i) N k p a (x i) hk.le (ice i)) univ)‖≤ pound C b m z j k (Mast.PatrolFee C I j) f:=by
    let f'(i):=C.O N p (x₁ i) ((y i) N)+ GridApprox.backTo P N p hk.le (betaDrop C d k N p a (x₁ i) ((y i) k) (ice i)); have hF:f'= F':=by unfold f' writeF; unfold Function.comp; simp_rw [there,vect C k p N _ hk.le]
    have hb:=A.tall.down (C:=C) A.scroll.le (le_refl _); have hγ:= A.next; have hx:= A.scroll.trans hγ; have hQ (a b:V × I)(h:a≠b): (C.path.levels.budget k).B^8 ≤ separation ((U' k) a) ((U' k) b) :=by
       apply corners i₀ he A.mount hb hγ.le le_rfl _ a b h; intro i j hij; unfold Function.comp; rw [there,there]; exact A.paid.trans (he.apart i j hij)
    have hf' := ember (u:=a) H T₀ (covers_band i₀ he A.mount hb hf (living A) A.price hγ.le) (A.tall.hbar.trans hx.le) hk (A.notch.trans hx) A.rank (Habitat i₀ he A.mount hb hf (hγ.le.trans hk.le)) (fun a i hi _=> begins (x:=x) A hi a) hv (fun _=>hw) (fun _=>hh) hL (fun i j he=> A.gain.trans_le (hQ i j he)) (by
       refine Loom.buys (p:=Loom.count C t k) (fun _ _ a _ b _ h=> ?_) (C.path.levels.budget k|>.B_pos) (Loom.count_pos ht) (fun i=>hL i.snd) (fun _=>mul_pos ((H.brine k).water k le_rfl |>.2) (mul_pos ((H.brine k).water k le_rfl |>.1) hw)) (fun i=>hm i.snd)
       simpa only [Loom.stride,Nat.add_sub_cancel] using A.stride.trans (hQ a b h)) hD -- order parameter u!
    have hS:= shoring (w:=f) H i₀ (covers_band i₀ he A.mount hb hf (living A) A.price (le_refl j)) b (Habitat_root (p:=p) A (letI : Nonempty I:=⟨i₀⟩; Fintype.card_pos.trans_le hf)) A.notch A.scroll A.next A.tall.hbar hk.le (funext (Habits.loops0 i₀ he)) (show Shown C N p m k f' _ _ from hf') hf (investments i₀ he (living A) A.fine A.price (A.tall.hbar.trans A.scroll.le)); rw [hF] at hS; exact le_trans (atone _ _ (seamless H.seed ..) (Interior.combines _ _ (fun i _=> canopy H i₀ he A x₁ ice hk i))) hS -- canopy hk args
end YM.OPE.Strobe

