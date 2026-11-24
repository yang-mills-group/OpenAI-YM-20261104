import YM.WilsonCoeffUV.Vacuum.Step.UniformPrice
/-!
# Domains for gear-dependent charges. L happens after overlapping real widths.
Gap constants post for all incl M-base difference.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Next.Free PowerSeries
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{r e m k n:ℕ}

-- R free pre for projection at output (may independently enlarge).
structure Gear (G:Gauge) where
   patch : Patch
   kernel : KernelChoices
   angle : ChartRatio G
   past: ℝ -- inlet t
   s : ℝ -- cross s > outlet
   σ : ℝ -- outlet >0
   price: 0<σ
   holds: σ<s
   depth: 0<past
   room : s/patch.L.val ≤ past
   preB : ℝ
   sig : ℝ -- free coarse Z bound
   D : ℝ -- any post constant incl inverse cost
   pre_nn : 0≤ preB
   tag_nn: 0≤ sig
   bill_nn : 1≤ D

variable (I:Gear G)
abbrev Helms (I:Gear G):= Hinge G I.patch.L
abbrev Pick (I:Gear G):= Larvae G I.patch.L

structure Stand (I:Gear G) where
    page : Canvas G
    M : ropes Cover (Larvae G I.patch.L) (Hooks G)
    T : ReaderT I.patch.L G
    Q : ropes Cover (Larvae G I.patch.L) (Hooks G)
    Z : ropes Cover (Hooks G) (Hooks G)
    R : ropes Cover (Larvae G I.patch.L) (Larvae G I.patch.L)
    crank : Crank M 3 I.s I.preB
    rule : verdant M Q T
    topQ : dragCup terrain I.s I.sig Z
    rolls: dragCup terrain I.s I.D T
    -- semantic rows for SAME-grade and local reclosure
    sym i : Pure (page i)
    move i r : stroll (page i r)
    even_page : vertical page
    bit i : 0< i → AxisClear (page i)
    negative k : spurs I.patch I.kernel I.angle R Q page k 0=0
    mint: readSun (orbQ Z)=1
    lead : tinge I.patch I.kernel I.angle Z R Q page 0= shine (orbQ Z)
    ez : ∀ i,∃ s A,0<s ∧ Amber terrain s A (tinge I.patch I.kernel I.angle Z R Q page i 2)

namespace Stand
variable {I} (T:Stand I)
abbrev rays:= spurs I.patch I.kernel I.angle T.R T.Q T.page
abbrev driftU := tinge I.patch I.kernel I.angle T.Z T.R T.Q T.page
def moving := back (Kstar T.driftU)
def stake := Blue.mix T.moving (lop T.driftU)
lemma sunshine : constantCoeff (Kstar T.driftU)=1:= by rw [← coeff_zero_eq_constantCoeff_apply,stellar_read, show T.driftU 0= _ from T.lead, shine_lit,T.mint]
lemma starlit : Kstar T.stake=1 := begin_again T.sunshine T.ez
end Stand

def lowerGrade (i r k j:ℕ):Prop:= i< k ∨ i=k ∧ j< r
lemma lowR (k i j r:ℕ)(h:i< k):lowerGrade i j k r:= Or.inl h

-- assumes the coverage at EVERY lower location. restrict by shell later.
structure Rally (k r :ℕ)(I: Gear G) where
   x:ℝ
   σ:ℝ
   rich: 1≤ x
   θ : 0≤σ
   P: Stand I
   Q: Stand I
   paid i j: lowerGrade i j k r → PairA I.past x σ (P.page i j) (Q.page i j)
   Υ: Ballast I.s I.D σ P.Q Q.Q
   Χ: Ballast I.s I.D σ P.R Q.R
   Ω: Ballast I.s I.D σ P.Z Q.Z
lemma permits (I:Gear G)(e r:ℕ): Brite (Rally.x (k:=e) (r:=r) (I:=I)) Rally.σ:= ⟨fun v=>v.rich,fun v=>v.θ⟩
-- r threshold may Nat usage; to request all even rank zero at order e need special sentinel (e+1, arbitrary => works)

-- stack
lemma skyPay {p t:Gear G→ℝ}{e r:ℕ}{S: (I:Gear G)→ Rally e r I → Ten ℝ (Cloth (Helms I)) k}{G': (I:Gear G)→ Rally e r I→ Ten ℝ (Cloth (Helms I)) k} (h:Satin (fun _=>Rally.x) (fun _=>Rally.σ) p S G') (hT:∀ i,t i≤p i): Satin (fun _=>Rally.x) (fun _=>Rally.σ) t S G':=by
    obtain ⟨d,h⟩:=h; refine ⟨d,fun i=>?_⟩; obtain ⟨A,h,e⟩:= h i; exact ⟨A,h,fun j=> ⟨(e j).pose.mono (hT i),(e j).vale.mono (hT i),(e j).visit.mono (hT i)⟩⟩
-- log prep before optic (exclude W positive terms)
def intake (I:Gear G)(T:Stand I) (e:ℕ): Gen ℝ (Cloth (Helms I)):=
   prism (upper 1 T.Q) (plants I.patch.L (bearingJ I.angle e))- prism (stair (upper 1 T.Q) ladder) (scrub (warren I.patch I.kernel G) e)

abbrev LapFold (I:Gear G) (P:Stand I): Scroll G I.patch:= stellar I.patch I.kernel I.angle P.Q P.page

section pressure
variable {k' j:ℕ}
abbrev largus (k r:ℕ)(I:Gear G): Rally k r I→ ℝ:=Rally.x
abbrev smallus (k r:ℕ)(I:Gear G): Rally k r I→ ℝ:=Rally.σ
abbrev upperP (V:Rally k r I):= upper (1:ropes Cover (Pick I) (Pick I)) V.P.Q
abbrev upperQ (V:Rally k r I):= upper (1:ropes Cover (Pick I) (Pick I)) V.Q.Q
lemma votes (I:Gear G)(A:Rally k r I): Ballast I.s I.D A.σ (upper 1 A.P.Q) (upper 1 A.Q.Q):= Ballast.up (Ballast.same (dragCup.one.le I.bill_nn) A.θ) A.Υ
lemma pinkP {w:Gear G→ℝ}(e k r j:ℕ)(hp:∀ I,0≤w I)(h:∀ I,w I<I.s): Satin (largus k r) (smallus k r) w (fun I Q=> prism (upperP I Q) (plants I.patch.L (bearingJ I.angle e)) j) (fun I Q=> prism (upperQ I Q) (plants I.patch.L (bearingJ I.angle e)) j):= by
    have hx I: 0 ≤ Gear.D I:= le_trans zero_le_one (Gear.bill_nn I (G:=G));
    have h₀ : Satin (largus k r (G:=G)) (smallus k r) Gear.s (fun I _=>plants I.patch.L (bearingJ I.angle e) j) (fun I _=>plants I.patch.L (bearingJ I.angle e) j):= by
       apply Satin.fixed (fun I=>permits I k r) (P:=fun I=>plants I.patch.L (bearingJ I.angle e) j)
       intro I; obtain ⟨A,hA⟩:= bloom_bill I.angle e j I.past I.depth.le; have hh:= PairA.pack (P:=bearingJ I.angle e) (Q:=bearingJ I.angle e) (PairA.echo (δ:=0) hA le_rfl) (lt_trans I.price I.holds).le I.room; exact ⟨_,hh.pose⟩
    exact Satin.meld (P:=fun I _=>plants I.patch.L (bearingJ I.angle e)) (Q:=fun I _=>plants I.patch.L (bearingJ I.angle e)) (α:=Pick) (β:=Helms) hp h hx (fun I=>permits I k r) votes h₀
lemma pinkQ {w:Gear G→ℝ}(e k r j:ℕ)(hp:∀ I,0≤w I)(h:∀ I,w I<I.s): Satin (largus k r) (smallus k r) w (fun I Q=> prism (stair (upperP I Q) ladder) (scrub (warren I.patch I.kernel G) e) j) (fun I Q=>prism (stair (upperQ I Q) ladder) (scrub (warren I.patch I.kernel G) e) j):= by
    have hx I: 0 ≤ Gear.D I:= le_trans zero_le_one (Gear.bill_nn I (G:=G));
    have hu (I:Gear G): ∃ A,Amber terrain I.s A (scrub (warren I.patch I.kernel G) e j):=by
        unfold scrub; split; · exact ⟨0, Amber.zero⟩
        exact tide_pay I.patch I.kernel G e j I.s (lt_trans I.price I.holds).le
    have H: Satin (fun I=>Rally.x (I:=I) (k:=k) (r:=r)) (fun _=> Rally.σ) Gear.s (fun I _=> scrub (warren I.patch I.kernel G) e j) (fun I _=>scrub (warren I.patch I.kernel G) e j):= Satin.fixed (fun I=> permits I k r) hu
    exact Satin.meld (P:=fun I _=>scrub (warren I.patch I.kernel G) e) (Q:=fun I _=>scrub (warren I.patch I.kernel G) e) (α:=Helms) (β:=Helms) hp h hx (fun I=>permits I k r) (fun I j=> Ballast.staged (votes I j) (Ballast.same (ladder_amber.le I.bill_nn) j.θ)) H
lemma intake_frames {w:Gear G→ℝ}(e k r j:ℕ) (hp:∀ I,0≤w I)(h:∀ I,w I<I.s): Satin (fun I=> Rally.x (I:=I) (r:=r) (k:=k)) (fun _=>Rally.σ) w (fun I Q=> intake I Q.P e j) (fun I Q=> intake I Q.Q e j):=by
    exact (pinkP e k r j hp h).sub (pinkQ e k r j hp h) (fun I=> permits I k r)

lemma intones {w:Gear G→ℝ}{e k r j:ℕ}(b:lowerGrade e j k r)(hp:∀ I,0≤w I)(h:∀ I,w I<I.s): Satin (fun I=> Rally.x (I:=I) (r:=r) (k:=k)) (fun _=>Rally.σ) w (fun I Q=> LapFold I Q.P e j) (fun I Q=> LapFold I Q.Q e j):=by
    have ht: Satin (fun I=>Rally.x (I:=I) (k:=k) (r:=r)) (fun _=>Rally.σ) (Gear.past (G:=G)) (fun I i=>scrub i.P.page e j) (fun I i=>scrub i.Q.page e j):=by
        unfold scrub; split; · exact Satin.zero
        exact Satin.start fun i j=> j.paid _ _ b
    have hy:= Satin.tiles (P:=fun (I:Gear G) (i:Rally k r I)=> scrub i.P.page e) (Q:=fun I i=>scrub i.Q.page e) ht (fun I=>I.patch.L) (he:=fun i=> (lt_trans i.price i.holds).le) (s:=Gear.s) (HP:=fun i=> i.room)
    have H:= Satin.meld (P:=fun (I:Gear G) (i:Rally k r I)=>plants I.patch.L (scrub i.P.page e)) (Q:=fun I i=>plants I.patch.L (scrub i.Q.page e)) hp h (fun I=>zero_le_one.trans (Gear.bill_nn I)) (fun I=>permits I k r) (fun I A=> Ballast.up (Ballast.same (dragCup.one.le I.bill_nn) A.θ) A.Υ) hy
    exact (intake_frames e k r j hp h).sub H (fun I=>permits I k r)
end pressure
end YM.WilsonCoeffUV.Bank
