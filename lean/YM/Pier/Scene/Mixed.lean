import YM.Pier.Scene.Geometry
/-!
# Full-volume mixed native projections with ANY Aspect bound

Let every mark have its OWN physical column carrier (including different
canonical weights and grades) *before* the shared chronological march.
On each lattice and weighted leg at an eligible level there's a full-priced
Layout for this moment/tile comparison via flared evidence. Zoom every
separate mark through each step; `ShowF` etc track the complete regular and
forced thresholds. This intermediate result reaches a root expectation, not
pointwise density cost. Adapted from Strobe/Letter and Radar.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Strobe.Panoramic
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
variable {F:I→ Config G (C.side N p)→ℂ}{o:I→ ∀ i:ℕ, Site (C.side i p)}{w:I→ℕ→ℝ} {d₀:Finset I}{Y:I→∀ i:ℕ,Lamp G (C.side i p)}
local notation "Z" => royal C m p
local notation "r*" => stepUp
variable {x w:I→ℝ} {grade:I→ℕ} {f : (i:I)→ C.label (grade i)}{S:Extra.Histories.Music (C.labels.level d) C.path N p} {u K:ℕ} {ice : I → Bool}{ρ :ℝ}
include H
local notation "u!" => omen C d k u
local notation "o!" i => (fun a=> o a (i))
open Vitrines GridApprox
open Pier.Scene
local notation "U" => (fun i=>C.O N p (f i) (o i N))
local notation "Q'" => (fun i=> betaDrop C (grade i) k N p u (f i) (o i k) (ice i))
local notation "L" => ((Z k).place (o! k))
local notation "P'" => renal C.path.levels k
lemma alloyEmber (T₀ : Citizen C W r D)
    (E:Band C o r k N m)(hm:m≤k)(hk:k<N)(hl:C.ref 0 < k) (he:∀ i,C.ref (grade i) ≤ k)(hω:Occupancy ((Z N).place (o! N)) (r N)) (hA:∀ a,∀ i,k ≤ i→ i < N→ o a (i+1)= (C.path.levels.clock.op i p).ratio.embed (o a i)) (hL:∀ a, Spindle.paid C (grade a) k N p (f a) ≤ ρ)(hw:∀ a,0<w a)(hv:∀ a,w a*ρ ≤ ζ (grade a) k) (hy:∀ a,0<x a) (hsize:∀ i, omen C (grade i) k u ≤ K)(ht: ∀ i j, i≠j→ 2*muzzle C.path.levels k K< separation ((L) i) ((L) j))
    (hq:Repegs L (C.path.levels.budget k).B (fun j=> renal C.path.levels k*(near C.path.levels k*w j.snd)) (x ∘ Prod.snd) (1/2) 1 (Names (Site (C.side m p)) I))(hC:∀ a,payment C k u ρ (ice a) ≤ 4*(1/x a)): Shown C N p m k (fun i=> C.O N p (f i) (o i N)+ GridApprox.backTo C.path N p hk.le (betaDrop C (grade i) k N p u (f i) (o i k) (ice i))) (fun i=> o i k) x:=by
   choose S hS using fun i=> Yarn.curtain H (p:=p) (he i) hk.le; let X(i) := (C.factory (grade i) N p).terminal.symm (f i); let v₀ (i):= stair η (w i) k
   choose V' hV hP hT using fun i=> Yarn.first_wish H (o i) (hA i) (hS i) (he i) hk.le (hw i) (by unfold X; rw [Yarn.bond_paid (he i) hk.le (hS i)]; exact le_trans (mul_le_mul_of_nonneg_left (hL i) (hw i|>.le)) (hv i): w i*bond C.path N p (S i) k (X i) ≤ ζ (grade i) k) -- explicit X def rw needs
   let W':= Q'; let z i:= flickVolume (W' i) (V' i k); have hZ(i): (z i).Flex (R k) (o i k) (4*(1/x i)):= Blade.more (prizeMe (v:=f i) H T₀ (ice i) u (o i) (o i k) hl (he i) hk (hL i) (hS i) rfl (hT i k le_rfl hk.le|>.1) (hT i k le_rfl hk.le|>.2)) (hC i)
   let F' := U; have hp(i): Patent C N p (o i N) (V' i N) (F' i) (v₀ i N):=by have hx:= hP i; rw [show (C.factory (grade i) N p).terminal (X i)=f i from LinearEquiv.apply_symm_apply ..] at hx; exact hx
   have hF := flared H E hm hl hk W' z hp hV (fun a i _ _=>H.protectors _ (hw a) _ i) (fun i hi he a=> (H.fall_march hi.le).symm.le) hω (y:=x) (by unfold v₀; simp_rw [H.fall_march (Nat.le_refl k),H.anchor_march (hw _)]; exact hq) hy ht (fun i=> (dropped H _ _ (he i) hk.le u (ice i)).enlarges (fun _ hv=> sparrow.mpr ((sparrow.mp hv).trans (hsize i)))) (fun _=>rfl) (fun _=>rfl) -- x named y. fallback
   exact ⟨hF.choose,z,hF.choose_spec,hZ⟩ -- rev ?_
end YM.OPE.Strobe.Panoramic
set_option autoImplicit false

namespace YM.OPE.Strobe.Panoramic
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
open Pier.Scene
local notation "B" i => (C.path.levels.budget (i)).B
local notation "s" i => C.S.a (i)
variable {n t b a wide j':ℕ}{x:I→Site (C.side k p)} (i₀:I) (he:Nearest C k p n wide x i₀) (A:Passage C d j k n m z b r a t)
    (hf:Fintype.card I ≤ b)
local notation "y" => ((loops C k p) ∘ x)
local notation "U'" i => ((Z (i)).place (fun j=>(y j) (i)))
include H he
variable {grade:I→ℕ}(hl:∀ i, Passage C (grade i) j' k (wide*n) m z b r a t) (x₁:(i:I)→ C.label (grade i))(ice:I→Bool)(t':ℝ) (hk:k<N)
local notation "N*" => center C.S p (A.tall.hbar.trans (A.scroll.le.trans (A.next.le.trans hk.le))) 0
local notation "F'" => (fun i=>writeF C (x₁ i) N k p a (x i) hk.le (ice i))
include A hl hk
-- locality
omit [Fintype I] [DecidableEq I] in
lemma canopyWide (i:I) : Interior ((N*).chamber 0) (F' i):=by
    --
    let hp:= A.tall.hbar.trans (A.scroll.le.trans A.next.le); let v:= x₁ i; let X:= GridApprox.anchor C.S p hk.le (x i); unfold writeF; refine Interior.plus ((hl i).seats N hk.le p X ?_ v) ((Safe.seen (h:=hp) (u:=(0:Site (C.side m p))) (hl i).porch ?_).owns N hk.le le_rfl)
    · rw [show X=(C.S.toDepth hk.le p).embed (x i) from rfl,C.S.embeds_place]; exact (mul_le_mul_of_nonneg_left (Nearest.tops i₀ he i |>.2) (by norm_num)).trans (hl i).mount
    have hx:= dropped H (x i) v (hl i).rank hk.le a (ice i); apply hx.enlarges; intro v hv; rw [show GridApprox.anchor C.S p hp 0=0 from (C.S.toDepth hp p).root.map_zero]; refine sparrow.mpr ((separation_triangle _ (x i) _).trans (Nat.add_le_add ?_ (sparrow.mp hv))); rw [separation_comm]; exact he.close i
-- numeric cost. simple generic weights; use count chosen.Inspect.A leg needs Bar cum >=b not n.Act.
include hf
lemma decayWideF (hbig:1≤wide) (hsize:∀ i, omen C (grade i) k a ≤ omen C d k a) (T₀:Citizen C W r D) {w f:I→ℝ} (ht:0<t)(hv:∀ i, Spindle.paid C (grade i) k N p (x₁ i)≤ t')(hw:∀ i,0<w i)(hh:∀ i,w i*t' ≤ (ζ (grade i) k)) (hL:∀ i,0<f i)(hD:∀ i,payment C k a t' (ice i) ≤4*(1/f i))(hm: ∀ i,f i ≤ δ k*(η k*w i)*Real.exp ((Loom.count C t k:ℝ)/24)) : ‖moment (C.beta N p) (fineJob (fun i=>writeF C (x₁ i) N k p a (x i) hk.le (ice i)) univ)‖≤ pound C b m z j k (Mast.PatrolFee C (Fin wide) j) f:=by
    let f'(i):=C.O N p (x₁ i) ((y i) N)+ GridApprox.backTo P N p hk.le (betaDrop C (grade i) k N p a (x₁ i) ((y i) k) (ice i)); have hF:f'= F':=by unfold f' writeF; unfold Function.comp; simp_rw [there,vect C k p N _ hk.le]
    have hb:=A.tall.down (C:=C) A.scroll.le (le_refl _); have hγ:= A.next; have hx:= A.scroll.trans hγ; have hQ (a b:V × I)(h:a≠b): (C.path.levels.budget k).B^8 ≤ separation ((U' k) a) ((U' k) b) :=by
       apply cornersWide i₀ he (hl i₀).mount hb hγ.le le_rfl _ a b h; intro i j hij; unfold Function.comp; rw [there,there]; exact A.paid.trans (he.apart i j hij)
    have hf' := alloyEmber (u:=a) H T₀ (covers_bandWide i₀ he (hl i₀).mount hb hf (living A) A.price hγ.le) (A.tall.hbar.trans hx.le) hk (A.notch.trans hx) (fun i=>(hl i).rank) (HabitatWide i₀ he (hl i₀).mount hb hf (hγ.le.trans hk.le)) (fun a i hi _=> begins (x:=x) A hi a) hv hw hh hL hsize (fun i j he=> A.gain.trans_le (hQ i j he)) (by
       refine Loom.buys (p:=Loom.count C t k) (fun _ _ a _ b _ h=> ?_) (C.path.levels.budget k|>.B_pos) (Loom.count_pos ht) (fun i=>hL i.snd) (fun a=>mul_pos ((H.brine k).water k le_rfl |>.2) (mul_pos ((H.brine k).water k le_rfl |>.1) (hw a.2))) (fun i=>hm i.snd)
       simpa only [Loom.stride,Nat.add_sub_cancel] using A.stride.trans (hQ a b h)) hD -- order parameter u!
    have hS:= shoring (w:=f) H i₀ (covers_bandWide i₀ he (hl i₀).mount hb hf (living A) A.price (le_refl j)) b (Habitat_root (p:=p) A (letI : Nonempty I:=⟨i₀⟩; Fintype.card_pos.trans_le hf)) A.notch A.scroll A.next A.tall.hbar hk.le (funext (Nearest.loops0 i₀ he)) (show Shown C N p m k f' _ _ from hf') hf (investmentsWide i₀ he (living A) A.fine A.price (A.tall.hbar.trans A.scroll.le) hbig); rw [hF] at hS; exact le_trans (atone _ _ (seamless H.seed ..) (Interior.combines _ _ (fun i _=> canopyWide H i₀ he A hl x₁ ice hk i))) hS -- canopy hk args
end YM.OPE.Strobe.Panoramic
