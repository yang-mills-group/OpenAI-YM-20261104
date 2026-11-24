import YM.Agora26.Marks.Geometric

/-!
# Joint discrepancy slot with label-dependent horizons

Multi-price version of Strobe/Letter `ember`; history pricing (Patrol, lamp,
Serves, gauge/health/masks, disjoint selection, last-step repeg) that earns
the proof is unchanged; we keep these exact full-density results in scope.
All copies still on one estimated presentation. Last-step clearance/gain paid
on the maximum omen over these horizons.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Strobe
namespace Vista26
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
local notation "γ" => ((1,false):Motion)
variable {x w:I→ℝ} {d':I→ℕ}{f : (i:I)→ C.label (d' i)} {u ξ:ℕ} {ice : I → Bool}{ρ :ℝ}
include H
local notation "s!" i => (C.factory (d' i) N p)
local notation "o!" i => (fun a=> o a (i))
open Vitrines GridApprox
local notation "U" => (fun i=>C.O N p (f i) (o i N))
local notation "Q'" => (fun i=> betaDrop C (d' i) k N p u (f i) (o i k) (ice i))
local notation "L" => ((Z k).place (o! k))
local notation "P'" => renal C.path.levels k
lemma ember (T₀ : Citizen C W r D)
    (E:Band C o r k N m)(hm:m≤k)(hk:k<N)(hl:C.ref 0 < k) (he:∀ a,C.ref (d' a) ≤ k)(hω:Occupancy ((Z N).place (o! N)) (r N)) (hA:∀ a,∀ i,k ≤ i→ i < N→ o a (i+1)= (C.path.levels.clock.op i p).ratio.embed (o a i)) (hL:∀ a, Spindle.paid C (d' a) k N p (f a) ≤ ρ)(hw:∀ a,0<w a)(hv:∀ a,w a*ρ ≤ ζ (d' a) k) (hy:∀ a,0<x a) (hu:∀ i, omen C (d' i) k u ≤ ξ)(ht: ∀ i j, i≠j→ 2*muzzle C.path.levels k ξ< separation ((L) i) ((L) j))
    (hq:Repegs L (C.path.levels.budget k).B (fun j=> renal C.path.levels k*(near C.path.levels k*w j.snd)) (x ∘ Prod.snd) (1/2) 1 (Names (Site (C.side m p)) I))(hC:∀ a,payment C k u ρ (ice a) ≤ 4*(1/x a)): Shown C N p m k (fun i=> C.O N p (f i) (o i N)+ GridApprox.backTo C.path N p hk.le (betaDrop C (d' i) k N p u (f i) (o i k) (ice i))) (fun i=> o i k) x:=by
   choose S hS using fun i=> Yarn.curtain H (p:=p) (he i) hk.le
   let X(i):=(s! i).terminal.symm (f i); let v₀(i):=stair η (w i) k
   choose V' hV hP hT using fun i=> Yarn.first_wish H (o i) (hA i) (hS i) (he i) hk.le (hw i)
      (by unfold X; rw [Yarn.bond_paid (he i) hk.le (hS i)]; exact le_trans (mul_le_mul_of_nonneg_left (hL i) (hw i|>.le)) (hv i)
        : w i*bond C.path N p (S i) k (X i) ≤ ζ (d' i) k)
   let W':= Q'; let z i:= flickVolume (W' i) (V' i k)
   have hZ(i): (z i).Flex (R k) (o i k) (4*(1/x i)):= Blade.more
      (prizeMe (v:=f i) H T₀ (ice i) u (o i) (o i k) hl (he i) hk (hL i) (hS i) rfl (hT i k le_rfl hk.le|>.1) (hT i k le_rfl hk.le|>.2)) (hC i)
   let F' := U
   have hp(i): Patent C N p (o i N) (V' i N) (F' i) (v₀ i N):=by
      have hx:= hP i; rw [show (C.factory _ N p).terminal (X i)=f i from LinearEquiv.apply_symm_apply _ _] at hx; exact hx
   have hW(i): Interior (GridApprox.window (o i k) ξ) (W' i):= (dropped H _ _ (he i) hk.le u (ice i)).enlarges (by
      intro v hv
      exact sparrow.mpr ((sparrow.mp hv).trans (hu _)))
   have hF := flared H E hm hl hk W' z hp hV (fun a i _ _=>H.protectors _ (hw a) _ i) (fun i hi _ a=> (H.fall_march hi.le).symm.le) hω (y:=x) (show Repegs _ _ (fun j:V × I=> P'*v₀ j.2 (k+1)) _ _ _ _ from by
      unfold v₀; simp_rw [H.fall_march (Nat.le_refl k),H.anchor_march (hw _)]; exact hq) hy ht hW (fun _=>rfl) (fun _=>rfl)
   exact ⟨hF.choose,z,hF.choose_spec,hZ⟩
end Vista26
end YM.OPE.Strobe

namespace YM.OPE.Strobe.Vista26
open Yarn
open Function Filter Set MeasureTheory Finset Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Overlay
open MergeProof Accent Ribbons ManyCopies MergeProof.Float PhysicalNext.Repeat Lotus Legato Mallow Bandage Patrol Loom
open Yarn.SitePlan Next.Rank.Station
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
variable {o:I→ ∀ i:ℕ, Site (C.side i p)} {n br a b t:ℕ}
variable {x:I→Site (C.side k p)}
-- retain Passage, widen its mount & porch; births can use dependent d for each leg
structure Further26 (C:Family G) (d j k n m z b:ℕ)(r:ℕ→ℕ)(a t br:ℕ): Prop extends Passage C d j k n m z b r a t where
    gmount : 8*(2*C.S.a k *(↑(br*n):ℝ))≤ C.S.a m
    gporch : GridApprox.room C.path.levels m k (br*n+omen C d k a)

local notation "B" i => (C.path.levels.budget (i)).B
local notation "y" => ((loops C k p) ∘ x)
local notation "U'" i => ((Z (i)).place (fun j=>(y j) (i)))

-- Adapted from Strobe/Radar canopy.
include H
lemma canopy (i₀:I) (he:Range26 C k p n br x i₀) (A:Further26 C d j k n m z b r a t br)
    (x₁:C.label d)(ice:Bool)(hk:k<N) (i:I) :
    Interior ((center C.S p (A.tall.hbar.trans (A.scroll.le.trans (A.next.le.trans hk.le))) 0).chamber 0)
      (writeF C x₁ N k p a (x i) hk.le ice):=by
    let hp:= A.tall.hbar.trans (A.scroll.le.trans A.next.le); let v:= x₁; let X:= GridApprox.anchor C.S p hk.le (x i); unfold writeF; refine Interior.plus (A.seats N hk.le p X ?_ v) ((Safe.seen (h:=hp) (u:=(0:Site (C.side m p))) A.gporch ?_).owns N hk.le le_rfl)
    · rw [show X=(C.S.toDepth hk.le p).embed (x i) from rfl,C.S.embeds_place]; exact (mul_le_mul_of_nonneg_left (Range26.tops i₀ he i |>.2) (by norm_num)).trans A.gmount
    have hx:= dropped H (x i) v A.rank hk.le a ice; apply hx.enlarges; intro v hv; rw [show GridApprox.anchor C.S p hp 0=0 from (C.S.toDepth hp p).root.map_zero]; refine sparrow.mpr ((separation_triangle _ (x i) _).trans (Nat.add_le_add ?_ (sparrow.mp hv))); rw [separation_comm]; exact he.close i
omit [Fintype J] [DecidableEq J] in
lemma room_too (br:ℕ){φ:Filter J}{k n:J→ℕ}(L:GracesP C φ k n)(S:Citizen C W r D) (d t:ℕ) (hZ:Barrow C r m b z)(hz:C.ref 0<z) :
    ∀ᶠ i in φ, Further26 C d (chapter C (k i) (n i)) (k i) (n i) m z b r (B (k i)) t br:=by
   let X i:= (B i)^8
   have hC:= C.S.divergent
   have hδ:= C.S.divergent.comp L.seeks
   have hv':RateLE φ (C.S.scale ∘ k) (fun i=> C.S.a (k i)*(n i:ℝ)) ((-1:ℝ)+0):=
      RateLE.mul (L.ages.mesh.pays hδ) (rapid hδ L.ear (RateLE.const 1 hδ))
   have hv : Tendsto (fun i=> C.S.a (k i)*(n i:ℝ)) φ (𝓝 0):= hv'.tends (by norm_num) hδ
   have h0:Tendsto (fun i=> C.S.a (k i)* (↑(br*n i):ℝ)) φ (𝓝 0):=by
      have ht:= hv.mul_const (br:ℝ); rw [zero_mul] at ht; apply ht.congr' (?_)
      filter_upwards with i; push_cast; ring
   have h1 : Tendsto (fun i=>C.S.a i*(X i:ℝ)) atTop (𝓝 0):=((RateLE.mul ((first_price (C:=C)).mesh.pays hC) (rapid hC (show Cheap atTop C.S.scale (fun i=>(X i:ℝ)) from by unfold X; push_cast; exact Cheap.power (covers_p (C:=C) hC first_price|>.up) hC _) (RateLE.const 1 hC))).tends (by norm_num) hC)
   let u:= C.S.a m/32; have hu : 0<u:= div_pos (C.S.a_pos _) (by norm_num)
   filter_upwards [bolted H L S d t hZ hz,h0.eventually (gt_mem_nhds hu), (h1.comp L.seeks).eventually (gt_mem_nhds hu), (GridApprox.tail_zero T |>.comp L.seeks).eventually (gt_mem_nhds hu)] with i hi ha hB hT
   let d₀:= omen C d (k i) (B (k i)); have he: (d₀:ℝ) ≤ X (k i):= by exact_mod_cast (show d₀ ≤ X (k i) from by have ht:=hi.gain; change 2*(d₀+_) < X (k i) at ht; omega)
   let a₀:=C.S.a (k i); have hf:0<a₀:=C.S.a_pos _; have hE : a₀*(↑(br*n i):ℝ)<u:=ha; have hG: a₀*(d₀:ℝ) <u:= lt_of_le_of_lt (mul_le_mul_of_nonneg_left he hf.le) hB; have hW : GridApprox.tail T (k i)<u:=hT
   refine ⟨hi,?_,?_⟩
   · change 8*(2*a₀*(↑(br*n i):ℝ)) ≤ _; unfold u at hE hu; linarith only [hE,hu]
   unfold GridApprox.room; rw [Nat.cast_add]; change 2*(a₀*((↑(br*n i):ℝ)+ d₀)+_) < _; unfold u at hE hG hW hu; nlinarith only [hE,hG,hW,hu]

lemma earn (i₀:I)(he:Range26 C k p n br x i₀){d:I→ℕ}
    (A:∀ i,Further26 C (d i) j k n m z b r a t br)
    (hf:Fintype.card I≤b)(x₁:(i:I)→C.label (d i))(ice:I→Bool)(t':ℝ)(hk:k<N)(T₀:Citizen C W r D) {w f:I→ℝ}
    (hbr:0<br)(ht:0<t)(hv:∀ i, Spindle.paid C (d i) k N p (x₁ i)≤ t')(hw:∀ i,0<w i)(hh:∀ i,w i*t' ≤ ζ (d i) k) (hL:∀ i,0<f i)(hD:∀ i,payment C k a t' (ice i) ≤4*(1/f i))(hm: ∀ i,f i ≤ δ k*(η k*w i)*Real.exp ((Loom.count C t k:ℝ)/24)) :
    ‖moment (C.beta N p) (fineJob (fun i=>writeF C (x₁ i) N k p a (x i) hk.le (ice i)) univ)‖≤ pound C b m z j k (Mast.PatrolFee C (I×Fin br) j) f:=by
    let f'(i):=C.O N p (x₁ i) ((y i) N)+ GridApprox.backTo P N p hk.le (betaDrop C (d i) k N p a (x₁ i) ((y i) k) (ice i));
    let F':=fun i=>writeF C (x₁ i) N k p a (x i) hk.le (ice i)
    have hF:f'= F':=by unfold f' F' writeF; unfold Function.comp; simp_rw [there,vect C k p N _ hk.le]
    let A₀:= A i₀; let A':=A₀.toPassage
    have hb:=A₀.tall.down (C:=C) A₀.scroll.le (le_refl _); have hγ:= A₀.next; have hx:= A₀.scroll.trans hγ; have hQ (v z:V × I)(h:v≠z): (C.path.levels.budget k).B^8 ≤ separation ((U' k) v) ((U' k) z) :=by
       apply corners i₀ he A₀.gmount hb hγ.le le_rfl _ v z h; intro i j hij; unfold Function.comp; rw [there,there]; exact A₀.paid.trans (he.apart i j hij)
    obtain ⟨s,hs,hs'⟩:= Finset.exists_max_image univ (fun i:I=> omen C (d i) k a) (show (univ:Finset I).Nonempty from ⟨i₀,mem_univ _⟩)
    have hf' := ember (u:=a) H T₀ (covers_band i₀ he A₀.gmount hb hf (living A') A'.price hγ.le) (A'.tall.hbar.trans hx.le) hk (A'.notch.trans hx) (fun i=> (A i).rank) (Habitat i₀ he A₀.gmount hb hf (hγ.le.trans hk.le)) (fun a i hi _=> begins (x:=x) A' hi a) hv hw hh hL (fun j=> hs' j (mem_univ _)) (fun i j he=> (A s).gain.trans_le (hQ i j he)) (by
       refine Loom.buys (p:=Loom.count C t k) (fun _ _ a _ b _ h=> ?_) (C.path.levels.budget k|>.B_pos) (Loom.count_pos ht) (fun i=>hL i.snd) (fun i=>mul_pos ((H.brine k).water k le_rfl |>.2) (mul_pos ((H.brine k).water k le_rfl |>.1) (hw i.snd))) (fun i=>hm i.snd)
       simpa only [Loom.stride,Nat.add_sub_cancel] using A'.stride.trans (hQ a b h)) hD
    have hS:= shoring (w:=f) H i₀ (covers_band i₀ he A₀.gmount hb hf (living A') A'.price (le_refl j)) b (Habitat_root (p:=p) A' (letI : Nonempty I:=⟨i₀⟩; Fintype.card_pos.trans_le hf)) A'.notch A'.scroll A'.next A'.tall.hbar hk.le (funext (Range26.loops0 i₀ he)) (show Shown C N p m k f' _ _ from hf') hf (investments i₀ he (living A') A'.fine A'.price (A'.tall.hbar.trans A'.scroll.le) hbr)
    rw [hF] at hS; exact le_trans (atone _ _ (seamless H.seed ..) (Interior.combines _ _ (fun i _=> canopy H i₀ he (A i) (x₁ i) (ice i) hk i))) hS
end YM.OPE.Strobe.Vista26

