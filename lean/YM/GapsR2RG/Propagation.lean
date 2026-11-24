import YM.OPE.Strobe.Radar
import YM.GapsR2RG.Geometry
/-!
# Propagation of designated error slots on the shared represented history.

Same Strobe machinery with aspect-ratio fee and mixed horizons. Keep complete
array/bare-law identities, not products of independently measured fields, and
leave the UV cutoff unbounded above. Bolt payment next.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GapsR2RG
open OPE OPE.Yarn OPE.Strobe
open Function Filter Set MeasureTheory Finset Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Overlay
open MergeProof Accent Ribbons ManyCopies MergeProof.Float PhysicalNext.Repeat Lotus Legato Mallow Bandage Patrol OPE.Loom
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {I:Type}[Fintype I][DecidableEq I]{G:Gauge}{C:Family G}{k z i j l m p N:ℕ}{d:I→ℕ}
variable {W r D}{σ χ:ℕ→ℝ} (H:OPE.Yarn.Tune C W r D σ χ)
set_option quotPrecheck false
local notation "V" => Site (C.side m p)
local notation "Z"=> royal C m p
local notation "P" => C.path
local notation "T" => C.path.levels
open Yarn.SitePlan Next.Rank.Station
variable {n b E t a:ℕ}

/- Heterogeneous version of `ember`, with any one common droplet radius A
bounding all the subtractions and paid slot-by-slot. -/
section
local notation "δ" => renal C.path.levels
local notation "η" => near C.path.levels
local notation "ζ" => fly C.path.levels
variable {w x':I→ℝ} {f : (i:I)→ C.label (d i)} {u:ℕ} {ice : I → Bool}{ρ :ℝ}
    {o:I→ ∀ i:ℕ, Site (C.side i p)}
local notation "U" => (fun i=>C.O N p (f i) (o i N))
local notation "L" => ((Z k).place (fun i=>o i k))
include H
lemma flaredMixed (T₀ : Citizen C W r D)
    (E0:Band C o r k N m)(hm:m≤k)(hk:k<N)(hl:C.ref 0 < k)(he:∀ i:I,C.ref (d i) ≤ k)(hω:Occupancy ((Z N).place (fun i=>o i N)) (r N))
    (hA:∀ a,∀ i,k ≤ i→ i < N→ o a (i+1)= (C.path.levels.clock.op i p).ratio.embed (o a i)) (hL:∀ a, Spindle.paid C (d a) k N p (f a) ≤ ρ)(hw:∀ a,0<w a)(hv:∀ a,w a*ρ ≤ ζ (d a) k)
    (y:I→ℝ)(u:ℕ)(ice:I→Bool)(hy:∀ a,0<y a)(A:ℕ)(hu:∀ i:I, omen C (d i) k u ≤ A)
    (ht: ∀ i j:V×I, i≠j→ 2*muzzle C.path.levels k A< separation ((L) i) ((L) j))
    (hq:Repegs L (C.path.levels.budget k).B (fun j=> renal C.path.levels k*(near C.path.levels k*w j.snd)) (y ∘ Prod.snd) (1/2) 1 (Names (Site (C.side m p)) I))(hC:∀ a,payment C k u ρ (ice a) ≤ 4*(1/y a)):
    Shown C N p m k (fun i=> C.O N p (f i) (o i N)+ GridApprox.backTo C.path N p hk.le (betaDrop C (d i) k N p u (f i) (o i k) (ice i))) (fun i=> o i k) y:=by
    choose S hS using fun i=> Yarn.curtain H (p:=p) (he i) hk.le; let X(i):= ((C.factory (d i) N p).terminal.symm (f i)); let v₀ (i):= stair η (w i) k
    choose V' hV hP hS' using fun i=> Yarn.first_wish H (o i) (hA i) (hS i) (he i) hk.le (hw i) (by unfold X; rw [Yarn.bond_paid (he i) hk.le (hS i)]; exact le_trans (mul_le_mul_of_nonneg_left (hL i) (hw i|>.le)) (hv i): w i*bond C.path N p (S i) k (X i) ≤ ζ (d i) k)
    let W' i:= betaDrop C (d i) k N p u (f i) (o i k) (ice i); let z i:= flickVolume (W' i) (V' i k); have hZ(i): (z i).Flex (C.path.rep N p k) (o i k) (4*(1/y i)):= Blade.more (prizeMe (v:=f i) H T₀ (ice i) u (o i) (o i k) hl (he i) hk (hL i) (hS i) rfl (hS' i k le_rfl hk.le|>.1) (hS' i k le_rfl hk.le|>.2)) (hC i)
    let F' := U; have hp(i): Patent C N p (o i N) (V' i N) (F' i) (v₀ i N):=by have hx:= hP i; rw [show (C.factory (d i) N p).terminal (X i)=f i from LinearEquiv.apply_symm_apply ..] at hx; exact hx
    have hF := flared H E0 hm hl hk W' z hp hV (fun a i _ _=>H.protectors _ (hw a) _ i) (fun i hi he a=> (H.fall_march hi.le).symm.le) hω (y:=y) (by change Repegs _ _ (fun j:V × I=> renal C.path.levels k * v₀ j.2 (k+1)) _ _ _ _; unfold v₀; simp_rw [H.fall_march (Nat.le_refl k),H.anchor_march (hw _)]; exact hq) hy ht (fun i=> (dropped H _ _ (he i) hk.le ..).enlarges (fun _ hx=>sparrow.mpr ((sparrow.mp hx).trans (hu i)))) (fun _=>rfl) (fun _=>rfl)
    exact ⟨hF.choose,z,hF.choose_spec,hZ⟩
end

structure Retreat (C:Family G)(d:I→ℕ)(j k n m z b:ℕ)(r:ℕ→ℕ)(a t E:ℕ): Prop where
    every i : Passage C (d i) j k n m z b r a t
    tower : 8*(2*C.S.a k *(E*n:ℝ))≤ C.S.a m
    clearance i : GridApprox.room C.path.levels m k (E*n+omen C (d i) k a)
variable {x:I→ Site (C.side k p)}(i₀:I) (he:Annular C k p n E x i₀) (A:Retreat C d j k n m z b r a t E) (hk:k<N)
include A H he hk
lemma canopy (x₁:(i:I)→C.label (d i)) (ice:I→Bool) (i:I) : Interior ((center C.S p ((A.every i).tall.hbar.trans ((A.every i).scroll.le.trans ((A.every i).next.le.trans hk.le))) 0).chamber 0) (writeF C (x₁ i) N k p a (x i) hk.le (ice i)):=by
    --
    let hp:= (A.every i).tall.hbar.trans ((A.every i).scroll.le.trans (A.every i).next.le); let v:= x₁ i; let X:= GridApprox.anchor C.S p hk.le (x i); unfold writeF; refine Interior.plus ((A.every i).seats N hk.le p X ?_ v) ((Safe.seen (h:=hp) (u:=(0:Site (C.side m p))) (A.clearance i) ?_).owns N hk.le le_rfl)
    · rw [show X=(C.S.toDepth hk.le p).embed (x i) from rfl,C.S.embeds_place]; exact (mul_le_mul_of_nonneg_left (Annular.tops i₀ he i |>.2) (by norm_num)).trans A.tower
    have hx:= dropped H (x i) v (A.every i).rank hk.le a (ice i); apply hx.enlarges; intro v hv; rw [show GridApprox.anchor C.S p hp 0=0 from (C.S.toDepth hp p).root.map_zero]; refine sparrow.mpr ((separation_triangle _ (x i) _).trans (Nat.add_le_add ?_ (sparrow.mp hv))); rw [separation_comm]; exact he.close i

-- numeric cost as for one homogeneous Strobe.
variable (hf:Fintype.card I ≤ b) (x₁:(i:I)→ C.label (d i))(ice:I→Bool)(t':ℝ)
include hf
local notation "y" => ((loops C k p) ∘ x)
local notation "U'" i => ((Z (i)).place (fun j=>(y j) (i)))
local notation "F'" => (fun i=>writeF C (x₁ i) N k p a (x i) hk.le (ice i))
local notation "A'" => A.every i₀
set_option maxHeartbeats 500000 in
theorem decay (T₀:Citizen C W r D) {w f:I→ℝ} (ht:0<t)(hE:0<E)(hv:∀ i, Spindle.paid C (d i) k N p (x₁ i)≤ t')(hw:∀ i,0<w i)(hh:∀ i,w i*t' ≤ (fly C.path.levels (d i) k)) (hL:∀ i,0<f i)(hD:∀ i,payment C k a t' (ice i) ≤4*(1/f i))(hm: ∀ i,f i ≤ renal C.path.levels k*(near C.path.levels k*w i)*Real.exp ((Loom.count C t k:ℝ)/24)) : ‖moment (C.beta N p) (fineJob (fun i=>writeF C (x₁ i) N k p a (x i) hk.le (ice i)) univ)‖≤ pound C b m z j k (raid C I E j) f:=by
    let f'(i):=C.O N p (x₁ i) ((y i) N)+ GridApprox.backTo P N p hk.le (betaDrop C (d i) k N p a (x₁ i) ((y i) k) (ice i)); have hF:f'= F':=by unfold f' writeF; unfold Function.comp; simp_rw [there,vect C k p N _ hk.le]
    have hb:=(A').tall.down (C:=C) (A').scroll.le (le_refl _); have hγ:= (A').next; have hx:= (A').scroll.trans hγ; have hQ (a b:V × I)(h:a≠b): (C.path.levels.budget k).B^8 ≤ separation ((U' k) a) ((U' k) b) :=by
       apply corners i₀ he A.tower hb hγ.le le_rfl _ a b h; intro i j hij; unfold Function.comp; rw [there,there]; exact (A').paid.trans (he.apart i j hij)
    let α i:= omen C (d i) k a; obtain ⟨α₀,hα,hh'⟩:= Finset.exists_max_image Finset.univ α ⟨i₀,Finset.mem_univ _⟩
    have hf':= flaredMixed H T₀ (covers_band i₀ he A.tower hb hf (living A') ((A').price) hγ.le) ((A').tall.hbar.trans hx.le) hk ((A').notch.trans hx) (fun i=>(A.every i).rank) (Habitat i₀ he A.tower hb hf (hγ.le.trans hk.le)) (fun a i hi _=> begins (x:=x) (A') hi a) hv hw hh f a ice hL (α α₀) (fun i=>hh' i (Finset.mem_univ i)) (fun i j he=> (A.every α₀).gain.trans_le (hQ i j he)) (by
       refine Loom.buys (p:=Loom.count C t k) (fun _ _ a _ b _ h=> ?_) (C.path.levels.budget k|>.B_pos) (Loom.count_pos ht) (fun i=>hL i.snd) (fun i=>mul_pos ((H.brine k).water k le_rfl |>.2) (mul_pos ((H.brine k).water k le_rfl |>.1) (hw i.snd))) (fun i=>hm i.snd)
       simpa only [Loom.stride,Nat.add_sub_cancel] using (A').stride.trans (hQ a b h)) hD
    have hS:= shoring (w:=f) H i₀ (covers_band i₀ he A.tower hb hf (living A') (A').price (le_refl j)) b (Habitat_root (p:=p) A' (letI : Nonempty I:=⟨i₀⟩; Fintype.card_pos.trans_le hf)) (A').notch (A').scroll (A').next (A').tall.hbar hk.le (funext (Annular.loops0 i₀ he)) (show Shown C N p m k f' _ _ from hf') hf (investments i₀ he (living A') (A').fine (A').price ((A').tall.hbar.trans (A').scroll.le) hE); rw [hF] at hS
    exact le_trans (atone _ _ (seamless H.seed ..) (Interior.combines _ _ (fun i _=> canopy H i₀ he A hk x₁ ice i))) hS
end YM.GapsR2RG
