import YM.OPE.Yarn.Broker
/-!
# Record promotions, consume every finite event
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Yarn
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
-- guard
abbrev Pod:= Option ℕ
def pocket (C:Family G)(u:Pod)(k:ℕ)(t w:ℝ):= Option.elim u (t*w) (fun i=>stair (near C.path.levels) w i k)
-- base W lim; at reducible (lane) `t` factor
structure CrewBook (C:Family G) (N p j k:ℕ)(D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)) (hk:j≤k)(hn:k ≤ N)(F:I→ Config G (C.side N p)→ℂ)(d:Finset I)(o:I→∀ i:ℕ,Site (C.side i p))(u:I→Pod)(w:I→ℝ)(S:I→∀ i:ℕ,Lamp G (C.side i p))(X:I→Lamp G (C.side k p)):Prop where
    ready:∃ Q, Wagon C N p j k hk hn Q F d (fun i=>o i k) X (fun i=>pocket C (u i) k 1 (w i))
    serves i : 0<w i
    issued i n: u i=some n → X i=S i k ∧ Drive C.path n k N p (o i) (stair (near C.path.levels) (w i) n) D (S i) hn
    rest i : u i=none → (X i).Flex (C.path.rep N p k) (o i k) (4*(1/w i))
namespace Tune
variable {a:Pod} {v w t:ℝ}
include H
lemma pokes (i:ℕ)(hp:0<v)(hz:0<w) : 0<pocket C a i v w:=by cases a; exact mul_pos hp hz; exact H.protectors _ hz ..
lemma pokes_le (hv:0<v)(hw:t ≤ w): pocket C a i v t ≤ pocket C a i v w:=by
   cases a; exact mul_le_mul_of_nonneg_left hw hv.le
   next a=> change stair η _ _ _≤ stair η _ _ _; rw [stair_eq _ t,stair_eq _ w]; exact mul_le_mul_of_nonneg_right hw (H.protectors _ zero_lt_one a i|>.le)
lemma gate (hp:v≤1) (hw:0<w): pocket C a i v w≤pocket C a i 1 w := Function.const _ (by cases a; exact mul_le_mul_of_nonneg_right hp hw.le; exact le_rfl) H
lemma returning (hp:∀ n,a=some n→ n ≤ i) (hv:0<v)(hw:0<w): η i*pocket C a i v w ≤ pocket C a (i+1) v w:=by
   cases a; exact mul_le_of_le_one_left (mul_pos hv hw|>.le) ((inv_le_one₀ (zero_lt_one.trans ((T).fits.delayed (i+1)))).mpr ((T).fits.delayed _|>.le))
   next a=> exact (H.fall_march (a:=w) (hp _ rfl)).symm.le
end Tune
-- structural requires.License_to_w
variable {F:I→ Config G (C.side N p)→ℂ}{o:I→ ∀ i:ℕ, Site (C.side i p)}{w:I→ℝ}{u:I→Pod}{v:J→Pod} {d₀:Finset I}{Y:I→∀ i:ℕ,Lamp G (C.side i p)} {X:I→ Lamp G (C.side k p)} (long:Bool)
    {hm:m≤j} (ht:j < k) (hk:C.ref 0 < j) {hn:k≤N}
structure Event (L:Fibers I J) (C:Family G)(o:I→∀ i:ℕ,Site (C.side i p))(r:ℕ→ℕ)(j k m l:ℕ)(long:Bool)(u:I→Pod)(v:J→Pod) : Prop where
    clock : Band C o r j k m
    aligns (i:I) : long=true → u i=none → ∀ b:ℕ,j ≤ b → b<k → o i (b+1)= (C.path.levels.clock.op b p).ratio.embed (o i b)
    floor (i:I)(n:ℕ): u i=some n→ n ≤ j
    collar (i:J)(n:ℕ): v i=some n→ L.Only i ∧ u (L.twig i)=some n
    finishes (i:I)(n:ℕ): u i=some n→ v (L.bunch i)=none → n=j
    price (i:Site (C.side m p) × I): let x' := (royal C m p j).place (fun l=>o l j); coverNumber (C.path.levels.budget j).B ({x' (i.1,L.twig (L.bunch i.2)), x' i}:Support _) ≤ l
variable (b:ℕ) (L:Fibers I J) (E: Event L C o r j k m l long u v)
def promotion (C:Family G)(u:I→Pod)(v:J→Pod)(w:I→ℝ)(j k b l:ℕ)(long:Bool)(L:Fibers I J)(x:J):ℝ:=if v x=none then grouped C.path (renal C.path.levels) b l j (fun i=> pocket C (u i) (j+1) (fee C j k long) (w i)) L x else license C.path (renal C.path.levels) b l j * near C.path.levels j*w (L.twig x)
local notation "f*"=> fee C j k long
local notation "w!"=> fun (i':I)(l:ℕ)=> pocket C (u i') l (fee C j k long) (w i')
local notation "x*"=> promotion C u v w j k b l long L
local notation "L'"=> license C.path δ b l j
include H E ht
lemma Event.invoice (i:I)(hp:0<w i)(hF:v (L.bunch i)=none) : w! i (j+1)=(if u i=none then fee C j k long else η j)* w i:=Function.const _ (by
    cases h:u i with
    | none=> simp [pocket,h,Option.elim]
    | some n=> obtain rfl : n=j:= E.finishes i n h hF; simp [pocket,h,Option.elim]; rw [H.fall_march (a:=w i) (le_refl _),H.anchor_march hp]) (‹DecidableEq I›, ‹Fintype J›)
include hk
lemma Event.earns (hF:0<b)(hw:∀ i,0<w i) (x:J) : 0<x* x ∧ pocket C (v x) j 1 (x* x)=grouped C.path δ b l j (fun i=> w! i (j+1)) L x:=by
    by_cases he: v x=none
    · unfold promotion; rw [if_pos he,he]; refine ⟨grouped_pos b l L (H.mantle hk.le).funs.1 hF (fun i=> H.pokes _ (voucher H ht long|>.1) (hw i)) x, one_mul _⟩
    obtain ⟨s,hs⟩:=Option.ne_none_iff_exists'.mp he -- check
    let i:=L.twig x; have hb:= (E.collar x s hs); let X':=L'; have hx:0< X':= license_pos b l (H.mantle hk.le).funs.1 hF; have hη:0<η j:= (H.brine j).water _ le_rfl|>.1
    unfold promotion; rw [if_neg he, hs]; refine ⟨mul_pos (mul_pos hx hη) (hw i),?_⟩; unfold grouped; rw [show L.contents x={i} from hb.1, Finset.prod_singleton]; dsimp only; rw [show u i= _ from hb.2]; change stair η (X'*_*_) s j=X'* stair η (w i) s (j+1); rw [H.fall_march (E.floor i s hb.2), stair_eq η (X'*_*_),stair_eq η (w i)]; ring
variable (hz:0<b)(hb:Fintype.card I≤b)(hr:CrewBook C N p m k D (hm.trans ht.le) hn F d₀ o u w Y X)
include hz hb hr hk
set_option maxHeartbeats 200000 in
lemma Event.finish : ∃ X', CrewBook C N p m j D hm (ht.le.trans hn) (fun i=>fineJob F (L.contents i)) (d₀.image L.bunch) (o ∘ L.twig) v (x*) (Y ∘ L.twig) X':=by
    obtain ⟨Q,hQ⟩:= hr.ready; have hη := (H.brine j).water _ le_rfl|>.1; have hx(i k): 0 < w! i k:= H.pokes k (voucher H ht long|>.1) (hr.serves i)
    have hU(i:I):∃ S, S k=X i ∧ Drive C.path j k N p (o i) (w! i) D S hn ∧ (u i≠none → S=Y i):= by
        cases hh:u i
        case none=>
           obtain ⟨S,hK,hS⟩:= ripe H (o i) (fun j hj hk=> E.clock.clock j hj hk i) ht hk.le hn (hr.serves i) (hr.rest i hh) long (fun h=> E.aligns i h hh); refine ⟨S,hK,?_ ,fun h=>False.elim (h rfl)⟩; simp_rw [hh,pocket,Option.elim]; exact hS
        case some n=>
           obtain ⟨hT,hP⟩:=hr.issued i n hh; refine ⟨Y i,hT.symm, ?_,fun _=>rfl⟩; simp_rw [hh,pocket,Option.elim]; exact ⟨fun j hj=> hP.drives j ((E.floor i _ hh).trans hj)⟩
    choose S hS hA hC using hU
    have he' := fun x=> E.earns H long ht hk b L hz hr.serves x -- binder check
    obtain ⟨P',hT,hM,hh⟩:= crux (w:=w!) (Y:=S) H E.clock hm hk ht hn (by simp_rw [hS]; exact hQ.shorten (fun i=>hx i k) (fun i=> H.gate (voucher H ht long|>.2) (hr.serves i))) hA (fun a i _ _=>hx a i) (fun i hi hk a=> H.returning (fun n h=> (E.floor a n h).trans hi.le) (voucher H ht long|>.1) (hr.serves a)) b L (fun i=>v i ≠ none) hz hb (fun i h=> by obtain ⟨s,hs⟩:=Option.ne_none_iff_exists'.mp h; exact (E.collar i s hs).1) E.price -- pass Q explicit metavars
    refine ⟨P',⟨⟨(fun U=>Fibers.reap (partialGroup V L) (gust C.path N p k Q j ht.le U)),?_⟩,fun x=>(he' x).1,?_, fun i h=>?_⟩⟩
    · convert! hh using 1; exact funext fun x=>(he' x).2
    · intro x s hs; let i:= L.twig x; have hp:= E.collar x s hs; have he:v x ≠ none:=by simp only [hs,ne_eq,reduceCtorEq,not_false_eq_true]
      refine ⟨(hT _ he).trans (congr_fun (hC (L.twig x) (by simp [hp.2])) j),?_⟩; have hD: Drive P s j N p (o i) (stair η (w i) s) D (Y i) (ht.le.trans hn):=⟨fun n hh he=> (hr.issued i s hp.2|>.2).drives n hh (he.trans ht)⟩
      apply Drive_on hD _ (fun v _ _=> H.protectors _ (he' _|>.1) ..); intro n _ _; refine H.pokes_le (a:=some s) (i:=n) (v:=1) zero_lt_one ?_; unfold promotion; rw [if_neg he]
      have hδ:= (H.mantle hk.le).funs; have hL: L'≤1:= (unit_license b l (H.mantle hk.le) hz (T|>.budget j |>.exponent_pos.le)).trans hδ.2
      exact mul_le_of_le_one_left (hr.serves i|>.le) (mul_le_one₀ hL hη.le ((inv_le_one₀ (zero_lt_one.trans ((T).fits.delayed (j+1)))).2 ((T).fits.delayed _|>.le)))
    · change Blade ..; rw [promotion,if_pos h]; exact hM i (not_not_intro h)
end YM.OPE.Yarn

