import YM.FVA2.O.Seam.Timber
/-!
# Bounding the cross operations between inputs at large separation

Use stronger prices (`Lend`) on the respective inputs **without** the shifts,
obtain rough estimates after the operation with the shifts applied. `ShareV`/`TouchV`,
can include odd second input, needed e.g. when passing `nav` through the product.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Seam
open MS Function Filter Set Finset MS.Latch Job MS.Plane MeasureTheory Real Metric
open Heat LogTime IntervalFamily Koszul Tone Momentum Landau Fiddle Osc Snap Wire Signal
open Lives MS.City MS.Rake Tune Flux Book Convolve Serve O.Pad Vane High Detect
open MS.Local.Physical MS.Land O.Hue Rough O.Cool O.Clift Rake.Geo O.Price O.Fuse O.Ward
open scoped Topology ContDiff Interval
variable { G: Gauge } {I W α : Type} { a b p : I→ QP } { S:Home α I } {P:Geo I}{Y X:T ( Glade G I )} {F H:Glade G I}{k c v z:ℤ}
variable {B:Deck G}{K: Booked B}{M:MS_Data G K}{n:ℕ}{u r:Label B}{x y:α→ℝ}{L:Planet G I}{t:Bool}
abbrev Lend (S:Home α I)(P: Geo I)(F:Glade G I):= ∃ q:ℤ,Latch.Lease false false S.toScale ( sendT S F ) (tar S P q)
lemma Earn (hp:Lend S P F): Tame S P F:= by obtain ⟨q,h⟩:=hp; exact ⟨ _,from_cost h ⟩
lemma Lend.heart (hp:liveP S P.η): Lend S P ( rowM P M u n ):= ⟨ -(u.h:ℤ),Latch.Lease.sticks (priceField hp) ( TarLow ( q:=-(u.h:ℤ) ) (by omega) )⟩
lemma Covers (he:Grass S P)(h:CoverSep P p)(hp:Lend S P F)(hr:Lend S P H)(hy:Sheet S.toScale x ( sendT S L ))(hv:nn x)(ht:∀ i, x i≤ tar S P v i): Tiny S P ( regionC (fun _=>planeF) p L F H ):= by
    obtain ⟨q,hq⟩:= hp; obtain ⟨u,hu⟩:= hr; obtain ⟨⟨D,hD,H⟩,T,hT,hA⟩:=h; let V := roots P ∘ S.pick; intro k; let r:= ( k-v-q-u ).toNat;
    obtain hh:= PulseQ (v:=V) (A:=p∘ S.pick) hy (Latch.Lease.highp hq) ( Latch.Lease.highp hu ) hv tar_nn tar_nn (fun _=> exp_pos _) (fun i=> hA ( S.pick i )) (fun i=>( S.slot i ).symm ▸ exp_le_exp.mpr ( he i )) ⟨ D,hD,0,fun i=> by rw [pow_zero,mul_one]; exact H ( S.pick i )⟩ hT r;
    refine FormP.stays ( from_cost hh ) (fun i=>?_); refine le_trans ?_ ( tar_step he ( show k≤ v+(q+u)+r from (by unfold r; omega)) i ); rw [tar_mul P S (v+(q+u)),tar_mul P S v,tar_mul P S q]; dsimp only [ Pi.mul_apply,V,Function.comp_apply ]; rw [ ← tar_grade ( S:=S ) ( P:=P ) r i ]; -- V
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (ht i) ( mul_nonneg ( tar_nn i ) (tar_nn i))) (tar_nn i)
local notation "Λ"=> (fun _ : I=> lineA G)
local notation "Ω"=> (fun _ : I=> lineB G)
variable (he:Grass S P)
include he
lemma Cross_a (ht: CoverSep P ( a-b ))(h:Bank F 0)(hv:Bank H v)(hp:Lend S P F)(hx:Lend S P H): Tiny S P (voyage Λ false ( tilt G a F ) ( tilt G b H )):= by rw [ attach h hv ]; exact fun i=> FormP.chair _ ( Covers he ht hp hx ( capeA S G ) (fun _=>zero_le_one) ( v:=0 ) (fun i=>by rw [tar_zero]; rfl) i )
lemma Cross_b (ht:CoverSep P ( a-b ))(h:Bank F 0)(hv:Bank H v)(hp:Lend S P F)(hx:Lend S P H): Tiny S P (voyage Ω true ( tilt G a F ) ( tilt G b H )):= by
    rw [ Cool.hug h hv ]; refine fun i=> FormP.chair _ ( Covers he ht hp hx (capeB S G ) (true_nn S) ( v:=-1 ) ?_ i ); intro i; rw [ TrueT, ← zpow_neg_one ]; exact TarLow (by norm_num) i
lemma ShareV (h:CoverSep P (a-b))(hp:Banks X 0)(hv:Banks Y v)(ht:∀ i,Lend S P ( X i ))(hx:∀ i,Lend S P ( Y i )): Chaff S P ( Share G I ( swing G a X ) ( swing G b Y )):= fun k=> Tiny.sum (antidiagonal k) (fun i _=> Cross_a he h (hp i.1) (hv i.2) (ht _) ( hx _ ))
lemma TouchV (h:CoverSep P (a-b))(hp:Banks X 0)(hv:Banks Y v)(ht:∀ i,Lend S P ( X i ))(hx:∀ i,Lend S P ( Y i )): Chaff S P ( Touch G I ( swing G a X ) ( swing G b Y )) := fun k=> Tiny.sum (antidiagonal k) (fun i _=> Cross_b he h (hp i.1) (hv i.2) (ht _) (hx _))
variable (hp: liveP S P.η)(hv:CoverSep P ( a-b ))
include hp hv
lemma shareF : Chaff S P ( Share G I ( singletonM P M a u ) ( singletonM P M b r )):= ShareV he hv ( Response.visit u.item |>.life ) ( Response.visit r.item |>.life ) (fun _=> Lend.heart hp) (fun _=> Lend.heart hp)
lemma touchF : Chaff S P ( Touch G I ( singletonM P M a u ) ( singletonM P M b r )):= TouchV he hv ( Response.visit u.item|>.life ) ( Response.visit r.item|>.life ) (fun _=> Lend.heart hp) (fun _=> Lend.heart hp)
omit he hv hp in
lemma swing_co : swing G 0 X=X:= funext fun _=> dizzy
omit hv in
lemma ShareE (hx: CoverSep P a)(hy:Banks Y v)(hz: ∀ i,Lend S P ( Y i )): Chaff S P ( Share G I (singletonM P M a u) Y ) := by have h:= ShareV (X:=rowM P M u) he (by simpa only [sub_zero] using! hx : CoverSep P (a-0)) ( Response.visit u.item |>.life ) hy (fun _=> Lend.heart hp) hz; rw [swing_co] at h; exact h
omit hv in
lemma TouchE (hx: CoverSep P a)(hy:Banks Y v)(hz:∀ i,Lend S P ( Y i )): Chaff S P (Touch G I (singletonM P M a u) Y) := by have h:= TouchV (X:=rowM P M u) he (by simpa only [sub_zero] using hx : CoverSep P (a-0)) ( Response.visit u.item|>.life ) hy (fun _=> Lend.heart hp) hz; rw [swing_co] at h; exact h
end YM.FVA2.O.Seam
