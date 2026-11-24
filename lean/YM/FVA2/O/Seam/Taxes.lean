import YM.FVA2.O.Clift.Turns
import YM.FVA2.O.Pantry.Main
/-!
# Norm prices in two-scale geometry (`Home α I`, `Grass` for restricting the times)

`Tiny`: suppressed to every power of exp(t-θ), the small ratio below the upper
scale. `Tame`: allowing growth as a power of its inverse. *Rough* norms, not
charging differentiated kernels. Constants uniform over the α-space of sample
points (in applications, includes the index i and logarithmic scale).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Seam
open MS Function Filter Set Finset MS.Latch Job MS.Plane MeasureTheory Real Metric
open Heat LogTime IntervalFamily Koszul Tone Momentum Landau Fiddle Osc Snap Wire Signal
open Lives MS.City MS.Rake Tune Flux Book Convolve Serve O.Pad Vane High Detect
open MS.Local.Physical MS.Land O.Hue Rough O.Cool O.Clift Rake.Geo
open scoped Topology ContDiff Interval
variable { α E F I J : Type } { G:Gauge } { S:Home α I }{ t :α→ℝ } { P:Geo I } {η:I→ℝ}
variable {F H:Glade G I}{q v z:ℤ}{n m:ℕ}{x y:α→ℝ}
def Grass ( S:Home α I )( P:Geo I ): Prop:=∀ i,S.t i ≤ P.θ ( S.pick i )
def tar ( S:Home α I )( P:Geo I )( q:ℤ ): α→ℝ:= fun i=> exp ( ( q:ℝ )*( S.t i-P.θ ( S.pick i ) ) )
lemma tar_nn : nn (tar S P q):= fun _=> ( exp_pos _ ).le
lemma tar_zero : tar S P 0=1:= by ext i; simp [tar]
lemma tar_step (hp:Grass S P)(h:v≤q) : ∀ i, tar S P q i≤ tar S P v i:= fun i=> exp_le_exp.mpr ( mul_le_mul_of_nonpos_right (Int.cast_le.mpr h) (sub_nonpos.mpr (hp i)) )
lemma TarLow (hp: q≤0): ∀ i, S.length i ^ q ≤ tar S P q i:= by
    intro i; unfold tar; rw [ ← S.slot i, ← Real.rpow_intCast, ← Real.exp_mul ]; refine exp_le_exp.mpr ?_; rw [mul_sub,mul_comm _ ( S.t i )]; nlinarith [ show (q:ℝ)≤ 0 from by exact_mod_cast hp, P.room (S.pick i)]
lemma tar_mul (P:Geo I)(S:Home α I)(p q:ℤ) : tar S P (p+q)= tar S P p * tar S P q:= by ext i; simp [tar,add_mul,Real.exp_add]
lemma tar_grade (u:ℕ)(i:α) : tar S P (u:ℤ) i=( S.length i / roots P ( S.pick i ) )^u := by simp [tar, roots, ← S.slot i, ← Real.exp_sub,Real.exp_nat_mul]
-- whole-rank rough accounts (Costs are Rough.Size)
abbrev Pays (S:Home α I)(P:Geo I)(F: Glade G I)(q:ℤ): Prop:= totalT S F (tar S P q) false
abbrev Tame (S:Home α I)(P:Geo I) (F:Glade G I): Prop:= ∃ q,Pays S P F q
abbrev Tiny (S:Home α I)(P: Geo I)(F:Glade G I): Prop:= ∀ q:ℤ,Pays S P F q
lemma Tax_product (h:totalT S F x false)(he:totalT S H y false) : totalT S (joint G I F H) (x*y) false:= FormP.product h he
namespace Pays
lemma jointM (h:Pays S P F q)(hp:Pays S P H v) : Pays S P (joint G I F H) (q+v):= by rw [Pays,tar_mul]; exact Tax_product h hp
lemma size (h:Pays S P F q)(he:Grass S P)(hp:v≤q): Pays S P F v:= FormP.stays h (tar_step he hp)
lemma plus (h:Pays S P F q)(he:Pays S P H q): Pays S P (F+H) q:= FormP.plus h he
lemma minus (h:Pays S P F q)(he:Pays S P H q): Pays S P (F-H) q:= FormP.minus h he
end Pays
lemma Tiny.tame (h:Tiny S P F): Tame S P F:= ⟨0,h 0⟩
lemma Tiny.spec (h:∀ q:ℕ,Pays S P F q)(he:Grass S P): Tiny S P F:= fun i=> Pays.size ( h i.toNat ) he ( by omega )
lemma ThinAt : Tiny S P (0:Glade G I):= fun _=> FormP.unit tar_nn
lemma Tiny.add (h:Tiny S P F)(he:Tiny S P H): Tiny S P (F+H):= fun q=> Pays.plus (h q) (he q)
lemma Tiny.sub (h:Tiny S P F)(he:Tiny S P H): Tiny S P (F-H):= fun q=> Pays.minus (h q) (he q)
lemma Tame.unit : Tame S P (0:Glade G I):= ThinAt.tame
lemma Tiny.sum (s:Finset J){F:J→ Glade G I}(h:∀ i∈s,Tiny S P (F i)): Tiny S P (∑ i∈s,F i):= fun _=> at_sums _ (fun i hi=> h i hi _) tar_nn
lemma Tiny.tie (h:Tiny S P F)(he:Tame S P H): Tiny S P (joint G I F H) := by obtain ⟨q,hq⟩:= he; exact fun i=>( sub_add_cancel i q ) ▸ Pays.jointM ( h (i-q) ) hq
lemma Tiny.tier (h:Tame S P F)(he:Tiny S P H): Tiny S P (joint G I F H) := by obtain ⟨q,hq⟩:= h; exact fun i=>( show q+(i-q)=i from add_sub_cancel .. ) ▸ Pays.jointM hq ( he (i-q) ) -- lemma?
lemma Tame.add (hp:Grass S P)(h:Tame S P F)(he:Tame S P H): Tame S P ( F+H ):= by obtain ⟨q,h⟩:=h; obtain ⟨r,ht⟩:=he; exact ⟨ min q r,Pays.plus (Pays.size h hp (min_le_left ..)) (Pays.size ht hp (min_le_right ..))⟩
lemma Tame.sum (hv:Grass S P)(s:Finset J){F:J→ Glade G I}(h:∀ i∈s,Tame S P (F i)): Tame S P (∑ i∈s,F i):= by classical induction s using Finset.induction_on with | empty=> rw [ Finset.sum_empty ]; exact Tame.unit | insert i s hi ih=> rw [ Finset.sum_insert hi ]; exact Tame.add hv (h _ (by simp)) (ih fun j hj=>h j (mem_insert_of_mem hj))
lemma Tame.amalg (h:Tame S P F)(he:Tame S P H): Tame S P (joint G I F H):= by obtain ⟨q,hq⟩:=h; obtain ⟨v,hv⟩:=he; exact ⟨_,Pays.jointM hq hv⟩
-- T natural powers
abbrev Calm (S: Home α I)(P:Geo I)(X:T ( Glade G I )):= ∀ i,Tame S P ( X i )
abbrev Chaff (S: Home α I)(P:Geo I)(X:T ( Glade G I )):= ∀ i,Tiny S P ( X i )
variable { Y X:T (Glade G I)}
lemma Calm.bonds (he:Grass S P)(hp:Calm S P X)(ht:Calm S P Y): Calm S P (bond G I X Y) := fun n=> Tame.sum he (antidiagonal n) (fun _ _=> Tame.amalg (hp _) (ht _) )
namespace Chaff
lemma zeros : Chaff S P (0:T ( Glade G I )):= fun _=> ThinAt
lemma add (h:Chaff S P X)(ht:Chaff S P Y): Chaff S P (X+Y):= fun i=> Tiny.add (h i) (ht i)
lemma minus (h:Chaff S P X)(hp:Chaff S P Y): Chaff S P (X-Y):= fun i=> Tiny.sub (h i) (hp i)
lemma neg (h:Chaff S P X): Chaff S P (-X):= by simpa only [zero_sub] using minus zeros h
lemma sums (s:Finset J){X:J→ T ( Glade G I )}(h:∀ i∈s,Chaff S P (X i)): Chaff S P (∑ i∈s,X i):= by intro i; rw [ Finset.sum_apply ]; exact Tiny.sum _ (fun j hj=> h j hj i)
lemma badges (h:Chaff S P X)(he:Calm S P Y): Chaff S P (bond G I X Y):= fun n=> Tiny.sum (antidiagonal n) (fun _ _=> Tiny.tie ( h _ ) (he _) )
lemma pass (h:Calm S P X)(he:Chaff S P Y): Chaff S P (bond G I X Y):= fun n=> Tiny.sum (antidiagonal n) (fun _ _=> Tiny.tier ( h _ ) (he _) )
end Chaff
lemma bond_le {k:ℕ}(h:∀ i<k,totalT S ( X i ) x false)(he:∀ i<k,totalT S ( Y i ) y false)(hx:nn x)(hy:nn y)(hp:m<k): totalT S (bond G I X Y m) (x*y) false:= by apply at_sums (antidiagonal m) _ ( joy hx hy ); intro i hi; have hT:= mem_antidiagonal.mp hi; exact Tax_product ( h i.1 (by omega)) (he i.2 (by omega))
end YM.FVA2.O.Seam
