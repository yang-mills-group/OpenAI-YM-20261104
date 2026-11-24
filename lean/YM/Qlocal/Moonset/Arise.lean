import YM.Qlocal.Moonset.Triangle
import YM.Qlocal.Dialect.Knolls
/-!
# The analytic layout through the coupling-coordinate reporting change

An actual data transformer; leaves paths in place and their masks/predicates useable even
on the weighted norm. Padded family interface and approximate requisite ledger on model stencils.
Marker costs/iteration and wind billing handled at the client. The transformer does not choose the
input credential: those have to be obtained for each step and period on the same pose.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Moonset
open Function Filter Wilson Lattice RG Gauge Push.AbsoluteSums Finset Marker
open AllOrder AllOrder.Floe AllOrder.Floe.Pace
open Quipu Quipu.Sonnet Quipu.Sonnet.Tern Quipu.Eluder
open scoped Topology BigOperators Classical ContDiff
variable {V:Type} [Fintype V][DecidableEq V] {R:Marker.Census V} {G:Gauge}
variable {g:V→ℕ}{p N i k L:ℕ}{Y : Stanza R G g p}
variable {t a C : ℝ}
open Dialect
-- `book`: pads for rank & order. No Σ casts in consumer API.
noncomputable def book (Y : Stanza R G g p)(s:Senses R)(i k:ℕ) : Album ℕ s G k :=
  if h : i ≤ p ∧ k ≤ i+Lagger.dues g s.val then Y s ⟨i,Nat.lt_succ_of_le h.1⟩ ⟨k,Nat.lt_succ_of_le h.2⟩ else fun _=> Vase.vac s G k
abbrev Accept (s:Senses R)(i k:ℕ) := k ≤ i+Lagger.dues g s.val
set_option quotPrecheck false
variable (Y) (s:Senses R)
local notation "C'" => Lagger.dues g s.val
omit [Fintype V] in
lemma bookmark (e:Fin (p+1))(r:Fin (e.val+Lagger.dues g s.val+1)) : book Y s e.val r.val= Y s e r:= dif_pos (show e.val ≤ p ∧ r.val ≤ _ from by omega)
lemma padded_pay (B:ℝ)(hp: (Stanza.son Y N).Allows a B) (s:Senses R)(i k:ℕ) : Album.Health (book Y s i k) a B := by
  have ho: 0 ≤ B:= budget_nonneg (hp.pay s 0 0)
  unfold book; split; next h=> exact hp.pay s _ _
  unfold Album.Health; simp only [Vase.fare, Ballad.silent s, zero_mul]; exact budget_of_sum (fun _=> le_rfl) (by intro i; simpa using ho)

/-- `X e k j`: coefficients by which this original (e,k)-entry appears as `(e+j,k)` -/
abbrev Ladder := ℕ→ℕ→ℕ→ℝ
variable (X : Ladder)
noncomputable def stencil (Y: Stanza R G g p) : Stanza R G g p :=
  fun s e k=> Stack.crowd (J:=Fin (e.val+1)) (fun j=> book Y s j.val k.val) (fun j=> X j.val k.val (e.val-j.val))
-- there is no charge for fictitious silent rank/order pads
local notation "Y*" => stencil X Y
local notation "Lℓ" => Lagger.dues g
-- Price without request s.Version sum upper
noncomputable abbrev price_ops (p : ℕ)(k : ℕ) (B:ℝ) : ℝ:= ∑ v∈range (p+1),∑ i∈range (v+1),∑ j∈range (k+1),|X i j (v-i)| * B
lemma nonneg_price (h : 0 ≤ C) (p k:ℕ): 0 ≤ price_ops X p k C:= by unfold price_ops; positivity
lemma age_price (e:Fin (p+1))(r:Fin (e.val+Lagger.dues g s.val+1))(B:ℝ)(hp:(Stanza.son Y N).Allows a B)(H:ℕ)(hk:r.val ≤  H) : Album.Health ((Y*) s e r) a (price_ops X p H B) := by
  have h := Stack.assembled (J:=Fin (e.val+1)) (fun j=>book Y s j.val r.val) (fun j=> X j.val r.val (e.val-j.val)) (fun i=> padded_pay Y B hp s _ _)
  apply budget_loosen h
  have hc:0 ≤ B:= budget_nonneg (hp.pay s 0 0)
  let Z v i:= ∑ j∈range (H+1),|X i j (v-i)| * B
  apply (le_trans ?_ (Finset.single_le_sum (f:=fun v=> ∑ i∈range (v+1), Z v i) (fun v _=> sum_nonneg fun i _=> sum_nonneg fun j _=> by positivity) (Finset.mem_range.mpr e.isLt)))
  rw [Fin.sum_univ_eq_sum_range (fun i=> |X i r.val (e.val-i)| * B)]
  exact Finset.sum_le_sum fun j hj=> Finset.single_le_sum (f:=fun i=> |X j i (e.val-j)| * B) (fun i _=> by positivity) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
-- furnish shape for all s with one rent horizon
lemma retain_price (L:ℕ)(B:ℝ)(h:∀ s:Senses R, Lagger.dues g (s:Senses R).val ≤ L)(hp:(Stanza.son Y N).Allows a B) :
  (Stanza.son (stencil X Y) N).Allows a (price_ops X p (p+L) B):= by
    constructor; intro i k r; let m:= (i:Senses R); exact age_price Y i X k r B hp (p+L) ((Nat.le_of_lt_succ r.isLt).trans (Nat.add_le_add (show k.val ≤ p from Nat.le_of_lt_succ k.isLt) (h i)))

-- exact rendering identities
variable {n:Side}(o:V→Site n)(Z:ℕ→ Prop)(x:Config G n) (N:ℕ)
noncomputable def draw (Y : Stanza R G g p) (s:Senses R)(i k : ℕ) (Z:ℕ→ Prop) (o: V→Site n) (N : ℕ) :=
  Album.picture (Stack.history Z (book Y s i k)) (book Y s i k) o N
local notation "T" => Stanza.son Y N
local notation "D" => Stack.selector (T) Z
lemma below (hx:¬(i ≤ p∧Accept (g:=g) s i k)) : draw Y s i k Z o N=0:= by
  unfold draw; rw [book,dif_neg hx]
  ext U; unfold Album.picture Album.realize; change _=(0:ℝ); refine Eq.trans (tsum_congr (g:=fun _=>0) ?_) tsum_zero
  intro i; unfold Album.readout; split; next h=> rw [Ballad.blind s _]
  rfl
lemma treaty (e:Fin (p+1))(r: Fin (e.val+Lagger.dues g s.val+1)) : draw Y s e.val r.val Z o N=(T).playing (D) o s e r:= by
  unfold draw; rw [bookmark]; rfl
lemma retention (i k : ℕ)(hi:i ≤ p)(hp:(Stanza.son Y N).Allows a C) (ha:0<a) : draw (stencil X Y) s i k Z o N x=∑ j∈range (i+1), X j k (i-j) * draw Y s j k Z o N x := by
  by_cases he:k ≤ i+C'
  · let e:Fin (p+1):=⟨i,by omega⟩; let w: Fin (e.val+Lagger.dues g s.val+1):= ⟨k,by change k < i+C'+1; omega⟩
    rw [← Fin.sum_univ_eq_sum_range]; change draw (stencil X Y) s e.val w.val Z o N x= _; unfold draw; rw [bookmark]; exact Stack.tenure (fun t : Fin (i+1)=> book Y s t.val k) (fun t:Fin (i+1)=> X t.val k (i-t.val)) (fun t=>padded_pay Y C hp s _ _) Z o x ha N
  rw [below (stencil X Y) s o Z N (hx:= fun q=>he q.2)]; refine Eq.symm (Finset.sum_eq_zero fun j hj=>?_); rw [below Y s o Z N (hx:= fun q=>?_ )]; simp only [Pi.zero_apply,mul_zero];
  exact he (q.2.trans (Nat.add_le_add_right (Nat.le_of_lt_succ (mem_range.mp hj)) _))

-- exact identification between stencil realization and pre-model realization:
-- use after forward model projection in the layout (without giving B heights another physical mask)
local notation "U" => AllOrder.Floe.Pace.Coin
noncomputable def toParent (q:Coin)(Y : Stanza R G g p):= stencil (raise q) Y
noncomputable def toChild (q:Coin)(Y : Stanza R G g p):= stencil (Moonset.forward q) Y -- the book remains on the parent fields, in child coupling
variable (q:Coin) (q₀:q 0=0)
set_option quotPrecheck false
local notation "V₁" => toParent q Y
local notation "V₂" => toChild q (V₁)
include q₀
-- Proof for all padded slots
lemma recovers (e k:ℕ)(hp:e ≤ p)(hP:(Stanza.son Y N).Allows a C)(ha:0<a) : draw (toChild q (toParent q Y)) s e k Z o N x= draw Y s e k Z o N x:= by
  let B:=∑ v:Senses R,Lagger.dues g v.val
  have h (v:Senses R): Lagger.dues g v.val ≤ B:= Finset.single_le_sum (f:=fun v:Senses R=>Lagger.dues g v.val) (fun i _=> Nat.zero_le _) (mem_univ v)
  rw [toChild,retention (V₁) s _ o Z x N e k hp (retain_price Y _ B C h hP) ha]
  change ∑ j∈range (e+1), forward q j k (e-j) * _=_
  let f i:= draw Y s i k Z o N x
  let G v j:= (raise q v k (j-v)*forward q j k (e-j))* f v
  have he (j:ℕ)(hj:j ≤ e) : forward q j k (e-j) * draw (toParent q Y) s j k Z o N x=∑ v∈range (e+1), if v ≤ j then G v j else 0:= by
    unfold toParent; rw [retention Y s _ o Z x N j k (hj.trans hp) hP ha, mul_sum, ←Finset.sum_filter, show ((range (e+1)).filter (fun v=>v ≤ j))=range (j+1) from (by ext; simp only [mem_filter, mem_range]; omega)]; exact Finset.sum_congr rfl fun v _=> by unfold G f; ring
  apply Eq.trans (Finset.sum_congr rfl fun j hj=>he j (Nat.le_of_lt_succ (mem_range.mp hj)))
  have hr (v:ℕ)(hv:v ≤ e) : (∑ j∈range (e+1), if v ≤ j then G v j else 0)=if v=e then f v else 0:= by
    rw [← Finset.sum_filter, show ((range (e+1)).filter (fun j=>v ≤ j))= Finset.Icc v e from (by ext; simp only [mem_filter,mem_range,Finset.mem_Icc]; omega)]
    unfold G; rw [← Finset.sum_mul,raised_from q q₀ v k e hv]; split_ifs <;> simp only [one_mul,zero_mul] <;> omega
  rw [Finset.sum_comm]
  exact Eq.trans (Finset.sum_congr rfl fun v hv=> hr v (Nat.le_of_lt_succ (mem_range.mp hv))) (by simp [f])
-- note no claim labels equal/identical f_n state (actual projection at old pose still needs exact K compatibility)
end YM.Qlocal.Moonset
