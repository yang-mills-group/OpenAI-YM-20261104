import YM.QuadraticLocal.Lamps
import YM.Integration.LocalComparisonInterface
import Mathlib.Analysis.Complex.ExponentialBounds
/-!
Export strong Gallery comparison budgets to LocalComparison. `Π` derivative order p and every
position/marker/test sup remain INSIDE each sum. The output K bills price WHOLE table on the
chosen vacuum, then reindex occurrencewise, don't weaken after evaluation. Can position global
captions in the unit stream later if separately needed; here pay on actual stencil through `Lamp`
and send to Captions. The passport isn't conditioned on disjointness/κ support cropping: one
Budget for the entire finite Census, including overlapping disjoint combinations permitted by it.

`Retains` in published `LocalComparison` has strictly stronger predicate demanding every
(`i`,`j`) forced support holds a real marker address EVEN on padding off. Since `i` already
ranges over a full vacuum family with arbitrarily far supports and every (`i`,`j`) tag MUST
contain at least one marker to obey `Overlay.Active`, no such claim is made. This file preserves
roots exactly on every declared (`Gallery`) label with a response. Larger address receipts kept
on actual supplied labels, not automatically HEADLINE all padding. This layout is an extension
with explicit packaging into the other relevant `LocalComparison` types retaining prices.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.QuadraticLocal.Display
open Function Filter Finset Lattice Wilson RG Ac Marker Overlay RG3 RG3.Held RG3.Forms Press
open Push.Corrected Push.AbsoluteSums MeasureTheory Extra.Trajectories Next.Foundations Push.Local
open RG3.Script.Picnic Integration.LocalComparison
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V:Type}[DecidableEq V][Nonempty V]{R:Census V}{G:Gauge}{n:Side} {T:Type*}[Nonempty T]
variable {ι:Type*}[Countable ι]{P:Rep G n}{o:V→Site n} {w:V→ℝ}{q b c κ:ℝ}
local notation "Q"=> pin (α:=ι)
variable (A:Gallery T ι o P R)

def article (t:T) : Press.Article ℕ P.p G R o:= ⟨P.activities.forced,A.K.hard t⟩
def focus (i:ι):Support n:= A.E.ground i
def val (i:ι) := A.E.mode i
def drawn (t:T) (i:ι): Config G n →ℂ:= if A.E.clear i then 0 else A.E.nominal t i
def nomad (t:T)(i:ι):ℂ:= if A.E.clear i then A.E.nominal t i 1 else 0
local notation "jv"=> R.fire (Classical.arbitrary V)
def view : View T V G n P R:= ⟨o,unpin (val A) jv,unpin (focus A) univ,fun _ _=>jv,0,fun t=>unpin (drawn A t) 0,0⟩
def taste : Taste T o P R where
  menu := (view A).impression (article A) id
  root := rfl
  tag := unpin (val A) jv
  site := unpin (focus A) univ
  score t:= unpin (nomad A t) 0

local notation "X"=> taste A
local notation "Y" => (view A)
-- packing identities don't retire a mask predicate, no dropping off-X K.
variable (t:T)(U:Config G n)

omit [Nonempty T] [Nonempty V] [Countable ι] in
lemma carried : (article A t).Hosting P id:= ⟨rfl,fun _=>rfl,fun _=>rfl,fun i U he=>(A.K.charged _ i U he).2⟩
omit [Nonempty V] [Nonempty T] [Countable ι] in
lemma soundArticle (h:P.activities.ForcedFamily P.p): (article A t).Sound:= ⟨A.K.locality t,A.K.charged t,fun i U=> by rw [show ( (article A t).flow i U).part R.quiet=_ from A.K.quiet t i U]; rfl,h.meas_test,h.symtest,h.reads_test⟩
lemma hostel (hw:∀ v,0<w v)(h:A.K.Paid w P.p.B P.p.supportExponent b) (i:ℕ) : ((X).leaf t).contents.each i U= A.K.hard t i U:=by
    let D:= article A t
    have hel (v) (hv:v ≠ (⟨i,rfl⟩ : { j // id j=i})): False := hv (Subtype.ext v.prop)
    have hB : D.Budget w b:=by obtain ⟨f,h,hF⟩:= h.wages; exact ⟨f,fun i U=> h i t U,hF⟩
    change (Press.Article.impression D ((view A).terms t) id).each i U=_
    have ht : D.broth id i U= ↑(P.activities.K i U):=by unfold Press.Article.broth; rw [tsum_eq_single (⟨i,rfl⟩ : {j // id j=i}) (fun _ h=> (hel _ h).elim)]; exact A.K.quiet t i U
    rw [D.identical _ id _ _ hw hB ht]; unfold Press.Article.stream; rw [tsum_eq_single (⟨i,rfl⟩ : {j // id j=i}) (fun _ h=> (hel _ h).elim)]; rfl
local notation "E₀"=> (taste A).leaf t
local notation "XA"=> (E₀).contents
local notation "CA"=> (E₀).captions
variable {A}

lemma logE (i:ι) : Bands.ray XA (pin i) U + (Poly.send ((CA).tag (pin i)) ((CA).value (pin i)))= A.E.frame i t U:=by
    unfold Bands.ray; change Poly.send (unpin _ jv (pin i)) (masked _ (unpin _ univ (pin i)) ((unpin (drawn A t) 0 (pin i))) U) + Poly.send (unpin _ jv (pin i)) (unpin _ 0 (pin i))= _
    rw [unpin_pin,unpin_pin,unpin_pin,unpin_pin]; unfold Lamps.frame Lamps.light drawn nomad focus Display.val; split
    next h=> rw [A.E.pure t i U h]; simp [masked]
    simp
-- Display budget and equality separately.
lemma vacR {i:ℕ} (h:i∉Set.range Q): Bands.ray XA i U=(0:Poly R) ∧
    Poly.send ((CA).tag i) ((CA).value i)=0:=by
    unfold Bands.ray; rw [show (XA).H i=0 from unpin_blank _ _ h, show (CA).value i=0 from unpin_blank _ _ h]; simp [masked]
-- summability log via normalized price, occurrence transport; need series across padding
variable (A)
variable [Fintype V]
set_option maxHeartbeats 200000 in
lemma tasteH (hw:∀ v,0<w v) (h:A.E.Paid w P.p.B P.p.supportExponent c): ((X).leaf t).log U= A.E.log t U:=by

    let D:= Q
    let a i:= Bands.ray XA i U; let b i:= Poly.send ((CA).tag i) ((CA).value i)
    have hV i: a (D i)+b (D i)= A.E.frame i t U:= logE t U i
    have ht i : a (D i)=0 ∨ b (D i)=0:= by
      by_cases h:A.E.clear i
      · apply Or.inl; change Poly.send _ (masked _ _ (unpin (drawn A t) 0 (pin i)) U)=0; rw [unpin_pin]; simp [drawn,h,masked]
      exact Or.inr (show Poly.send _ (unpin (nomad A t) 0 (pin i))=0 from by rw [unpin_pin, nomad,if_neg h,Poly.send_zero])
    have he:= (h.sums P.p.exponent_pos.le hw t U).norm
    have h1 : Summable a:= pin_injective.summable_iff (g:= (pin (α:=ι))) (f:=a) (fun i hi=> (vacR t U hi).1)|>.mp ((he.of_nonneg_of_le (g:=fun i=> ‖a (D i)‖) (fun i=>norm_nonneg _) (fun i=>by rw [← hV]; rcases ht i with h|h <;> simp [h])).of_norm)
    have h2 : Summable b:= pin_injective.summable_iff (g:= (pin (α:=ι))) (f:=b) (fun i hi=> (vacR t U hi).2)|>.mp ((he.of_nonneg_of_le (g:=fun i=> ‖b (D i)‖) (fun i=>norm_nonneg _) (fun i=>by rw [← hV]; rcases ht i with h|h <;> simp [h])).of_norm)
    have hx : ∀ i,(XA).units i=0:= fun _=>rfl
    change (∑ i:V,Poly.send (R.fire i) ((XA).units i))+_+_= _; simp_rw [hx, Poly.send_zero]; rw [Finset.sum_const_zero,zero_add]; change (∑' i,a i)+(∑' i,b i)=_
    rw [← Summable.tsum_add h1 h2]; refine (Push.Corrected.Pad.sums D pin_injective (fun i=>A.E.frame i t U) (fun i=>a i+b i) hV (fun i hi=> ?_)).symm
    by_contra hx; obtain ⟨hr,hs⟩:= vacR (A:=A) t U hx; apply hi
    change a i + b i= 0; rw [show a i=0 from hr,show b i=0 from hs,zero_add]


lemma same_density (hw:∀ v,0<w v)(h:A.Pays w P.p.supportExponent c b): ((taste A).leaf t).density=A.density t:=by
   funext U; rw [RG3.Forms.Deck.density, tasteH A t U hw h.budget]; unfold QuadraticLocal.Gallery.density
   suffices he:Bands.cluster XA U=A.gas t U by rw [he]
   refine tsum_congr fun i=>?_ ; unfold Bands.packet Fusion.Attached.packet; split; simp only [hostel A t U hw h.wages]; rfl

omit [Nonempty T] [Fintype V] in
private lemma contents (t:T) : Article.Contents ((Y).terms t) :=by
  constructor
  · intro i; by_cases he:i∈ Set.range Q
    · obtain ⟨i,rfl⟩:=he; rw [show (((view A).terms t).rays (Q i))=A.E.mode i from unpin_pin ..]; exact Finset.nonempty_iff_ne_empty.mpr (fun h=> A.E.live i (Subtype.ext h))
    rw [show ((view A).terms t).rays i=jv from unpin_blank _ _ he]; exact singleton_nonempty _
  · intro i v hv; by_cases he:i∈ Set.range Q
    · obtain ⟨i,rfl⟩:=he; rw [show (((view A).terms t).rays (Q i))=A.E.mode i from unpin_pin ..] at hv; rw [show (((view A).terms t).support (Q i))=focus A i from unpin_pin ..]; exact A.E.roots i v hv
    rw [show (((view A).terms t).support i)=univ from unpin_blank _ _ he]; exact Finset.mem_univ _
  intro i; by_cases he:i∈ Set.range Q
  · obtain ⟨i,rfl⟩:=he; rw [show (((view A).terms t).support (Q i))=focus A i from unpin_pin ..,show ((view A).terms t).H (Q i)=drawn A t i from unpin_pin ..]; unfold drawn; split; exact regular_const _; exact A.E.legal _ _
  rw [show (((view A).terms t).H i)=0 from unpin_blank _ _ he]; exact regular_const _

variable (hY:P.activities.ForcedFamily P.p)

section prices
local notation "D"=> (view A).impression (article A) id
local notation "B"=> P.p
variable (h:A.E.Paid w P.p.B P.p.supportExponent c)(hw:∀ v,0<w v)
local notation "facts" => Press.Article.Contents
include hw hY
omit [Fintype V] in
lemma snacks (hq:b≤q*κ)(hk:0<κ)(h:A.Pays w P.p.supportExponent c b) : Nonempty ((taste A).Snacks w 0 c q κ c):=by
   obtain ⟨f,hf,hR,hL⟩:=h.budget.budget; obtain ⟨g,hg,hB⟩:=h.wages.wages
   let F:= unpin f 0
   have hz i:0≤ F i:=by by_cases hp:i ∈ Set.range Q; obtain ⟨i,rfl⟩:=hp; unfold F; rw [unpin_pin]; exact hf i; exact (unpin_blank _ _ hp).ge
   have hP i: SumBudget ((view A).costR w F i) c:= by
      let v (j:ι):= if i∈ (A.E.mode j).val then Poly.toll w (A.E.mode j)* (B).mass (A.E.ground j) (f j) else 0
      have hv: SumBudget v c:= budget_mono (hL (o i)) (fun j=>by unfold v; split; exact mul_nonneg (Poly.worth hw _).le ((hf j).trans ((B).loMass _ _ (hf j))); exact le_rfl) fun j=> (by
         unfold v; split
         next ht=> rw [if_pos (show o i∈A.E.ground j from A.E.roots j i ht), BudgetPoint.mass]; linarith
         next=>exact (hL (o i)).1 j) -- layout
      refine Push.Corrected.Pad.absolute Q pin_injective ?_ (fun i h=> ?_) hv
      · intro j; unfold View.costR F view; simp only [unpin_pin]; rfl
      by_contra ht; apply h; unfold View.costR; split
      next=> rw [show F i=_ from unpin_blank _ _ ht]; simp [BudgetPoint.mass]
      next=>rfl
   have hp(i:ι)t v(hv:v∈(A.E.mode i).val): P.p.supBounds (o v) (A.E.ground i) (drawn A t i) (f i):=by
       unfold drawn; split; exact bound_weaken (bound_const _) ((norm_zero).trans_le (hf i)); exact hR i t _ (A.E.roots i v hv)
   have hΩ i t (v:V)(hv:v ∈ ((view A).rays i).val) : P.p.supBounds (o v) ((view A).branch i) ((view A).regular t i) (F i):= by
     by_cases he:i∈ Set.range Q
     · obtain ⟨i,rfl⟩:=he; rw [show (view A|>.rays (Q i))=A.E.mode i from unpin_pin ..] at hv; rw [show ((view A).branch (Q i))=focus A i from unpin_pin .., show (view A|>.regular t (Q i))=drawn A t i from unpin_pin ..,show F (Q i)=f i from unpin_pin ..]; exact hp i _ v hv
     rw [show ((view A).regular t i)=0 from unpin_blank _ _ he, show F i=0 from unpin_blank _ _ he]; exact bound_weaken (bound_const _) (norm_zero.le)
   obtain ⟨W⟩:= (view A).issued (article A) id rfl (fun t=> soundArticle A t hY) (carried A) g w hg hB hq hk hw (contents A) F (fun t i=> by change w i *‖(0:ℂ)‖ ≤ 0; simp) (fun i=> ⟨hz i, hΩ i ⟩) hP
   refine ⟨W, (fun t=>⟨(contents A t).1,(contents A t).2⟩), F, (fun i=>⟨hz i, fun t=>?_⟩), hP ⟩
   by_cases he:i∈ Set.range Q
   · obtain ⟨i,rfl⟩:=he; rw [show ((taste A).score t (Q i))=nomad A t i from unpin_pin ..,show F (Q i)=f i from unpin_pin ..]; unfold nomad; split; exact (hR i t _ (A.E.address i).anchor).2 1 (one_healthy _ _ P.p.threshold_pos.le) [] (Nat.zero_le _) (by simp); rw [norm_zero]; exact hf i
   rw [show ((taste A).score t i)=0 from unpin_blank _ _ he,norm_zero]; exact hz _

omit [Fintype V] in
private lemma score3 (hq:b≤q*κ)(hk:0<κ)(h:A.Pays w P.p.supportExponent c b) : Nonempty (FullBudget P.p (taste A) w κ (4*c) q):=by
  obtain ⟨W⟩:= snacks A hY hw hq hk h
  let white (i:ℕ):= 3* W.strong.white i; let T':=taste A
  have he i:0≤white i := mul_nonneg (by norm_num) (W.strong.bulk i).1
  have hV i (x:T) (v:V) (hv:v∈ (T'.menu.rays i).val): Mix.grain P.p (T'.menu.branch i) (T'.menu.regular x i) (o v) (white i):=by
     let w0 := W.strong.white i; have ht : P.p.supBounds (o v) (T'.menu.branch i) (T'.menu.regular x i) w0:= (W.strong.bulk i).2 x v hv
     refine ⟨fun _=> w0,fun _=> ht.1,?_,fun k h₁ h₂ U hU=> ht.2 _ hU _ h₁ h₂⟩
     let t (n:ℕ):ℝ:= 1 / n.factorial; have hS: HasSum t (Real.exp 1) :=by rw [Real.exp_eq_exp_ℝ]; simpa [t] using NormedSpace.expSeries_div_hasSum_exp (1:ℝ)
     let S:=Finset.range (P.p.order+1); change ∑ i ∈ S,(w0/_ :ℝ) ≤ _; have h0: w0* Real.exp 1 ≤ white i:= (mul_le_mul_of_nonneg_left Real.exp_one_lt_three.le ht.1).trans_eq (mul_comm w0 3)
     have hm := hS.mul_left w0; rw [← hm.tsum_eq] at h0
     refine le_trans (le_of_eq ?_) ((hm.summable.sum_le_tsum S (fun i _=> mul_nonneg ht.1 (by unfold t; positivity))).trans h0)
     congr 1; simp [t,div_eq_mul_inv]
  have hc1 (i:V): SumBudget (T'.menu.costR w white i) (3*c):=by
     convert budget_scale (show (0:ℝ)≤3 by norm_num) (W.strong.bulkCap i) using 1
     funext j; change ( (taste A).menu.costR w white i j)= 3*_ ; unfold white View.costR
     split
     · unfold BudgetPoint.mass; ring
     ring
  refine ⟨white,W.strong.black,W.gold,0,(fun t=> ((taste A).snack W t).1), hw,hk,he,(fun i=>⟨fun x=>hV i x⟩),?_,(fun i=>(W.strong.spends i.1 i.2).1), (fun x i j=> (W.strong.spends i j).2 x), (fun i=>(W.given i).1), fun t i=>(W.given i).2 t,fun v=>le_rfl, ?_, fun i=>⟨3*c,c,hc1 i,W.ticket i,?_⟩, ?_ ⟩ -- nested check
  · exact fun x=> (W.strong.active x).regular
  · intro x v; simp [taste,View.impression,view]
  · change w i * 0 + 3*c+c ≤ _; linarith
  intro i; rw [mul_comm κ]; exact W.strong.till i

theorem present (hq:b≤q*κ) (hk:0<κ)(h:A.Pays w P.p.supportExponent c b) : Nonempty (FullBudget P.p (taste A) w κ (4*c) q) ∧ (∀ t U,Bands.cluster ((taste A).leaf t).contents U=A.gas t U) ∧ (∀ t U, ((taste A).leaf t).log U=A.E.log t U) ∧ ∀ t, ((taste A).leaf t).density=A.density t := by
   refine ⟨score3 A hY hw hq hk h,?_,fun t U=> tasteH A t U hw h.budget,fun t=> same_density A t hw h⟩
   intro t U; refine tsum_congr fun i=>?_ ; unfold Bands.packet Fusion.Attached.packet; split; simp only [hostel A t U hw h.wages]; rfl
end prices
end YM.QuadraticLocal.Display
