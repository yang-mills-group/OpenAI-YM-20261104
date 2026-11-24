import YM.RGComparison.Core16.Lumen.Stage

/-!
# Local pressure polynomials at coupled precisions.

Charge each finite combination before cancellation. Support not needed on resulting moment solve
in this seam; matters in actual Peierls and Fk costs. `Offers` not a replacement of real-source
`Y` or residual norms. Readers use via `Ticket`. Pointwise Wick polynomials only, rescale here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Lumen
open Function Filter Lattice RG Tree Wilson MeasureTheory Pressure Metric Push.Uniform Forge
open Planet Finset
open scoped Topology ContDiff BigOperators Classical InnerProductSpace
variable {G:Gauge} {S:Side} {ι k T A D:Type}

abbrev Rail (G:Gauge)(ι:Type):= List (Wire G ι)
def tally (g:ℝ) (w:Wire G ι)(x:Sky G ι):= curve x w / g
def sing (w:Rail G ι) (g:ℝ)(x: Sky G ι):= (w.map (fun i=> tally g i x)).prod
lemma sing_nil {g:ℝ} (x:Sky G ι) : sing [] g x=1:=rfl
lemma sing_cons {w:Rail G ι} {i:Wire G ι} (x:Sky G ι)(g:ℝ) : sing (i::w) g x=tally g i x*sing w g x:=rfl
lemma sing_join {g:ℝ}(x:Sky G ι)(a b:Rail G ι):sing (a++b) g x=sing a g x*sing b g x:= by simp [sing,List.prod_append]
lemma tally_cont (g:ℝ)(w:Wire G ι): Continuous (tally g w):= by
    unfold tally curve; fun_prop
lemma sing_cont (w:Rail G ι)(g:ℝ):Continuous (sing w g):=by induction w with
    | nil=>exact continuous_const
    | cons i _ hi=>exact (tally_cont g i).mul hi

abbrev Melody (G:Gauge)(ι:Type):= ℝ→ Sky G ι→ℝ
-- shell budget
inductive Offers (d:ℕ) : ℝ→ Melody G ι→Prop
| words (w:Rail G ι): w.length ≤ d→ Offers d 1 (sing w)
| add {p q:Melody G ι} {x y:ℝ}:Offers d x p→ Offers d y q→ Offers d (x+y) (p+q)
| scale (a:ℝ){p:Melody G ι}{x:ℝ}: Offers d x p→ Offers d (|a| *x) (a • p)
| raise {p:Melody G ι}{x y:ℝ}: Offers d x p→ x≤y→ Offers d y p
namespace Offers
variable {x y:ℝ}{d n:ℕ}{p q:Melody G ι} (H:Offers d x p)
omit H in -- none
lemma flat (d:ℕ)(x:ℝ): Offers (G:=G) (ι:=ι) d |x| (fun _ _=>x):= by
    have h:Offers d _ _:= @Offers.scale G ι _ x _ _ (Offers.words [] (Nat.zero_le d)); convert! h using 1; simp; ext; simp [sing]
omit H in
lemma zero (d:ℕ) : Offers d 0 (0:Melody G ι):= by change Offers _ _ fun _ _=>0; simpa only [abs_zero] using flat (G:=G) (ι:=ι) d 0
include H
lemma pos:0≤x:=by induction H <;> first|exact zero_le_one|apply add_nonneg <;> assumption|apply mul_nonneg (abs_nonneg _) <;> assumption|exact le_trans (by assumption) (by assumption)
lemma widen (h:d≤n) : Offers n x p:= by induction H with
    | words w hw=> exact .words w (hw.trans h)
    | add _ _ hp hq => exact .add hp hq
    | scale a _ hp=> exact .scale _ hp
    | raise _ h hx=> exact .raise hx h
lemma cont (g:ℝ):Continuous (p g):=by induction H with
    | words w _=> exact sing_cont w g
    | add _ _ hp hq => exact hp.add hq
    | scale a _ hp => exact (continuous_const (y:=a)).smul hp
    | raise _ _ h=> exact h
lemma local_mul (u:Rail G ι)(h:u.length≤n): Offers (d+n) x (p*sing u):=by
    induction H with
    | words w hw=>
       rw [show sing w*sing u=sing (w++u) from funext fun g=>funext fun x=>(sing_join x w u).symm]
       exact .words _ (by simp; omega)
    | add _ _ hp hq=> rw [RightDistribClass.right_distrib]; exact .add hp hq
    | scale a _ hp=>rw [smul_mul_assoc]; exact .scale _ hp
    | raise _ _ hx=>exact .raise hx (by assumption)
-- protect left & right at same normalized moment; multiply in same g convention.
lemma mul (J:Offers n y q): Offers (d+n) (x*y) (p*q):=by
    induction J with
    | words w hw=> rw [mul_one]; exact H.local_mul w hw
    | add _ _ hp hq=> rw [mul_add p,mul_add x]; exact .add hp hq
    | scale a _ hp=> rw [mul_smul_comm a, mul_left_comm x]; exact .scale a hp
    | raise _ h hz=> exact .raise hz (mul_le_mul_of_nonneg_left h H.pos)
omit H in
lemma finance {α:Type*}(f:α→ Melody G ι)(c:α→ℝ)(t:Finset α)(h:∀i∈t,Offers d (c i) (f i)): Offers d (∑ i∈t,c i) (∑ i∈t,f i):=by
    induction t using Finset.induction_on with
    | empty=> simp_rw [sum_empty]; exact zero _
    | insert i t ht ih=> rw [sum_insert ht,sum_insert ht]; exact (h i (mem_insert_self ..)).add (ih (fun j hj=>h j (mem_insert_of_mem hj)))
omit H in
lemma team {α:Type*} (f:α→Melody G ι)(c:α→ℝ)(t:Finset α)(h:∀i∈t,Offers d (c i) (f i)): Offers (t.card*d) (∏ i∈t,c i) (∏ i∈t,f i):=by
    induction t using Finset.induction_on with
    | empty=> rw [prod_empty,prod_empty,card_empty,zero_mul]; exact .words [] (Nat.zero_le 0)
    | insert i t ht ih=> rw [prod_insert ht,prod_insert ht,card_insert_of_notMem ht,add_mul,one_mul,add_comm (t.card*d)]; exact (h i (mem_insert_self ..)).mul (ih (fun j hj=> h j (mem_insert_of_mem hj)))

-- computes ∑vac costs by an older allocator, no g.ap continuation hidden. Hp.L receipts
-- by ab initio lower pert order for SD. Width-independent after that order.
variable {X:Shelf G A D} {P:Planet X S ι k T} [Fintype ι][Fintype k][Fintype T][Fintype D]
   (J:P.Steady){U:Stage}{c:ℝ}
include J
lemma stints {r:ℕ}(w:Melody G ι)(hh:w=p)(hU:∀ s:ℝ,U.L≤s→amen X (dollar s))(hc:0≤c) (hb:∀ u:Rail G ι,u.length≤d→U.Ticket r c (fun s=> P.expect (dollar s) (sing u (dollar s)))) : U.Ticket r (c*x) (fun s=> P.expect (dollar s) (w (dollar s))):=by
    subst w
    induction H with
    | words w hw=> rw [mul_one]; exact hb w hw
    | @add f g x y p q hp hq=>
       rw [mul_add]; refine (hp.more hq).reload fun s hs=>?_ ; exact (expect_add J (hU s hs) (havenreal (p.cont ..)) (havenreal (q.cont ..))).symm
    | scale a hx hj=> rw [mul_left_comm c]; exact (hj.scales a).reload fun s hs=> (P.expect_mul _ _ _).symm
    | raise _ hk hj=>exact hj.promote (mul_le_mul_of_nonneg_left hk hc)
end Offers
end YM.RGComparison.Core16.Lumen
