import YM.RG03.TransportBill
import YM.RG03.BoardHull

/-!
# Curvature grading charged in the actual ordered link norm

At fixed color group, multilinear slots and derivative order/power, all lengths appear polynomially
(up to the exponential of the resulting cover paid separately). Coefficient coordinates use
fixed-dimensional real spaces (including color contractions, no period/marker-dependent norm
equivalence). Keep the original multilinear token for gauge invariance. Smooth bounds concern
each unmasked germ on the supplied healthy domain, including tested boundary equality as in
`supBounds`; no differentiation of hard indicators.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG03.Cost
open RG Wilson Lattice Work.G07 Boards Tight PathWords
open scoped BigOperators Matrix.Norms.Frobenius ContDiff Classical Topology
open Module
variable {G:Gauge} {n:Side} {P:BudgetPoint} {E: Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {o:Site n} {X:Support n}

lemma constant_vanish {x:E}: Vanishes 0 (fun _:Config G n=> x) := ⟨contDiff_const,fun _ h=>False.elim (Nat.not_lt_zero _ h)⟩

lemma word_vanish (w:Word)(o:Site n): Vanishes w.length (value (G:=G) w o) := by
  induction w with
  | nil => exact constant_vanish
  | cons c w ih =>
    rw [List.length_cons, Nat.add_comm]
    exact Vanishes.mul (defect_vanish G o c) ih

def jump (P : BudgetPoint) := (2:ℝ)^P.order
def level (G:Gauge)(P:BudgetPoint)(l:ℕ) := jump P * defectCost G P (2*l+4)
lemma level_ge (l:ℕ) : 1 ≤ level G P l := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (one_le_two)) (defectCost_ge ..)

lemma word_pay (P:BudgetPoint)(o:Site n)(w:Word) {l:ℕ}(hr:short w l):
    Pays P o (cage l o) (value (G:=G) w o) (‖(1:G.Mat)‖ * (level G P l * P.threshold)^w.length) := by
  induction w with
  | nil => simpa using! (LeftBound.const (r:=(1:ℝ)) (k:=P.order) (D:=P.dirBound o) (Z:=Healthy P.threshold (cage l o)) zero_le_one (1:G.Mat))
  | cons c w ih =>
    have hc := hr _ List.mem_cons_self
    have hl : c.path.length=2*c.prefix'.length+4 := by unfold Circuit.path oriented Lattice.reverse; simp; omega
    have hp:=defect_pay (G:=G) P o (cage l o) c (l:=2*l+4) (by omega) (in_cage hc o)
    apply Pays.mul hp (ih fun i hi=> hr i (List.mem_cons_of_mem c hi)) |>.more (le_of_eq ?_)
    rw [List.length_cons,pow_succ]; unfold level jump; ring

def digits (G:Gauge) := Fin (finrank ℝ G.Mat)
instance : Fintype (digits G) := Fin.fintype _
noncomputable instance : DecidableEq (digits G) := inferInstanceAs (DecidableEq (Fin _))
def desk (G:Gauge) : Basis (digits G) ℝ G.Mat := finBasis ℝ G.Mat
def lip (L:E→L[ℝ]ℝ):ℝ:= ‖L‖
lemma lip_nonneg (L:E→L[ℝ]ℝ) : 0≤lip L:=norm_nonneg _
def coordinate (G:Gauge)(i:digits G) := ((desk G).coord i).toContinuousLinearMap

variable {ι:Type*}{r:Board ι}

def voucher (T:Token G E ι)(i:ι→digits G) : ℝ→L[ℝ] E :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight (T (fun j=>(desk G) (i j)))

variable [Fintype ι]

def ink (T:Token G E ι) : ℝ := ∑ i : ι→digits G, ‖voucher T i‖ * ∏ j, lip (coordinate G (i j))
def core (P:BudgetPoint)(T:Token G E ι) := ink T * (jump P*‖(1:G.Mat)‖)^Fintype.card ι
def bill (P:BudgetPoint)(T:Token G E ι)(l K j:ℕ) := core P T*(level G P l)^K * P.threshold^j
lemma core_nonneg (P:BudgetPoint)(T:Token G E ι) : 0≤core P T := by unfold core ink jump; refine mul_nonneg (Finset.sum_nonneg (fun i _=> mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun j _=> lip_nonneg _))) (by positivity)
lemma bill_nonneg (P:BudgetPoint)(T:Token G E ι)(l K j:ℕ) : 0≤bill P T l K j := by
  have h:= core_nonneg P T; have := level_ge (G:=G) (P:=P) l; have := P.threshold_pos; unfold bill; positivity

def signal (i:ι→digits G)(r:Board ι)(o:Site n)(U:Config G n):ℝ :=
   ∏ j, coordinate G (i j) (value (r j) o U)

lemma encode (T:Token G E ι)(r:Board ι)(o:Site n)(U:Config G n):
    price T r o U = ∑ i : ι→digits G,voucher T i (signal i r o U) := by
  let f (j : ι) (k) := coordinate G k (value (r j) o U) • desk G k
  have he j : ∑ k, f j k = arrayValue r o U j := (desk G).sum_repr _
  unfold price; rw [← funext he, T.map_sum]
  exact Finset.sum_congr rfl fun i _ => T.map_smul_univ _ _

open Finset
omit [Fintype ι] in
private lemma prod_vanish (I:Finset ι)(f:ι→Config G n→ℝ)(p:ι→ℕ)(h:∀ i,Vanishes (p i) (f i)) :
    Vanishes (∑ i∈I,p i) fun U=>∏ i∈I,f i U := by
  induction I using Finset.induction_on with
  | empty => simpa using (constant_vanish (x:=(1:ℝ)) (G:=G) (n:=n))
  | insert i I hi ih => rw [sum_insert hi]; simp only [prod_insert hi]; exact (h i).mul ih
omit [Fintype ι] in
private lemma sum_vanish {q:ℕ}(I:Finset ι)(f:ι→Config G n→E)(h:∀ i,Vanishes q (f i)) :
    Vanishes q fun U=>∑ i∈I,f i U := by
  induction I using Finset.induction_on with
  | empty => simp only [sum_empty]; refine ⟨contDiff_const,fun j hj=>?_⟩; rw [show incident (fun U:Config G n=>(0:E)) = 0 from rfl, iteratedFDeriv_zero]; rfl
  | insert i I hi ih => simp only [sum_insert hi]; exact (h i).add ih

omit [Fintype ι] in
private lemma prod_pay (I:Finset ι)(f:ι→Config G n→ℝ)(b:ι→ℝ)(h:∀ i,Pays P o X (f i) (b i)) :
    Pays P o X (fun U=>∏ i∈I,f i U) (∏ i∈I,jump P*b i) := by
  induction I using Finset.induction_on with
  | empty => simpa using! (LeftBound.const (r:=(1:ℝ)) (k:=P.order) (D:=P.dirBound o) (Z:=Healthy P.threshold X) zero_le_one (1:ℝ))
  | insert i I hi ih => simp only [prod_insert hi]; apply (h i).mul ih
omit [Fintype ι] in
private lemma sum_pay (I:Finset ι)(f:ι→Config G n→E)(b:ι→ℝ)(h:∀ i,Pays P o X (f i) (b i)) :
    Pays P o X (fun U=>∑ i∈I,f i U) (∑ i∈I,b i) := by
  induction I using Finset.induction_on with
  | empty => simpa using! (LeftBound.const (r:=(1:ℝ)) (k:=P.order) (D:=P.dirBound o) (Z:=Healthy P.threshold X) zero_le_one (0:E))
  | insert i I hi ih => simp only [sum_insert hi]; apply (h i).add ih

lemma scaled (T:Token G E ι)(r:Board ι)(P:BudgetPoint)(l:ℕ) :
    bill P T l (grade r) (grade r)=
    ∑ a : ι→digits G, ‖voucher T a‖ * ∏ j, (jump P * (lip (coordinate G (a j)) * (‖(1:G.Mat)‖ * (level G P l * P.threshold)^(r j).length))) := by
  unfold bill core ink grade
  simp only [sum_mul]
  refine sum_congr rfl fun a _=>?_
  have he (j:ι) : jump P * (lip (coordinate G (a j)) * (‖(1:G.Mat)‖ * (level G P l * P.threshold)^(r j).length)) =
       lip (coordinate G (a j))*(jump P*‖(1:G.Mat)‖)*((level G P l)^((r j).length)*(P.threshold)^((r j).length)) := by rw [mul_pow];ring
  simp_rw [he]; rw [prod_mul_distrib,prod_mul_distrib,prod_mul_distrib,prod_mul_distrib,prod_const,prod_const,card_univ, prod_pow_eq_pow_sum,prod_pow_eq_pow_sum,mul_pow]; ring

lemma price_vanish (T:Token G E ι)(r:Board ι)(o:Site n) : Vanishes (grade r) (price T r o) := by
  rw [show price T r o = fun U=> _ from funext (encode T r o)]
  refine sum_vanish _ _ fun i=>(prod_vanish (n:=n) univ _ _ ?_).clm (voucher T i)
  exact fun j=>(word_vanish (G:=G) (r j) o).clm (coordinate G (i j))

lemma price_pay (T:Token G E ι)(r:Board ι)(P:BudgetPoint)(o:Site n){l:ℕ}(h:radius r l):
    Pays P o (cage l o) (price T r o) (bill P T l (grade r) (grade r)) := by
  rw [show price T r o = fun U=> _ from funext (encode T r o),scaled]
  exact sum_pay (G:=G) (E:=E) (P:=P) (o:=o) (X:=cage l o) univ _ _ (fun i=> LeftBound.postcomp
      (show Pays P o (cage l o) (signal (G:=G) i r o) _ from prod_pay univ _ _ fun j=>
        LeftBound.postcomp (word_pay (G:=G) P o _ (h j)) (coordinate G (i j))) (voucher T _))
omit [Fintype ι] in
lemma word_continuous (w:Word)(o:Site n) : Continuous (value (G:=G) w o) := by
  induction w with
  | nil => exact continuous_const
  | cons c w ih =>
    apply Continuous.mul (f:=c.defect (G:=G) o) ?_ ih
    exact (G.continuous_mat.comp (continuous_travel _ _)).sub continuous_const

lemma price_continuous (T:Token G E ι)(r:Board ι)(o:Site n) : Continuous (price T r o) := by
  rw [show price T r o = fun U=> _ from funext (encode T r o)]
  exact continuous_finsetSum _ fun a _=>(voucher T a).continuous.comp (continuous_finsetProd _ fun i _=>(coordinate G (a i)).continuous.comp
    (word_continuous (r i) o))

lemma price_regular (T:Token G E ι)[MeasurableSpace E][BorelSpace E](r:Board ι)(o:Site n){l:ℕ}
    (h:radius r l) (ht:Together T)(P:BudgetPoint) : P.Regular (cage l o) (price T r o) := by
  have hp := price_pay T r P o h |>.smooth
  refine ⟨price_local _ h o,(price_continuous ..).measurable,price_invariant ht r o,fun U hu=>?_ ,fun U hu a t hl=>hp.has hl.le U a⟩
  exact (hp [] (Nat.zero_le _) U).contDiffAt.of_le (by exact_mod_cast le_top (a:=(P.order:ℕ∞)))

lemma priced_tail (T:Token G E ι)(r:Board ι)(P:BudgetPoint)(o:Site n){l L K:ℕ}
    (h:bounded l L r)(hk: K≤grade r) : Pays P o (cage l o) (price T r o) (bill P T l L K) := by
  apply (price_pay T r P o h.2).more
  unfold bill
  have ht := pow_le_pow_of_le_one P.threshold_pos.le P.threshold_le hk
  have hl := pow_le_pow_right₀ (level_ge (G:=G) (P:=P) l) h.1
  have hc := core_nonneg P T; have HN : 0≤level G P l := zero_le_one.trans (level_ge _)
  exact mul_le_mul (mul_le_mul_of_nonneg_left hl hc) ht (pow_nonneg P.threshold_pos.le _) (mul_nonneg hc (pow_nonneg HN _))

def stub (P:BudgetPoint)(T:Token G E ι)(l K q m : ℕ) := capacity ι q l K * bill P T l K m
lemma assembled (T:Token G E ι)(r:List (Board ι))(P:BudgetPoint)(o:Site n) {q l L K:ℕ}
  (hb : r.length ≤capacity ι q l L) (h : ∀ i∈r, bounded l L i) (hk:∀ i∈r,K≤grade i) :
  Pays P o (cage l o) (render T r o) (stub P T l L q K) := by
 have he : Pays P o (cage l o) (render T r o) ((r.length:ℝ) * bill P T l L K) := by
   clear hb; induction r with
   | nil => simpa using! (LeftBound.const (r:=(1:ℝ)) (k:=P.order) (D:=P.dirBound o) (Z:=Healthy P.threshold (cage l o)) zero_le_one (0:E))
   | cons i r ih =>
     rw [List.length_cons,Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_comm]
     exact Pays.add (priced_tail T i P o (h i List.mem_cons_self) (hk i List.mem_cons_self)) (ih (fun j hj=>h j (List.mem_cons_of_mem i hj)) (fun j hj=>hk j (List.mem_cons_of_mem i hj)))
 exact he.more (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hb) (bill_nonneg P T l L K))
end YM.RG03.Cost
