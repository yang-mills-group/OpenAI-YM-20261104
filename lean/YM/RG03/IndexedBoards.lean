import YM.RG03.AtomAdapter
import YM.Push.LOCAL_SPLITTING.Calculus
import YM.Push.ABSOLUTE_SUMS.Basic

/-!
# Budgets in actual regular palettes for the path pass

Addresses have been aligned on common healthy supports at a *fixed threshold* before using this
lemma. A separate failed-mask attachment such as `Reclose.result`/`Joint.allows_exact` is needed
if the support arrays being tested here differ from those of incoming activities. `Costs.choose_all`
gives an unmasked identity at each indexed root (not at separately chosen masks), local ordered-
derivative estimates and affine-nullness of the added high-valuation term. `vacuum_step` uses this in
the concrete `Activities` accounting before and after exponentiation. A smooth inherited remainder
can be kept without ever supposing it analytic in the coupling, but its own nonlinear-RG estimates
are still an input, as is a genuine pre-output support reserve for the explicit new charges.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG03.Indexed
open RG Wilson PathWords Boards Tight Cost Lattice Push.Local Push.AbsoluteSums Next.Foundations MeasureTheory
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius Topology
variable {G:Gauge}{n:Side} {P:BudgetPoint} {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]
variable {I ι : Type*}[Fintype ι][DecidableEq ι]

def farLength (l q : ℕ) := l*3^q
def farGrade (r:Board ι)(q:ℕ) := grade r+2*q

def expense (P:BudgetPoint)(T:Token G E ι)(r:Board ι)(l q:ℕ):ℝ :=
    let L:=farLength l q
    let K:=farGrade r q
    capacity ι q L K * Cost.bill P T L K (grade r)

def rfield (T:I→Token G E ι)(r:I → List (Board ι))(o:I→Site n): I→Config G n → E := fun i=>render (T i) (r i) (o i)
omit [DecidableEq ι] in
lemma deposit (P:BudgetPoint)(T:Token G E ι)(r:Board ι)(l q:ℕ) :
    (@capacity ι _ q (farLength l q) (farGrade r q):ℝ)*Cost.bill P T (farLength l q) (farGrade r q) (grade r+q) =
        expense P T r l q * P.threshold^q := by
  simp only [expense,Cost.bill,pow_add,mul_assoc]

/-- All the following measure and gauge statements at *literal* test supports. No individual
reindexing of hidden marker loads. -/
theorem choose_all (P:BudgetPoint)(o:I→Site n)(S:I→Support n)[MeasurableSpace E][BorelSpace E]
    (T:I→Token G E ι)(r:I→Board ι)(l:I→ℕ)(q:ℕ)
    (hS:∀i, cage (farLength (l i) q) (o i)⊆S i)(hr:∀i,radius (r i) (l i))(ht:∀i,Together (T i)) :
    ∃ A B : I → List (Board ι), (∀i k,k∈A i→canonical k) ∧
    (fun i=>price (T i) (r i) (o i)) = rfield T A o + rfield T B o ∧
    ∀ i, let c:=expense P (T i) (r i) (l i) q
      P.Regular (S i) (rfield T A o i) ∧ P.supBounds (o i) (S i) (rfield T A o i) c ∧
      P.Regular (S i) (rfield T B o i) ∧ P.supBounds (o i) (S i) (rfield T B o i) (c*P.threshold^q) ∧
      Vanishes (grade (r i)+q) (rfield T B o i) := by
  choose A B hs hA hB hU using (fun i=> normalize_words (T i) (o i) (l i) (r i) q (hr i))
  refine ⟨A,B,fun i k h=>(hA i k h).1,funext (fun i=>funext (hU i)),fun i=> ?_⟩
  let L:=farLength (l i) q; let K:=farGrade (r i) q
  have hA' x (hx:x∈A i) : grade (r i)≤grade x ∧ bounded L K x := (hA i x hx).2
  have hB' x (hx:x∈B i) : grade (r i)+q≤grade x ∧ bounded L K x := hB i x hx
  have hs' : (A i).length+(B i).length≤capacity ι q L K:=hs i
  refine ⟨render_regular (T i) _ _ _ (fun x hx=>(hA' x hx).2) (ht i) (hS i),
    external_quote (T i) _ _ _ (hS i) (by change _≤capacity ι q L K;omega) hA',render_regular (T i) _ _ _ (fun x hx=>(hB' x hx).2) (ht i) (hS i),?_,render_vanish _ _ _ (fun x hx=>(hB' x hx).1)⟩
  rw [← deposit]; exact external_quote (T i) _ _ _ (hS i) (by change _≤capacity ι q L K;omega) hB'

section Vacuum

lemma regular_plus (P:BudgetPoint) {s:Support n} {f g:Config G n→ℝ} (hf:P.Regular s f)(hg:P.Regular s g):P.Regular s (f+g) := by
  refine ⟨(fun U V he=> congr_arg₂ HAdd.hAdd (hf.1 _ _ he) (hg.1 _ _ he)),hf.borel.add hg.borel,(fun u U=>congr_arg₂ HAdd.hAdd (hf.symmetry u U) (hg.symmetry u U)),
    (fun U hU=>(hf.smooth U hU).add (hg.smooth U hU)),(fun U hU a l hl=>left_has a hl ?_)⟩
  exact (hf.smooth U hU).add (hg.smooth U hU)
lemma bound_plus (P:BudgetPoint)(o:Site n) {s:Support n}{f g:Config G n→ℝ}{a b:ℝ}(hf:P.Regular s f)(hg : P.Regular s g)
    (ha:P.supBounds o s f a)(hb:P.supBounds o s g b) : P.supBounds o s (f+g) (a+b) := by
  refine ⟨add_nonneg ha.1 hb.1, fun U hU l hl hw=>?_⟩
  rw [Push.Local.left_add l (hf.smooth U hU) (hg.smooth U hU) hl]
  exact (norm_add_le ..).trans (add_le_add (ha.2 U hU l hl hw) (hb.2 U hU l hl hw))
open Finset
lemma identity_healthy (P:BudgetPoint)(S:Support n):Healthy P.threshold S (1:Config G n) := by
  refine disjoint_left.mpr fun x hx he=>?_
  obtain ⟨w,_,hw⟩:= (flags_spec ..).1 he
  have hz : G.chord (faceValue (1:Config G n) w)=0 := by rw [show faceValue (1:Config G n) w = 1 from identity_travels ..]; simp
  rw [hz] at hw; exact (not_lt_of_ge P.threshold_pos.le) hw
lemma hess_plus (P:BudgetPoint){S:Support n} {f g:Config G n→ℝ}(hf:P.Regular S f)(hg : P.Regular S g) (x y : Directions G n):
    logHessian (f+g) x y = logHessian f x y + logHessian g x y := by
  have he : (2:ℕ)≤P.order:= (by have := P.order_ge;omega)
  have ha:= (hf.smooth _ (identity_healthy (G:=G) P _)).of_le (m:=(2:WithTop ℕ∞)) (by
    convert! (Nat.cast_le (α:=WithTop ℕ∞).mpr he) using 1)
  have hb:= (hg.smooth _ (identity_healthy (G:=G) P _)).of_le (m:=(2:WithTop ℕ∞)) (by
    convert! (Nat.cast_le (α:=WithTop ℕ∞).mpr he) using 1)
  unfold logHessian
  rw [show (fun A : Directions G n=> (f+g) (increment 1 A))=(incident f + incident g) from rfl]; exact congr_arg (fun p:ContinuousMultilinearMap ℝ (fun _:Fin 2=>Directions G n) ℝ=>p ![x,y]) (iteratedFDeriv_add_apply ha hb)

def setE (D:Activities G n)(f : ℕ → Config G n→ℝ) := {D with E:=f}
lemma budget_occurrence (A:Activities G n)(P:BudgetPoint) {δ:ℝ}(h:A.EBound P δ)(U:Config G n):
    Summable fun i=>A.regularOccurrence P i U := by
  obtain ⟨b,hS,hB⟩:=Activities.E_total h
  apply Summable.of_norm_bounded hS; intro i
  by_cases he : Healthy P.threshold (A.reg i).support U
  · rw [Activities.regularOccurrence,masked_eq _ _ _ _ he]
    exact (hB i).2 U he [] (Nat.zero_le _) (by simp)
  rw [Activities.regularOccurrence,masked_ne _ _ _ _ he,norm_zero]
  exact (hB i).1
lemma exponential_add (A:Activities G n)(P:BudgetPoint)(f g:ℕ→Config G n→ℝ) {μ δ:ℝ}(hf:(setE A f).EBound P μ)(hg:(setE A g).EBound P δ) :
    (setE A (f+g)).additive P = (setE A f).additive P + (setE A g).additive P := by
  funext U
  change ∑' i,(setE A (f+g)).regularOccurrence P i U= (∑' i,(setE A f).regularOccurrence P i U)+(∑' i,(setE A g).regularOccurrence P i U)
  rw [← (budget_occurrence _ _ hf U).tsum_add (budget_occurrence _ _ hg U)] -- explicitly
  exact tsum_congr fun i=> by
    simp only [setE,Activities.regularOccurrence]
    by_cases h:Healthy P.threshold (A.reg i).support U
    · simp only [masked_eq _ _ _ _ h]; rfl
    simp [masked_ne _ _ _ _ h]

variable (D:Activities G n)(P:BudgetPoint)

def artist (X:ℕ→Token G ℝ ι)(r:ℕ→List (Board ι)) : ℕ→Config G n→ℝ :=
   rfield X r (fun i => (D.reg i).site)

def vacuumLoan (T:ℕ→Token G ℝ ι)(r:ℕ→Board ι)(l:ℕ→ℕ)(q:ℕ)(m:ℝ) := ∀ x, SumBudget (fun i=> if (D.reg i).site=x then
    P.mass (D.reg i).support (expense P (T i) (r i) (l i) q) else 0) m

theorem vacuum_step (T:ℕ→Token G ℝ ι)(r:ℕ→Board ι)(l:ℕ→ℕ)(q:ℕ)(c:ℕ→Config G n→ℝ)
    {b m : ℝ} (he : D.E = c+(fun i U=>price (T i) (r i) (D.reg i).site U))
    (hI:(setE D c).RegularFamily P)(hb:(setE D c).EBound P b)
    (hs:∀ i,cage (farLength (l i) q) (D.reg i).site⊆(D.reg i).support)(ha:∀ i,radius (r i) (l i))(ht:∀ i,Together (T i))
    (hD:∀i,3≤grade (r i)+q)(hm:vacuumLoan D P T r l q m) :
    ∃ A B:ℕ→List (Board ι), (∀i z,z∈A i→canonical z) ∧
      D.E = artist D T A + (c+artist D T B) ∧
      (setE D (D.E-artist D T A)).RegularFamily P ∧
      (setE D (D.E-artist D T A)).EBound P (b+m*P.threshold^q) ∧ (setE D (artist D T A)).EBound P m ∧
      D.additive P = (setE D (artist D T A)).additive P+(setE D (D.E-artist D T A)).additive P := by
  obtain ⟨A,B,hA,hR,h⟩:=choose_all P (fun i=>(D.reg i).site) _ T r l q hs ha ht
  have ht : D.E=artist D T A+(c+artist D T B) := by
    change D.E= c + (fun i=>price (T i) (r i) (D.reg i).site) at he
    change D.E= rfield T A _+_; rw [he,hR]; unfold artist; abel
  have he' : D.E-artist D T A=c+artist D T B := by rw [ht]; abel
  have hw i := hI.smooth i
  have hsmooth i := (h i).2.2.1
  have hreg :(setE D (c+artist D T B)).RegularFamily P := by
    refine ⟨(fun i=>regular_plus P (hw i) (hsmooth i)),?_,?_⟩
    · intro i; change c i 1 + artist D T B i 1=0
      rw [show c i 1=0 from hI.at_flat _,show artist D T B i 1=0 from (h i).2.2.2.2.shorten (by have := hD i; omega) |>.flat,add_zero]
    intro i hr a b ha hb
    have hv: logHessian (c i) a b=0:=hI.vanish i hr a b ha hb
    have ht : logHessian (artist D T B i) a b=0 := (h i).2.2.2.2.shorten (hD i) |>.affine a b
    calc _ = logHessian (c i) a b+logHessian (artist D T B i) a b:=hess_plus P (hw i) (hsmooth i) a b
         _ = _:=by rw [hv,ht,add_zero]
  obtain ⟨e,h',hB⟩:=hb
  let F(i):=expense P (T i) (r i) (l i) q
  have hModel : (setE D (artist D T A)).EBound P m := ⟨F,fun i=>(h i).2.1,hm⟩
  have hBudget : (setE D (c+artist D T B)).EBound P (b+m*P.threshold^q) := by
    refine ⟨fun i=> e i+ F i*P.threshold^q,fun i=>bound_plus P _ (hw i) (hsmooth i) (h' i) (h i).2.2.2.1,fun x=>?_⟩
    rw [mul_comm m]
    convert budget_plus (hB x) (budget_scale (pow_nonneg P.threshold_pos.le q) (hm x)) using 1
    funext i; dsimp [setE,F]; split <;> simp [*,BudgetPoint.mass]; ring
  refine ⟨A,B,hA,ht,he'.symm ▸ hreg,he'.symm ▸ hBudget,hModel,?_⟩
  convert! exponential_add D P (artist D T A) (D.E-artist D T A) hModel (he'.symm ▸ hBudget) using 2
  rw [show artist D T A+(D.E-artist D T A)=D.E from add_sub_cancel _ _]; rfl
end Vacuum
end YM.RG03.Indexed
