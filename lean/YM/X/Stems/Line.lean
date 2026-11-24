import YM.X.Stems.Window
/-!
Independent orbit on position rules with multiplicative engineering scaling (returns continuous centers later).
Here Whitney frame/calibration **not** used yet. Vertex mark pair may be of any lexical horizon.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Stems
open Function Filter Set Metric MeasureTheory Lattice Wilson PertExtension PertExtension.Series PertExtension.Series.Radial
open Source ProjectorNext.Calibration Gauss Next.Rank Normal MvPolynomial Precision
open Feyn Gauge LatticePT PertExtension.Orb Chart Series.Tested Finset
open Pert.Orb (positiveLinks wilson Potential)
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge} {n:Side} {j:ℕ}{d:ℕ}{I : Type*}[Fintype I]
variable (U : Potential G n) (he:Even n.val)(h:G.Simple)
local notation "E" => Potential G n
local notation "J" => Jam n G

def water : Symmetric J:= formed pier cost
def mean : poly J→ₗ[ℂ] ℂ := blend water 0
lemma sprinters (r:E→ℝ)(p:poly J)(hr:∀ v:E,glaze v p=(r v :ℂ)): mean p=(fog r:ℂ):= by
    let L:=Complex.reCLM;let v:=Complex.imCLM
    have hh := expect_leads cost mist («E»:=E) pier L.toLinearMap p
    have he := expect_leads cost mist («E»:=E) pier v.toLinearMap p
    rw [show seen pier L.toLinearMap p=r from funext fun u=>congr_arg Complex.re (hr u)] at hh -- ends? cast
    rw [show seen pier v.toLinearMap p=0 from funext fun u=>congr_arg Complex.im (hr u), Gauss.average_zero] at he
    exact Complex.ext hh.symm he.symm
variable (o : I→Site n) (w:I→Word G)(t:Mixed.Task w)(ε:ℝ)
local notation "Φ"=> X o w t ε
local notation "Λ"=> ∏ i:I, exactus w t o ε 0 i

include he
lemma headN : mean (∏ i:I, exactus w t o ε 0 i)=(diagonalWith (tray G) (restrictedO Φ) (Mixed.number w t) :ℂ):= by
   -- explicit w? t binder references old; edit
   let O:= X o w t ε; let n:=Mixed.number w t
   obtain ⟨u,v⟩:= Mixed.product_good w t o ε
   rw [full0 he (smoothRX o w t ε he) u.curved v (gaugeX o w t ε) (traySpec G)]; exact sprinters (jet _ n) _ (fun u=> exact_glaze u o w t ε) -- provide traySpec G
include h
lemma plusN [DecidableEq I]: mean (exact₁ o w t ε - (∏ i:I, exactus w t o ε 0 i)*boil) = (diagonalWith (tray G) (restrictedO Φ) (Mixed.number w t+1) :ℂ) := by
   let n:= Mixed.number w t
   obtain ⟨u,v⟩:= Mixed.product_good w t o ε
   rw [full1 he (smoothRX o w t ε he) u.curved v (gaugeX o w t ε) h (traySpec G)]
   refine sprinters (fry _ n) _ ?_; intro y; unfold fry; simp only [_root_.map_sub,_root_.map_mul, next_glaze, exact_glaze, overTop,← Complex.ofReal_mul,← Complex.ofReal_sub]; rfl

omit he h
lemma task_sum {Y: I→ Type*}[∀ i,Fintype (Y i)] {V : Type*}[CommSemiring V] [DecidableEq I](f g:(i:I)→ Y i→V): ∑ p:(i:I)→Y i,Jet.dot (fun i=>f i (p i)) (fun i=>g i (p i)) Finset.univ = Jet.dot (fun i=>∑ z,f i z) (fun i=>∑ z,g i z) Finset.univ:= by
   classical
   simp_rw [Jet.listed]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i hi
   conv_rhs=>arg 2; intro j; rw [show (if i=j then ∑ z,g j z else ∑ z,f j z)=∑ z,if i=j then g j z else f j z by split_ifs <;> simp [*]]
   apply Eq.symm; rw [Finset.prod_univ_sum,Fintype.piFinset_univ]
lemma dot_factors [DecidableEq I] {V:Type*}[CommSemiring V] (f g q:I→V): Jet.dot (q*f) (q*g) Finset.univ=(∏ i:I,q i)*Jet.dot f g Finset.univ:= by rw [Jet.listed,Jet.listed, Finset.mul_sum]; refine Finset.sum_congr rfl fun j _=>?_ ; rw [← Finset.prod_mul_distrib]; apply Finset.prod_congr rfl; intro i hi;split_ifs<;> rfl

def toll (ε:ℝ)(i:Word G):ℝ:= ε^4/ε^i.d
lemma sumBump (w:Word G)(j:ℕ)(o:Site n) : ∑ i:w.F.Index, bump j w o i ε=((toll ε w:ℝ):ℂ) • hairAt o (bookMark w j):= by unfold bookMark; rw [_root_.map_sum, Finset.smul_sum]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [map_smul, smul_smul, bump,Word.cost,Complex.ofReal_mul]; rfl

local notation "L"=> ((∏ i:I, toll ε (w i):ℝ):ℂ)
-- ordinary positioned products

def transfers (r:ℕ) : I→poly J := fun i=>hairAt (o i) (bookMark (w i) r)
def road := ∏ i:I,transfers o w 0 i
def triangle [DecidableEq I]:= Jet.dot (transfers o w 0) (transfers o w 1) Finset.univ
private lemma pin_a (z:ℂ)(x:poly J): z • x=MvPolynomial.C z*x := C_mul' .. |>.symm
lemma before_sum [DecidableEq I] : ∑ p:Mixed.Task w, (∏ i:I,exactus w p o ε 0 i)= ((∏ i:I,toll ε (w i):ℝ):ℂ) • road o w:= by
   change ∑ p:Mixed.Task w, (∏ i:I,bump 0 (w i) (o i) (p i) ε)= L • road o w
   rw [← Fintype.piFinset_univ,← Finset.prod_univ_sum _ (fun i:I=>fun t=> bump 0 (w i) (o i) t ε)]; simp_rw [sumBump,pin_a]; rw [Finset.prod_mul_distrib,Complex.ofReal_prod,map_prod];rfl
lemma next_sum [DecidableEq I] : ∑ p:Mixed.Task w,exact₁ o w p ε=((∏ i:I,toll ε (w i):ℝ):ℂ) • triangle o w:= by
   unfold exact₁ exactus; rw [task_sum (fun i t=> bump 0 (w i) (o i) t ε) (fun i t=> bump 1 (w i) (o i) t ε)]; simp_rw [sumBump,pin_a]; rw [Complex.ofReal_prod,map_prod]; exact dot_factors (transfers o w 0) (transfers o w 1) (fun i=> C ((toll ε (w i) :ℝ):ℂ))

-- return point rows scaled by multiplicative L
abbrev rowP [DecidableEq I](e:ℕ) := ∑ t:Mixed.Task w,diagonalWith (tray G) (restrictedO (X o w t ε)) (Mixed.number w t+e)
lemma formula (he:Even n.val)[DecidableEq I] : (rowP o w ε 0:ℂ)= ((∏ i:I,toll ε (w i):ℝ):ℂ)*mean (road o w) := by unfold rowP; rw [Complex.ofReal_sum]; simp_rw [Nat.add_zero,← headN he]; rw [← map_sum,before_sum,map_smul];rfl
lemma formula' (he:Even n.val)(h:G.Simple)[DecidableEq I] : (rowP o w ε 1:ℂ)= ((∏ i:I,toll ε (w i):ℝ):ℂ)* mean (triangle o w - road o w*boil):= by unfold rowP; rw [Complex.ofReal_sum]; simp_rw [← plusN he h]; rw [← map_sum, Finset.sum_sub_distrib,next_sum o w ε,← Finset.sum_mul,before_sum,smul_mul_assoc, ← smul_sub,map_smul];rfl
end YM.PositionX.Stems
