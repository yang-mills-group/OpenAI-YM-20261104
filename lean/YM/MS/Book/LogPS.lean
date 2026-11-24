import YM.MS.High.Logs
import YM.MS.Book.Triang
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Real polynomial parameters and wave transformations

Work over complexification in coefficient calculations but always preserve full y polynomial data.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Book.Program
open Function Filter Set Finset Koszul Convolve Logarithm
open PowerSeries (coeff)
variable {I: Type} {M:Type}[AddCommGroup M][Module ℝ M]{f g : ℝ→ℂ} {a b:ℝ→ Cn}

def Decent (f:ℝ→ℂ):= ∃ v:ℝ→ℝ, Ready v ∧ f=fun i=> (v i:ℂ)
namespace Decent
lemma const (x:ℝ): Decent (fun _=>(x:ℂ)):= ⟨_,Ready.const x,rfl⟩
lemma add (h:Decent f)(he:Decent g): Decent (f+g):= by obtain ⟨v,h,rfl⟩:=h; obtain ⟨u,hg,rfl⟩:=he; exact ⟨_, Ready.add h hg,by ext; simp⟩
lemma neg (h:Decent f): Decent (-f):= by obtain ⟨v,h,rfl⟩:=h; exact ⟨_, Ready.neg h,by ext; simp⟩
lemma mul (h:Decent f)(he:Decent g): Decent (f*g):= by obtain ⟨v,h,rfl⟩:=h; obtain ⟨u,hg,rfl⟩:=he; exact ⟨_, Ready.smul h hg,by ext; simp⟩
lemma sums (s:Finset I){V:I→ℝ→ℂ} (h:∀ i∈s, Decent (V i)): Decent (fun y=>∑ i∈s,V i y):= by
    classical
    induction s using Finset.induction_on with
    | empty=> convert! const 0 using 1
    | insert i s hi ih=> simp_rw [Finset.sum_insert hi]; exact add (h i (by simp)) (ih fun j hj=> h j (mem_insert_of_mem hj))
lemma starv (h:Decent f)(i:ℝ): star (f i)=f i:= by obtain ⟨v,h,rfl⟩:=h; simp
end Decent

def Ren (K:ℝ→ Cn):=∀ i:ℕ, Decent (fun x:ℝ => coeff i (K x))
namespace Ren
lemma mul (h: Ren a)(he: Ren b): Ren (fun x=> a x*b x):= by intro i; simp_rw [PowerSeries.coeff_mul]; exact Decent.sums _ fun j _=> Decent.mul (h j.1) (he j.2)
lemma one : Ren (fun _=>(1:Cn)):= by intro i; simp_rw [PowerSeries.coeff_one]; split; convert Decent.const 1; norm_num; convert Decent.const 0; norm_num
lemma pow (h: Ren a)(i:ℕ): Ren (fun x=>a x ^ i):= by induction i with | zero=>simpa using one| succ i ih=>simpa [pow_succ] using ih.mul h
lemma inv (h:Ren a): Ren (fun x=>PowerSeries.invOfUnit (a x) 1):= by
   intro i; induction i using Nat.strong_induction_on with
   | _ i ih=> simp_rw [PowerSeries.coeff_invOfUnit i, inv_one,Units.val_one,neg_one_mul]; split
              · convert! Decent.const 1
              refine Decent.neg (Decent.sums (antidiagonal i) (fun j hj=>?_)) -- expected neg synt
              split
              next ht => exact Decent.mul (h j.1) (ih j.2 ht)
              next hh=> convert! Decent.const 0
lemma swath {A:Type}(V:A→ℝ→Cn)(hv:∀ i,Ren (V i))(l:List A): Ren (fun x=> (l.map fun k=>V k x).prod):= by
   induction l with| nil=>exact one| cons i l ih=>exact (hv i).mul ih
end Ren
abbrev Low (a:Cn):= coeff 0 a=1

structure Plan where
   waveA : Logarithm.Poly
   waveC : Logarithm.Poly
   coupling : Logarithm.Poly
abbrev Team:= ℕ→Plan

local notation "Q"=>Polynomial ℝ
def affirmative (x:T Q) (y:ℝ) : Cn:= PowerSeries.mk (fun k=>if k=0 then 1 else (((x k).eval y:ℝ):ℂ))
def opposite (x:T Q)(y:ℝ) : Cn:= PowerSeries.invOfUnit (affirmative x y) 1
def shift (P:Team)(y:ℝ): Cn:= PowerSeries.mk (fun k=> if k=0 then 0 else if k=1 then 1 else (((P k).coupling.eval y:ℝ):ℂ))
lemma share (P:Team)(y:ℝ) : Rooted (shift P y):= by simp only [Rooted,shift,PowerSeries.coeff_mk,if_true] -- reduce dec
lemma ann (P:Team)(y:ℝ): coeff 1 (shift P y)=1:= by rw [shift,PowerSeries.coeff_mk]; simp
lemma affirmativeRent (x:T Q): Ren (affirmative x):= by
    intro i; simp_rw [affirmative,PowerSeries.coeff_mk]; split; convert! Decent.const 1; exact ⟨_,Ready.got _,rfl⟩
lemma shiftR (P:Team): Ren (shift P):= by
    intro i; simp_rw [shift,PowerSeries.coeff_mk]; split; · convert! Decent.const 0
    split; convert! Decent.const 1; exact ⟨_,Ready.got _,rfl⟩
lemma v0 (a:T Q)(y:ℝ): Low (affirmative a y):= by rw [Low,affirmative,PowerSeries.coeff_mk]; rfl
lemma o0 (a:T Q)(y:ℝ): Low (opposite a y):= by simp [Low,opposite,PowerSeries.coeff_zero_eq_constantCoeff]
lemma pairs (a: T Q)(y:ℝ): affirmative a y * opposite a y =1:= by unfold opposite; apply PowerSeries.mul_invOfUnit; rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,v0]; rfl
end YM.MS.Book.Program
