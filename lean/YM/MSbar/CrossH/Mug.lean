import YM.MSbar.Bakery.Glance
import YM.MSbar.Lis.Meadows
import YM.MSbar.Whisk.Room
import YM.MSbar.Lis.Colors
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.CrossH
open Function Filter Whisk Lis Measuring Cacao Push Uniform Lattice
open scoped Topology BigOperators ContDiff Classical
variable {σ ι:Type}[Fintype σ][DecidableEq σ]
open Polynomial MvPolynomial
local notation "P"=> Cacao.Pot σ
local notation "X"=> Positions σ
variable (x:Positions σ)(p: Pot σ)(j:σ)
noncomputable def clue(p:Pot σ) (x:Positions σ):= MvPolynomial.eval x p
lemma helm (p: Pot σ)(n:WithTop ℕ∞) : ContDiff ℝ n (clue p) := (Cacao.vent p).of_le le_top
lemma tabs : fderiv ℝ (clue p) x (bolt j)= clue (pderiv j p) x:= by rw [show bolt j=(Pi.single j 1:X) by ext i; by_cases hi:i=j <;> simp [bolt,hi]]; exact congr_fun (Bakery.TonD j p) x
lemma tours (l:List σ): buoy (clue p) x l= Whisk.read x l p:=by
    induction l generalizing p with
    | nil=>rfl
    | cons i l ih=> rw [read_next]; rw [← ih]; unfold buoy; rw [List.map_cons,takeG _ (helm p (↑(l.length+1:ℕ))).contDiffAt _ _ (by simp)]; congr; ext x; exact tabs ..
-- rank seminorm
variable {n:Side}{l:σ→ Site n}{a b t w:ℝ}{m k s:ℕ}
noncomputable def cog (l:σ→Site n)(a:ℝ)(s:ℕ)(p:Pot σ)(k:ℕ)(i:σ):=lump l {l i} a s k 0 (MvPolynomial.pderiv i p)
lemma scored (i:σ) : Yarn k (fun T:List σ=>|buoy (clue p) 0 (i::T)| *swipe l a s (i::T))=cog l a s p k i:=by
    refine stitch _ fun T _=>?_ ; rw [tours]; rw [mul_comm]; exact tasteful ..
lemma pressed (i:ℕ)(l:σ→Site n)(s:ℕ)(a:ℝ) (p:Pot σ)(C:ℝ)(w:ℝ)(hc:0<w): JetTab l a s w {0} (clue p) i C ↔ 0 ≤ C∧∀ j:σ,cog l a s p i j ≤ C/w^(i+1):=by
    constructor
    · intro h; refine ⟨h.1,fun j=>?_⟩; rw [← scored]; exact h.count hc _ (Set.mem_singleton 0) _
    intro ⟨hp,ht⟩; exact JetTab.grant (fun j=> (scored p j).trans_le (ht j)) hp hc
lemma token : Tokew l a s m 0 p b ↔ 0 ≤ b ∧ ∀ j≤ m,∀ i:σ,cog l a s p j i≤ b:=by
    constructor; intro h; exact ⟨h.1,fun j hj i=> h.2 i|>.2 j hj⟩; intro ⟨hp,h⟩; exact ⟨hp,fun i=>⟨hp,fun j hj=>h j hj i⟩⟩
lemma whole (h:p.totalDegree ≤ m+1) : ∀ N>m,∀ i:σ,cog l a s p N i=0 :=by
    intro N hN i; rw [← scored,_root_.eq_comm]; apply le_antisymm; exact luster N (fun v _=> mul_nonneg (abs_nonneg _) (effect ..|>.le)); rw [←spool (A:=ℝ) (ι:=σ) N]; apply shiny; intro t ht; rw [tours]; have hp: read (0:View σ) (i::t) p=0:= Bakery.blank_list p _ (by simp only [List.length_cons,ht]; omega)
    rw [hp,abs_zero,zero_mul]
lemma pieceC (p:Pot σ)(i:σ) (he:p=p):0 ≤ cog l a s p k i:=Whisk.lump.nonneg ..
end YM.MSbar.CrossH
