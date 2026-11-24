import YM.FVA2.Gen.Around
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
/-! # Real smooth (not analytic) permutation of jets -/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.Gen
open Function Set Finset Equiv Filter Topology
open scoped ContDiff Classical BigOperators
universe u
variable {α β:Type*}[DecidableEq α][DecidableEq β]
private lemma swap_emb {f:α→β}(hf:Injective f)(a b i :α): Equiv.swap (f a) (f b) (f i)= f (Equiv.swap a b i):= by
    by_cases h:i=a
    · rw [h]; simp
    by_cases k:i=b
    · rw [k]; simp
    exact ( swap_apply_of_ne_of_ne (fun e=>h (hf e)) (fun e=>k (hf e)) ).trans (congrArg f ( ( swap_apply_of_ne_of_ne h k ).symm ))
-- Universe max = same
variable {E F : Type u}[NormedAddCommGroup E][NormedAddCommGroup F][NormedSpace ℝ E][NormedSpace ℝ F]{f:E→ F}{x:E}{n:ℕ}
private lemma younger (h:ContDiffAt ℝ (n+1:ℕ) f x)(i:Fin n)(v:Fin (n+1) → E): iteratedFDeriv ℝ (n+1) f x (v ∘ Equiv.swap i.castSucc i.succ)=iteratedFDeriv ℝ (n+1) f x v:=by
    induction n generalizing F x with
    | zero=> exact i.elim0
    | succ n ih=>
        cases i using Fin.cases with
        | zero=> cases n with
           | zero=>
              change iteratedFDeriv ℝ 2 f x (v ∘ Equiv.swap (0:Fin 2) 1)=iteratedFDeriv ℝ 2 f x v
              simp only [iteratedFDeriv_two_apply, Function.comp_apply, swap_apply_left,swap_apply_right]
              exact h.isSymmSndFDerivAt (by norm_num) _ _
           | succ n=>
              -- shift avoiding last slot (n+3)
              let k:ℕ:= n+1; let x₀:Fin k:=⟨0,Nat.succ_pos _⟩; let X:=Equiv.swap x₀.castSucc x₀.succ; let Y:=Equiv.swap x₀.castSucc.castSucc x₀.succ.castSucc
              change iteratedFDeriv ℝ (k+1+1) f x ( v ∘ Y )=_; rw [iteratedFDeriv_succ_apply_right,iteratedFDeriv_succ_apply_right v]; have he : Fin.init (v ∘ Y) = Fin.init v ∘ X := by funext l; exact congrArg v ( swap_emb (Fin.castSucc_injective _) x₀.castSucc x₀.succ l )
              rw [he, show (v ∘ Y) (Fin.last _)=v (Fin.last _) from congrArg v ( swap_apply_of_ne_of_ne (Fin.castSucc_ne_last _).symm (Fin.castSucc_ne_last _).symm ) ]; exact congrArg (fun a:E→L[ℝ] F=> a (v (Fin.last _))) ( ih (x:=x) (f:=fderiv ℝ f) (h.fderiv_right (by push_cast; exact le_rfl)) x₀ (Fin.init v) )
        | succ i=>
            let k:= n+1; let Y:=Equiv.swap i.castSucc.succ i.succ.succ; let X:=Equiv.swap i.castSucc i.succ; rw [show i.succ.castSucc=i.castSucc.succ from rfl]; change iteratedFDeriv ℝ (k+1) f x (v ∘ Y)=_; have ht:= h.differentiableAt_iteratedFDeriv (m:=k) (show (k:WithTop ℕ∞) < ↑(n+1+1:ℕ) by exact_mod_cast k.lt_succ_self); rw [ht.iteratedFDeriv_succ_apply_left', ht.iteratedFDeriv_succ_apply_left', comp_apply, show Y 0=0 from ( swap_apply_of_ne_of_ne (Fin.succ_ne_zero _).symm (Fin.succ_ne_zero _).symm ), show Fin.tail (v ∘ Y)= Fin.tail v∘X from funext fun j=> congrArg v ( swap_emb (Fin.succ_injective _) _ _ _ ), (show ( fderiv ℝ ( fun y:E=> iteratedFDeriv ℝ k f y ( Fin.tail v ∘ X ) ) x ) = ( fderiv ℝ (fun y=>iteratedFDeriv ℝ k f y (Fin.tail v)) x ) from ?_)]; exact Filter.EventuallyEq.fderiv_eq ( (h.eventually (by simp)).mono ( fun y hy=> ih ( hy.of_le (mod_cast k.le_succ) ) _ _ ) )
-- then by compositions of adjacent swaps.
theorem perm_fee (h:ContDiffAt ℝ (n:ℕ) f x)(v:Fin n→ E)(p: Perm (Fin n)): iteratedFDeriv ℝ n f x (v∘p)=iteratedFDeriv ℝ n f x v:=by
    cases n with
    | zero=> rfl
    | succ n=>
        let G:=(iteratedFDeriv ℝ (n+1) f x)
        let D: Type:=Fin (n+1)
        let S: Submonoid (Perm D):= { carrier:={ f|∀ v:D→E, G (v∘f) = G v }, one_mem':= fun _=>rfl, mul_mem':=by rintro a b (ha:∀ v:D→E,G (v∘a)=G v) (hb:∀ v:D→E,G (v∘b)=G v) v; exact (hb (v∘a)).trans (ha v) }
        have hx: p∈ S:=by apply ( show ⊤ ≤ S from ?_ ) ( Submonoid.mem_top _ ); rw [ ← Equiv.Perm.mclosure_swap_castSucc_succ, Submonoid.closure_le ]; rintro _ ⟨i,rfl⟩ v; exact younger h i v
        exact (show ∀ w:D→E, _ from hx) v
end YM.FVA2.Gen
