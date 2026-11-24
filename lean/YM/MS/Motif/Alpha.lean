import YM.MS.Motif.Shift
import YM.MS.Motif.Sync

set_option autoImplicit false
noncomputable section
namespace YM.MS.Motif
open Set Filter Function Finset MeasureTheory Metric Real
open Plane Koszul Heat Flux Landau Arts Native Book Convolve
open Literal
open scoped Topology ContDiff InnerProductSpace
variable {G:Gauge} {n:ℕ} {z:ℂ} {F H:Mield G n}
local notation "S"=> field ( Landau.parity ( A:=Arts.L n ) (C:=G.ColorIndex))
lemma vect_sym (i:G.ColorIndex)(he:∀ i,Symm S (F i))(hv:∀ i,Symm S (H i)): Symm S (jaw G n F H i):= by rw [chew]; exact Symm.sum _ fun j _=> Symm.sum _ fun k _=> ( ( he j ).times (hv k ) ).smul _
lemma Cur_sym (a b:Arts.L n)(z:ℂ)(i:G.ColorIndex): Symm S (cur z a b i):= by apply (mono_sym a b i).add; exact (vect_sym _ (fun i=> note_sym ( at_g a i ) (fun _:SectorP n=> (1:ℂ))) (fun i=> note_sym ( at_g b i ) (fun _: SectorP n=> (1:ℂ))) ).smul z -- cur ... fails defeq
lemma valuedZ {I:Type}[AddCommGroup I][Module ℂ I](x:Box I)(K:I→ₗ[ℂ] ℂ)(hp:∀ z,K (value I z x)=0)(n:ℕ): K ( linear I x n ) = 0 := by
   have hh (i k:ℕ)(a:ℂ) : iteratedDeriv k (fun z:ℂ=> z^i • a) 0= if k=i then (i.factorial:ℂ)*a else 0:= by rw [ iteratedDeriv_smul_const (by fun_prop), iteratedDeriv_fun_pow_zero ]; split; rfl; simp
   by_cases ht:n∈ x.support; swap; · rw [hiss, Finsupp.notMem_support_iff.mp ht,map_zero]
   obtain H := congr_arg ( fun f:ℂ→ℂ=> iteratedDeriv n f 0 ) ( funext hp ); simp only [ valued,map_sum,map_smul] at H; rw [ iteratedDeriv_fun_sum, Finset.sum_eq_single_of_mem n ht] at H; · rw [hh, if_pos rfl, iteratedDeriv_const] at H; exact (mul_eq_zero.mp ((by simp_all : (n.factorial:ℂ) * K (x n)=0))).resolve_left (by exact_mod_cast Nat.factorial_ne_zero n)
   · intro i hi he; rw [hh,if_neg (Ne.symm he)]
   intro t _; fun_prop
end YM.MS.Motif
