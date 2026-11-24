import YM.Integration.WilsonPointChildNamedRootSum
import YM.WilsonCoeffUV.Marked.Capture.Draw
import YM.Integration.WilsonPointChildPlacedFold
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPointChildFoldedPageIncome
open YM Lattice WilsonCoeffUV RG FormalBulk08 Laurent
open WilsonCoeffUV.Bank WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Bank.Mosaic
open Work.F08 Function Finset Filter
open scoped Classical BigOperators Topology
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Winding
variable {ι α V A X Y:Type} [NormedAddCommGroup V]

theorem group [Fintype A] [DecidableEq A] (π:X → A)(K:X → V)(R:X → ℝ)(a:A → ℝ)(hp:∀x,1 ≤ R x)
    (pos:∀j,0 ≤ a j)(contract:∀x,a (π x) ≤ R x)(sum:Summable (fun x=>R x*‖K x‖)):
    (∑j,a j*‖∑' x, if π x=j then K x else 0‖) ≤ ∑' x,R x*‖K x‖:=by
  classical
  let w(x:X):=R x*‖K x‖
  have wp(x:X):0≤w x:=mul_nonneg (zero_le_one.trans (hp x)) (norm_nonneg _)
  have kn: Summable (fun x=>‖K x‖):=sum.of_nonneg_of_le (fun _=>norm_nonneg _) (fun x=>le_mul_of_one_le_left (norm_nonneg _) (hp x))
  let v(j:A)(x:X):=if π x=j then K x else 0
  let f(j:A)(x:X):=if π x=j then w x else 0
  have fn(j:A):Summable (f j):=sum.of_nonneg_of_le (fun x=>by dsimp [f];split;exact wp x;exact le_rfl) (fun x=>by dsimp [f];split;exact le_rfl;exact wp x)
  have vn(j:A):Summable (fun x=>‖v j x‖):=kn.of_nonneg_of_le (fun _=>norm_nonneg _) (fun x=>by dsimp [v];split<;>simp)
  have one(j:A):a j*‖∑' x,v j x‖ ≤ ∑' x,f j x:=by
    calc _ ≤ a j*(∑' x,‖v j x‖):=mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm (vn j)) (pos j)
         _ = ∑' x,a j*‖v j x‖:=(tsum_mul_left ..).symm
         _ ≤ ∑' x,f j x:=((vn j).mul_left _).tsum_le_tsum (fun x=>by
             by_cases h:π x=j
             · simp only [v,f,w,if_pos h];rw [←h];exact mul_le_mul_of_nonneg_right (contract x) (norm_nonneg (K x))
             · simp [v,f,h]) (fn j)
  apply (Finset.sum_le_sum (fun j _=>one j)).trans_eq
  rw [← Summable.tsum_finsetSum (fun j _=>fn j)]
  apply tsum_congr
  intro x
  simp [f,w]

theorem original [Fintype A][DecidableEq ι][Fintype α][DecidableEq α]
    (I:Finset ι)(o:ι)(x₀:Cover)(r:ℕ)(n:Side)(lifted:A → (I.erase o) → Cover)(inj:Injective lifted)
    (K:(ι → Cover) → dock Cover α r → V){w M:ℝ}(hw:0≤w)
    (paid:SumBudget (fun f:Fence α I o r=>
      let p:=toe I o x₀ f.1
      Real.exp (w*Syn terrain p I f.2)*‖K p f.2‖) M):
    (∑j,∑x,let p:=toe I o x₀ (lifted j)
      Real.exp (w*Syn (tor n) (wrap n ∘ p) I x)*‖plume (K p) n x‖) ≤ M:=by
  let U(j:A):=toe I o x₀ (lifted j)
  let f (q:Fence α I o r):=Real.exp (w*Syn terrain (toe I o x₀ q.1) I q.2)*‖K (toe I o x₀ q.1) q.2‖
  let ψ(q:A×dock Cover α r):Fence α I o r:=(lifted q.1,q.2)
  have unique:Injective ψ:=by
    rintro ⟨p,x⟩ ⟨q,y⟩ h
    have eq:(lifted p,x)=(lifted q,y):=h
    exact Prod.ext (inj (Prod.mk.inj eq).1) (Prod.mk.inj eq).2
  have all:Summable (f ∘ ψ):=paid.2.1.comp_injective unique
  have cost:tsum (f ∘ ψ) ≤ M:=(tsum_comp_le_tsum_of_inj paid.2.1 paid.1 unique).trans paid.2.2
  have step(j:A):
      (∑x,Real.exp (w*Syn (tor n) (wrap n ∘ U j) I x)*‖plume (K (U j)) n x‖) ≤
      ∑' x,f (ψ (j,x)):=by
    have applyGroup:=group (slideC n) (K (U j)) (fun x=>Real.exp (w*Syn terrain (U j) I x))
      (fun x=>Real.exp (w*Syn (tor n) (wrap n ∘ U j) I x))
    have lp(x:dock Cover α r):1≤Real.exp (w*Syn terrain (U j) I x):=
      Real.one_le_exp (mul_nonneg hw (Nat.cast_nonneg _))
    have cp(x:dock Cover α r):Real.exp (w*Syn (tor n) (wrap n ∘ U j) I (slideC n x))≤Real.exp (w*Syn terrain (U j) I x):=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (coast (n:=n) (U j) I x)) hw)
    have done:=applyGroup lp (fun x=>(Real.exp_pos _).le) cp (all.prod_factor j)
    simpa only [plume,peglet,ψ,f,U] using done
  apply (Finset.sum_le_sum (fun j _=>step j)).trans
  have pair:∑j,∑' x,f (ψ (j,x))=tsum (f ∘ ψ):=by rw [all.tsum_prod,tsum_fintype];rfl
  exact pair.le.trans cost

end YM.Integration.WilsonPointChildFoldedPageIncome
