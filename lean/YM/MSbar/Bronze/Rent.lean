import YM.MSbar.Bronze.Rust
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Bronze
open Function Filter Whisk Lis Measuring Cacao CrossH Push Uniform Lattice RG Pressure Matrix
open Precision Gauge Midpoint Rolling Tramp Exterior Tree Wilson Laurent Bloch Wave Tensor
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {σ:Type}[Fintype σ][DecidableEq σ]
local notation "X"=>Positions σ
local notation "H"=> Cacao.Pot σ
open MvPolynomial
variable (F: Cacao.Pot σ) (p:ℕ)(a b:ℝ)
local notation "ϕ"=> homogeneousComponent p F
lemma reassure (x:X):ϕ=ϕ ∧ clue ϕ (a • x)= a^p*clue ϕ x:=⟨rfl,hene a 0 x p F⟩
lemma jewels (L:List σ) : buoy (clue (homogeneousComponent p F)) 0 L= if L.length=p then buoy (clue F) 0 L else 0:=by
    have h(T:List σ)(q:ℕ)(hp:T.length ≠ q) : buoy (clue (homogeneousComponent q F)) 0 T=0:=by
       let v:= homogeneousComponent q F; let f:=clue v; let D:Positions σ→L[ℝ] Positions σ:= (2:ℝ) • ContinuousLinearMap.id ..
       let p:ℝ:= 2; let w:=T.map Uniform.bolt
       have hh : f ∘ D= p^q • f:=_root_.funext fun x=> hene 2 0 x q F
       have hf:ContDiff ℝ ω f:= helm ..; have hg: ContDiff ℝ ω (f∘ D):= hf.comp D.contDiff
       have he : buoy (f∘ D) 0 T=p^q*buoy f 0 T:=by unfold buoy; rw [hh]; exact wed w.length w _ _ (hf.contDiffAt.of_le le_top) le_rfl
       let W(x:Fin T.length):= bolt (T.get x); let h0 :=CrossH.chain f T w.length 0 (hf.contDiffAt.of_le le_top) (by simp [w]); have hv:iteratedFDeriv ℝ T.length f 0 W= buoy f 0 T:=h0.symm
       have hA(a): D (W a)=p • W a:=by dsimp only [D,p]; rw [_root_.smul_apply];rfl
       rw [CrossH.chain (f ∘ D) T w.length 0 (hg.contDiffAt.of_le le_top) (by simp [w]),D.iteratedFDeriv_comp_right hf 0 le_top,_root_.map_zero, ContinuousMultilinearMap.compContinuousLinearMap_apply] at he
       change iteratedFDeriv ℝ T.length f 0 (fun i=> D (W i)) = _ at he; simp_rw [hA] at he; rw [(iteratedFDeriv ℝ _ f 0).map_smul_univ (fun (_:Fin T.length)=>p) W,Finset.prod_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,hv] at he
       have hP:p^T.length≠p^q:=(pow_right_strictMono₀ (show 1<p from one_lt_two)).injective.ne hp; exact mul_eq_zero.mp (show (p^T.length-p^q)*buoy f 0 T=0 by rw [sub_mul,he,sub_self])|>.resolve_left (sub_ne_zero.mpr hP)
    split; next hv=>
       let n:=max F.totalDegree p
       have hm:p∈Finset.range (n+1):=Finset.mem_range.mpr (by unfold n; omega)
       have he:= Wave.buys n F (le_max_left ..)
       rw [CrossH.tours 0 ϕ L,CrossH.tours 0 F L]; nth_rw 2 [←he]; rw [_root_.map_sum,Finset.sum_eq_single_of_mem _ hm]; intro b hb hq; rw [←CrossH.tours]; exact h L b (by omega)
       -- use scored read.L + `map_sum` or Lis.tot.N instead add. avoid rw F inside
    next hl=> exact h L p hl
end YM.MSbar.Bronze
