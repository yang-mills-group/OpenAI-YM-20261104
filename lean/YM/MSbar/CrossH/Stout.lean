import YM.MSbar.CrossH.Faces
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.CrossH
open Function Filter Whisk Lis Measuring Cacao Push Uniform Lattice
open scoped Topology BigOperators ContDiff Classical
variable {σ ι β X:Type}[Fintype σ][DecidableEq σ][Fintype ι][DecidableEq ι][NormedAddCommGroup X][NormedSpace ℝ X]
open Polynomial MvPolynomial Matrix Rolling Work.G05
local notation "P"=> Cacao.Pot σ
local notation "Q"=>Positions σ
local notation "∆"=>PowerSeries.coeff
-- height homogeneous pricing must tie iterated proof. Li list stock
variable (F:Positions σ→ℝ) (p:ℕ) (t:List σ)
open Bakery
lemma budP (k:ℕ)(x:Q) (h:ContDiffAt ℝ k F x)(he:t.length≤k): buoy F x t= glance F t x:=by
   induction t generalizing F k with
   | nil=>rfl
   | cons i l ih=>
      unfold buoy; rw [List.map_cons,takeG k h]; have hh : Uniform.bolt i=(Pi.single i 1:View σ):=by ext j; by_cases hz:j=i <;> simp [bolt,hz]
      -- rw [hh] only direction
      have hv : glance F [i]= (fun y=>fderiv ℝ F y (bolt i)):= by funext y; unfold glance; rw [hh]; rfl
      rw [← hv]; exact ih (glance F [i]) l.length (glow [i] h (by simpa using he)) le_rfl; rw [List.length_map]; simp only [List.length_cons] at he;omega
lemma chain(k:ℕ)(x:Q)(h:ContDiffAt ℝ k F x)(he:t.length≤k):buoy F x t=iteratedFDeriv ℝ t.length F x (fun i=>Uniform.bolt (t.get i)):=by
    rw [budP F t k x h he,Bakery.glance_read t h he]; congr 1; funext i; let j:= t.get i; change (Pi.single j 1:View σ)=bolt j; ext k; by_cases hz:k=j<;> simp [bolt,hz]
-- homog.Line.Trans
local notation "f₀"=>potter F p
lemma ports (h:ContDiffAt ℝ p F 0) (hp:p≠0) (L:List σ)(ht:L.length≠0) : buoy (clue (potter F p)) 0 L= if L.length=p then buoy F 0 L else 0 :=by
    obtain ⟨p,rfl⟩:= Nat.exists_eq_succ_of_ne_zero hp; let f:=potter F (p+1)
    have he: clue f= blockTaylor (p+1) F-blockTaylor p F:=by funext x; unfold blockTaylor; rw [Finset.sum_range_succ (n:=p+1),Pi.sub_apply, Finset.sum_apply]; rw [Pi.add_apply,Finset.sum_apply,add_sub_cancel_left]; exact pots ..
    have hb(i:ℕ): ContDiffAt ℝ (L.length:ℕ∞ω) (blockTaylor i F) 0:=(blockTaylor_contDiff ..).contDiffAt
    by_cases hh:L.length ≤ p
    · have hx:L.length ≤ p+1:= by omega
      rw [if_neg (by omega),chain _ L L.length 0 ((helm f _).contDiffAt) le_rfl, show clue _=_ from he, iteratedFDeriv_sub_apply (hb _) (hb _), blockTaylor_jets h _ hx, blockTaylor_jets (h.of_le (m:=p) (by exact_mod_cast Nat.le_succ p)) _ hh,sub_self,_root_.zero_apply]
    by_cases hx:L.length=p+1
    · let g:=potter F p
      let M:=∑ i∈Finset.range (p+1),potter F i
      have hv:M.totalDegree ≤ p:= MvPolynomial.totalDegree_finsetSum_le fun i hi=> (potsD ..).trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
      have hM: clue M= blockTaylor p F:=by funext x; unfold M clue; rw [_root_.map_sum,blockTaylor,Finset.sum_apply]; exact Finset.sum_congr rfl fun i hi=> pots ..
      have hk:buoy (blockTaylor p F) 0 L=0:= by rw [←hM,tours]; exact Bakery.blank_list (x:=0) M _ (hv.trans_lt (by omega))
      rw [if_pos hx,chain _ L L.length 0 ((helm f _).contDiffAt) le_rfl, chain _ L _ 0 h hx.le,show clue _=_ from he,iteratedFDeriv_sub_apply (hb _) (hb _),blockTaylor_jets h _ hx.le]; rw [chain (blockTaylor _ _) L L.length 0 (hb p) le_rfl] at hk; rw [_root_.sub_apply,hk,sub_zero]
    rw [if_neg hx,tours]; exact Bakery.blank_list (x:=0) f _ ((potsD F _).trans_lt (by omega))
end YM.MSbar.CrossH
