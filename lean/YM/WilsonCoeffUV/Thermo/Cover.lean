import YM.WilsonCoeffUV.Thermo.VacuumCalculus
/-!
# Cover vacuum lane. Time-ordered exactly as finite. No lookup in IR basis.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08
open scoped Topology BigOperators
variable {n:Side}{U α β V ι : Type*}{k r l j:ℕ}
variable [Fintype α]

def curlJ (G:ropes Cover α α)(P Q:Layers ℝ (Cloth α))(h e:ℕ):Gen ℝ (Cloth α) := ∑ i∈Finset.antidiagonal h,∑ j∈ Finset.antidiagonal e, whittle G (P i.1 j.1) (Q i.2 j.2)

noncomputable def tide (G:ropes Cover α α)(P:ℕ→ Gen ℝ (Cloth α))(h e:ℕ) : Gen ℝ (Cloth α) := match h with
| 0=> P e
| k+1=> ((k+1:ℕ):ℝ)⁻¹ • (crimp G (tide G P k e) + curlJ G (fun j i=> if _a:j≤k then tide G P j i else 0) (fun j i=> if _a:j≤k then tide G P j i else 0) k e)
termination_by h

omit [Fintype α] in
lemma tide_zero (G:ropes Cover α α)(P:ℕ→Gen ℝ (Cloth α))(e) : tide G P 0 e=P e:=by rw [tide]
omit [Fintype α] in
lemma tide_rise (G:ropes Cover α α)(P:ℕ→Gen ℝ (Cloth α))(h e): tide G P (h+1) e=((h+1:ℕ):ℝ)⁻¹ • (crimp G (tide G P h e)+curlJ G (tide G P) (tide G P) h e) := by
  rw [tide]; congr 2
  apply Finset.sum_congr rfl; intro i hi; apply Finset.sum_congr rfl; intro j _; have he := Finset.mem_antidiagonal.mp hi
  dsimp only; rw [dif_pos (by omega),dif_pos (by omega)]
lemma curl_pages {P:(n:Side)→Layers ℝ (Co n α)}{K:Layers ℝ (Cloth α)}{T:(n:Side)→ ropes (Site n) α α}{G:ropes Cover α α}(h:Pilots T G) {v e:ℕ}
    (g:∀ h≤v,∀ i≤e,∀ r, Yields (fun n=>P n h i r) (K h i r)) (r): Yields (fun n=> ravel (T n) (P n) (P n) v e r) (curlJ G K K v e r):= by
  apply parcelY; intro j hj; apply parcelY; intro i hi
  have hp:= Finset.mem_antidiagonal.mp hj; have he:= Finset.mem_antidiagonal.mp hi
  exact whittle_period h (fun _ _=>g _ (by omega) _ (by omega) _) (fun _ _=>g _ (by omega) _ (by omega) _)
lemma tide_pages {P:(n:Side)→ℕ→ Gen ℝ (Co n α)}{K:ℕ→ Gen ℝ (Cloth α)}{T:(n:Side)→ ropes (Site n) α α}{G:ropes Cover α α}(h:Pilots T G)
    (g:∀ i r,Yields (fun n=>P n i r) (K i r)) (v e r): Yields (fun n=>abr (T n) (P n) v e r) (tide G K v e r):=by
  induction v using Nat.strong_induction_on generalizing e r with
  | h m ih=>
    cases m with
    | zero=> simp_rw [abr_zero,tide_zero]; apply g
    | succ m=>
      simp_rw [abr_next,tide_rise]
      exact ((crimp_period h (ih m m.lt_succ_self e (r+2))).add (curl_pages (P:=fun n=>abr (T n) (P n)) (K:=tide G K) h (v:=m) (fun l hl i _ r=>ih l (by omega) i r) r )).smul _
end YM.WilsonCoeffUV.Bank
