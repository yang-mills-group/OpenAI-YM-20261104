import YM.MSbar.CrossH.Stout
import YM.MSbar.Bout.Depart
import YM.MSbar.Chord.Fig

/-! Absolute rooted rows of the emitted polynomial pay its ordinary derivative
operator norm without any factor for the number of coordinates. The same
polynomial also admits independent base points for every derivative word. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Finset Lattice MSbar MSbar.Whisk MSbar.Lis MSbar.Cacao MSbar.CrossH
open MSbar.Bakery Push.Uniform Planned.AtomRegular AnalyticBridge.SectorAffine.Offset
open scoped Classical Topology BigOperators ContDiff
variable {σ : Type} [Fintype σ]

theorem word_function_sum (q : ℕ) (f : List σ → ℝ) :
    Yarn q f = ∑ v : Fin q → σ,f (List.ofFn v) := by
  induction q generalizing f with
  | zero => simp [Yarn]
  | succ q ih =>
    rw [twilled,← (Fin.consEquiv fun _ : Fin (q+1)=>σ).sum_comp,Fintype.sum_prod_type]
    apply sum_congr rfl
    intro i _
    rw [ih]
    apply sum_congr rfl
    intro v _
    change f (i :: List.ofFn v) = f (List.ofFn (Fin.cons i v))
    rw [List.ofFn_cons]

theorem vaulted_operator [DecidableEq σ] {n : Side} (site : σ → Site n) (W : Finset (Site n))
    {a B : ℝ} (ha : 0 ≤ a) (s k : ℕ) (x : View σ) (F : Pot σ)
    (vault : Vault site W a s k x F B) : Through k (clue F) x B := by
  refine ⟨(helm F k).contDiffAt,?_⟩
  intro j jk
  let T:=iteratedFDeriv ℝ j (clue F) x
  have onList (l : List σ) (h : l.length=j) :
      Whisk.read x l F = T (fun i=>bolt (l.get (i.cast h.symm))) := by
    subst j
    rw [←tours x F]
    exact CrossH.chain (clue F) l l.length x (helm F l.length).contDiffAt le_rfl
  have entries (v : Fin j → σ) : T (fun i=>bolt (v i)) = Whisk.read x (List.ofFn v) F := by
    simpa using (onList (List.ofFn v) (by simp)).symm
  apply op_le_of_unit vault.1
  intro w hw
  let g (i:Fin j) (u:σ):=w i u • bolt u
  have expand : w=fun i=>∑ u,g i u := funext fun i=>spiral _
  change ‖T w‖ ≤ B
  rw [expand,T.map_sum g]
  apply (norm_sum_le ..).trans
  apply le_trans _ (vault.2 j jk)
  rw [lump,word_function_sum]
  apply sum_le_sum
  intro v _
  change ‖T (fun i => w i (v i) • bolt (v i))‖ ≤ rate site W a s x F (List.ofFn v)
  rw [T.map_smul_univ,entries,norm_smul,Real.norm_eq_abs,Finset.abs_prod,Real.norm_eq_abs]
  have small : (∏ i,|w i (v i)|) ≤ 1 := Finset.prod_le_one (fun _ _=>abs_nonneg _) fun i _=>
    (show |w i (v i)| ≤ ‖w i‖ from (Real.norm_eq_abs _ ▸ norm_le_pi_norm (w i) (v i))).trans (hw i)
  exact mul_le_mul_of_nonneg_right (small.trans (w_start ha s _)) (abs_nonneg _)

theorem field_independent_backgrounds [DecidableEq σ] {n : Side} (site : σ → Site n) (W : Finset (Site n))
    {a B D : ℝ} (ha : 0 ≤ a) (hD : 0 ≤ D) (s d : ℕ) (x : View σ) (F : Pot σ)
    (degree : F.totalDegree ≤ d) (vault : Vault site W a s d x F B) (q : ℕ) :
    Phase site W a s q (clue F) (Metric.closedBall x D) (B*(1+D)^(d+1)) :=
  spice_fund ha degree vault hD q

end YM.Integration.FVA1Physical.Round2.Curvature
