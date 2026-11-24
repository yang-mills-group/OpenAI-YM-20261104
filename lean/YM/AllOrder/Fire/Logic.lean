import YM.AllOrder.Fire.Device
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Fire
open Function Finset Laplace.SigmaP PositionX.Jet PertExtension PertExtension.Series PositionX.Gauss Radial MeasureTheory Response Module
open scoped Topology ContDiff BigOperators Classical
variable {X:Type} [NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X] (x:X)
variable {u v w:Book X}
local infix:65 "+#" => alters
omit [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] in
lemma calor [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]  (_h:u 0=0): LOG (EXP u)=u:= by funext k x; exact congr_fun (log_expS (swap u x)) k
omit [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] in
lemma exponent_of [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]  (h:∀ x: X, 0< u 0 x) : EXP (LOG u)=u:= by
 funext k x; let v:= swap u x; have hc:= Act.swell v (show k ≤ k from le_rfl); have hp : 0<v 0:= h x
 have hx:= (hc.transit (m:=Real.log) (Real.contDiffAt_log.mpr hp.ne')).transit (m:=Real.exp) Real.contDiff_exp.contDiffAt
 exact (Act.realizes (show Real.exp ∘ Real.log ∘ delay v k=ᶠ[𝓝 0] delay v k from (hc.nice.continuousAt.eventually (lt_mem_nhds (hp.trans_eq hc.zero.symm))).mono (fun i hi=> Real.exp_log hi)) hx).trans_at hc le_rfl
lemma exponent_inv (h:u 0=(1:X→ℝ)): EXP (LOG u)=u:= exponent_of fun i=> by rw [h]; exact zero_lt_one
omit [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] in
lemma wins [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]  (h:u 0=0): EXP u 0=1:= funext fun x=> (show run Real.exp (swap u x) 0=1 from (run_zero ..).trans (by rw [swap,h]; exact Real.exp_zero))
omit [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] in
lemma fades [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]  (h:u 0=1): LOG u 0=0:= funext fun x=> (show run Real.log (swap u x) 0=0 from (run_zero ..).trans (by rw [swap,h]; exact Real.log_one))
lemma ration (h:Clear u)(j:ℕ):
  (↑(j+1).factorial:ℝ)⁻¹ • slope x (energy u (j+1)) = slope x u +# (((j.factorial:ℝ)⁻¹) • energy u j) := by
 rw [alt_smul, slope_rate x h, smul_smul]; apply congr_arg (· • _); rw [Nat.factorial_succ]; push_cast; field_simp
omit [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] in
private lemma congr_cost [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]  {n:ℕ}(h:∀ i ≤ n,v i=w i): (u+#v) n=(u+#w) n:= by rw [aligned,aligned]; exact Finset.sum_congr rfl fun i hi=> by rw [h _ (by omega)]
lemma charges_log (h:Clear u)(hu:u 0=0) : slope x (EXP u)= (EXP u) +# slope x u:= by
 let F i:= ((i.factorial:ℝ)⁻¹) • energy u i
 let G n:=arrow (fun j=>(j.factorial:ℝ)⁻¹) u n
 have hf i : Clear (F i):= (Clear.charge (square_p h i) _); let v:= slope x u
 have ht (n:ℕ): G n=∑ i∈ Finset.range (n+1),F i:=rfl
 have hr (n:ℕ) : slope x (G (n+1))= v+# G n:= by
   rw [ht,ht, totals x _ (fun i _=> hf i),Finset.sum_range_succ', show slope x (F 0)=0 from ?_,add_zero, alt_sum]; swap;
   · simp only [F, Nat.factorial_zero,Nat.cast_one,inv_one,one_smul,level]; ext1 i -- cases
     by_cases hi:i=0; rw [hi]; exact dift 1 x; change diff' x (wirings (fun _=>1) i)=_; rw [show _ from (show wirings (fun (_:X)=>1) i=(fun _=>0) from funext fun x=>if_neg hi)]; exact dift 0 x
   apply Finset.sum_congr rfl; intro j _; exact (collect x _ (u:=energy u (j+1)) (square_p h _)).trans (ration x h j)
 rw [commute (EXP u)]; ext1 k; unfold slope; rw [Expo hu (Nat.le_succ k)]; refine (congr_fun (hr k) k).trans (congr_cost (fun i hi=> (Expo hu hi).symm)) -- slope notation
end YM.AllOrder.Fire
