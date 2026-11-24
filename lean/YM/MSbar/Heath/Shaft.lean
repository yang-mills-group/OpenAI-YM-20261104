import YM.MSbar.Heath.Far
import YM.MSbar.LocalSD.Escrow
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Heath
open Lattice Wilson RG Function Filter MeasureTheory Push.Local Push Push.AbsoluteSums
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{n:Side}{U V:Config G n}{x:Site n}{R:Rep G n}
variable {k:ℕ}(q:ℕ→Atom G k)(p:BudgetPoint)(j:Site n){σ C Λ δ w:ℝ}(hx:Stab x U V)
open Finset
include hx
set_option maxHeartbeats 600000 in
lemma rained (h:0<σ)(hg:SumBudget (fun i=> (q i).budget σ) C) (i:ℕ):  |(q i).placed p U j - (q i).placed p V j| ≤ (q i).budget σ*p.threshold^k*(2*Real.exp (σ*8)*Real.exp (-σ*separation x j)):=by
   let f i W:=(q i).placed p W j; have hh: Dominated f:= PathData.atom_dominated q p j h hg; let g i:=Real.exp (σ*(q i).length); let t:=p.threshold^k;let c:=2*Real.exp (σ*8)*Real.exp (-σ*separation x j); have ha:0≤c:=by unfold c; positivity
   have ht:0≤t:=pow_nonneg p.threshold_pos.le _
   change _ ≤ (q i).budget σ*t*c
   have he(i:ℕ) : |f i U-f i V|≤ (q i).budget σ*t*c:=by
      by_cases hb: x∉inspected ((q i).footprint j)
      · rw [show f i U=f i V from ConnectedActivityE6.Raw.placed_local _ _ _ U V (hx _ hb),sub_self,abs_zero]; exact mul_nonneg (mul_nonneg (hg.1 _) ht) ha
      obtain ⟨y,hy,hf⟩:=halo_spec.mp (Next.Scheduling.flag_layer ((q i).footprint j) (not_not.mp hb)); rw [Paths.atom_foot] at hy
      have hz : separation x j ≤ (q i).length+8 :=by rw [separation_comm x]; exact (separation_triangle j y x).trans (Nat.add_le_add (Paths.where_slot j _ _ hy) hf)
      have hi:σ*↑(separation x j) ≤ σ* ((q i).length+8):= mul_le_mul_of_nonneg_left (by exact_mod_cast hz) h.le
      have hG : 1 ≤ g i*Real.exp (σ*8)*Real.exp (-σ*separation x j):=by unfold g; rw [← Real.exp_add, ← Real.exp_add]; apply Real.one_le_exp; linarith only [hi]
      have hH (T:Config G n) := healthy_atom (q i) p T j; let m:=(q i).magnitude
      have hM:0≤ m:= by unfold m Atom.magnitude; positivity
      refine (abs_sub _ _).trans ((add_le_add (hH _) (hH _)).trans ((le_mul_of_one_le_right (show 0≤ m*t+m*t from add_nonneg (mul_nonneg hM ht) (mul_nonneg hM ht)) hG).trans_eq ?_)); unfold g t c m Atom.budget; ring
   exact he i
omit hx in
lemma cherished {a':ℝ}  (f g u:ℕ→ℝ)(ha:Summable f)(hb:Summable g)(he:SumBudget u a')(hv:∀ i,|f i-g i|≤ u i) : |(∑' i,f i) -∑' i,g i| ≤ a':=by
   have hp : Summable (fun i=> ‖f i-g i‖):= he.2.1.of_nonneg_of_le (fun i=> norm_nonneg (f i-g i)) hv
   let F : ℕ→ℝ:=fun i=> f i-g i
   rw [← ha.tsum_sub hb]; change ‖∑' i,F i‖ ≤ _; exact (norm_tsum_le_tsum_norm (f:=F) hp).trans ((hp.tsum_le_tsum (fun i=> show ‖F i‖ ≤ u i from hv i) he.2.1).trans he.2.2)
lemma atomic (h:0<σ)(hg:SumBudget (fun i=> (q i).budget σ) C) : |RG.PathData.atomSeries q p U j -RG.PathData.atomSeries q p V j| ≤ (C*p.threshold^k)*(2*Real.exp (σ*8)*Real.exp (-σ*separation x j)):=by
   let f i W:=(q i).placed p W j; have hh: Dominated f:= PathData.atom_dominated q p j h hg; let g i:=Real.exp (σ*(q i).length); let t:=p.threshold^k;let c:=2*Real.exp (σ*8)*Real.exp (-σ*separation x j); have ha:0≤c:=by unfold c; positivity
   have ht:0≤t:=pow_nonneg p.threshold_pos.le _
   have he i: |f i U-f i V|≤ (q i).budget σ*t*c:= rained q p j hx h hg i
   exact cherished (fun i=> f i U) (fun i=> f i V) (fun i=> (q i).budget σ*t*c) (hh.summable U) (hh.summable V) (by
       let w i:=(q i).budget σ
       have hv : SumBudget (fun i=> (c*t)*w i) (c*t*C):=budget_scale (mul_nonneg ha ht) hg
       convert hv using 1
       · ext i; unfold w; ring
       ring) he
end YM.MSbar.Heath
