import YM.MSbar.Heath.Scent
import YM.MSbar.LocalSD.Rare
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Heath
open Lattice Wilson RG Function Filter MeasureTheory Push.Local Push Push.AbsoluteSums WilsonStartup
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{n:Side}{U V:Config G n}{x:Site n}{R:Rep G n}{σ C T a v δ w:ℝ}
open Finset
variable (h:R.Lawful σ C T δ w)(hv:0<v)(hw:U∈calm G n v) (hp:Stab x U V) (hz:0≤R.beta)
    (hd:Decent R.clip R.p)(ht:v ≤ R.p.threshold)
-- Budget consumable even at U near all media.Gas extensive to anchored usage. logs
variable (j:ℕ)
omit h
private lemma gas_cap (A:Activities G n)(p:BudgetPoint)(h:A.Valid p δ w) (V: Config G n) (X:Support n)(he:flags p.threshold V⊆ X) : ‖A.gas p V‖ ≤ Real.exp (X.card*w) := by
   obtain ⟨b,hb,hV⟩:=h.boundK
   let f j i:=if j∈(A.forced i).support then p.mass (A.forced i).support (b i) else 0
   let g i:=∑ j∈X,f j i; have hv:SumBudget g (∑ _∈X,w):= budget_over X f (fun _=> w) (fun i _=>hV i)
   have ht(k: Finset ℕ): ‖A.gasOccurrence p k V‖ ≤ ∏ i∈k,g i:=by
       unfold Activities.gasOccurrence; split
       next hu=>
         rw [norm_prod]; apply prod_le_prod (fun i _=> norm_nonneg _); intro i hi; obtain ⟨j,hj⟩:= (A.forced i).inventory_ne
         have hx : j∈X:=he (hu.2 ▸ mem_biUnion.mpr ⟨i,hi,hj⟩)
         have hh : b i ≤ f j i :=by unfold f; rw [if_pos ((A.forced i).inventory_sup hj)]; exact p.loMass _ _ (hb i).1
         exact ((hb i).2 _).trans (hh.trans (single_le_sum (f:=fun j=> f j i) (fun j _=> (hV j).1 i) hx))
       rw [norm_zero]; exact prod_nonneg fun i _=>hv.1 i
   have hF: Summable fun k=> ∏ i∈k,g i := summable_finsetProd_of_summable_nonneg hv.1 hv.2.1; have hs:= (A.gasSeries h).absolute V
   exact (norm_tsum_le_tsum_norm hs).trans ((hs.tsum_le_tsum ht hF).trans ((BetaTransport.exponential_sum hv.1 hv.2.1).trans (Real.exp_monotone (by simpa using hv.2.2))))
include h hv hw hp ht hd hz
def life (p:BudgetPoint)(δ:ℝ):=δ * (2*Real.exp (p.supportExponent*10))*((2*(4*p.B+2)+1:ℝ)^4* meter p.supportExponent)
def ankle (p:BudgetPoint)(l:Clip)(σ C δ T v w β:ℝ):= ash p l β C σ T v+life p δ+(9:ℝ)^4*w
lemma tavern : R.eval V ≤ R.eval U* Real.exp (ankle R.p R.clip σ C δ T v w R.beta):=by
    let t:=R.p.threshold; have hh : flags t U=∅:= voids hw ht
    let X:=halo 4 {x}; have hk : flags t V⊆ X:= by
       intro j hj; by_contra hv; have ht:4<separation x j:= lt_of_not_ge (fun hn=>hv (halo_spec.mpr ⟨x,mem_singleton_self _,hn⟩))
       exact (notMem_empty j) (hh ▸ (flag_turns t j hp ht).2 hj)
    let A:=R.activities; have hw':0≤w:=budget_nonneg ((h.labels.boundK).choose_spec.2 x); have hp': ‖A.gas R.p V‖≤ Real.exp ((9:ℝ)^4*w) := (gas_cap A R.p h.labels V X hk).trans (Real.exp_monotone (mul_le_mul_of_nonneg_right (by exact_mod_cast horizon 4 x) hw')) -- 2*4 calc simp
    let f:= ash R.p R.clip R.beta C σ T v; let d:=life R.p δ
    have he:R.exponent V ≤ R.exponent U+(f+d) :=by
        have hi : R.path.inChannels .. - _ ≤ f:= average_paid h hv hw hp hz hd ht
        have hh : |A.additive R.p U-A.additive R.p V| ≤ d := additive_var R.p hp A h.labels
        dsimp only [A] at hh; unfold Rep.exponent; linarith only [hi,(abs_le.mp hh).2]
    unfold Rep.eval; rw [Activities.gas_one _ _ hh,mul_one]; apply (mul_le_mul_of_nonneg_left ((le_abs_self _).trans hp') (Real.exp_pos _).le).trans; rw [← Real.exp_add, ← Real.exp_add]; unfold ankle; rw [← add_assoc]; exact Real.exp_monotone (add_le_add_left he _)
end YM.MSbar.Heath
