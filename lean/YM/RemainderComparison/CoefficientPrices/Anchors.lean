import YM.Ac.Tree
import YM.RG.Masks
import YM.Marker.Weight
import YM.Push.ABSOLUTE_SUMS.Basic
/-!
# tariff for mixed output coefficient read

Square-zero markers with arbitrary one-cut downward censorship. Each occurrence
already normalized with analytic envelope `χ`, through Chorus.material. Don't lever
that on the K-vac. Tag toll can now be restored (pay reciprocal product of radii on
extraction of the specified coefficient). Receipts are *simultaneous* across all sites,
varying positions / copy numbers / tests.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.CoefficientPrices
open Finset Lattice RG Marker Push.AbsoluteSums
open scoped BigOperators Classical
variable {θ ι:Type}{I:Type*}{n:Side}{Z:Set ι} [DecidableEq θ]{J:Census θ}{q:θ→ℝ}{z:ι→ Poly J}{p:BudgetPoint}{s:ℝ}{k:ℕ}
local notation "toll" => Poly.toll
structure Loan (J:Census θ) (q:θ→ℝ)(roots:θ→ Site n) (area:I→ Support n) (p:BudgetPoint) (σ:ℝ) (f:I→J.Mode→ℝ) (g:ℝ):Prop where
    nonnegative i j : 0 ≤ f i j
    locations (x:Site n) : SumBudget (fun i:I× J.Mode=> if x∈ area i.1 then toll q i.2*f i.1 i.2 * Real.exp (σ*coverNumber p.B (area i.1)) else 0) g
    ancestry (t:θ): SumBudget (fun i:I × J.Mode=>if t∈ i.2.val then toll q i.2*f i.1 i.2*Real.exp (σ*coverNumber p.B (area i.1)) else 0) g
    follows i s (t:θ): t ∈ s.val → f i s≠0→ roots t ∈ area i -- annotate s
lemma tallyI {l:I→ Support n} (f:I→ℝ) (σ:ℝ) (h: Ac.Hit l p.B f σ s) (g:I→ J.Mode→ℝ) (hg:∀ i j,0≤g i j) (hV:∀ i, ∑ j:J.Mode,g i j ≤ f i) : Ac.Hit (fun i:I×J.Mode=>l i.1) p.B (fun i=> g i.1 i.2) σ s:=by
    let A (x:Site n) (i:I× J.Mode):= if x∈ l i.1 then g i.1 i.2 * Real.exp (σ* coverNumber p.B (l i.1)) else 0
    have ha x (i:I× J.Mode):0≤A x i:=by unfold A; split; exact mul_nonneg (hg ..) (Real.exp_pos _).le; exact le_rfl
    refine fun x=>budget_of_sum (ha x) fun S=>?_ -- compare all projections
    calc
        (∑ i∈S,_ )≤ ∑ i∈ (S.image Prod.fst)×ˢ (@Finset.univ J.Mode _),A x i := sum_le_sum_of_subset_of_nonneg (fun i hi=> Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hi,Finset.mem_univ _⟩) fun i _ _=> ha x i
        _ ≤ _ :=by
             rw [sum_product]
             refine (le_trans ?_ (budget_sum (h x) (S.image Prod.fst))); refine sum_le_sum fun i _=>?_ 
             unfold A; by_cases hv:x∈l i;
             · simp only [hv,ite_true]; rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (hV i) (Real.exp_pos _).le
             · simp [hv]

variable (roots:θ→ Site n) (σ:ℝ) (X:I→ Support n)(g:I→ J.Mode→ℝ)
variable (h: ∀ x, 0<q x)
include h
lemma occupied (hi:∀ i j,0≤g i j)(hv:∀ i (s:J.Mode) t,t∈s.val → g i s≠0→ roots t∈ X i) (hB : Ac.Hit (fun i:I ×J.Mode=> X i.1) p.B (fun i=> toll q i.2*g i.1 i.2) σ s) : Loan J q roots X p σ g s:=by
    refine ⟨hi,hB,fun t=>budget_mono (hB (roots t)) ?_ ?_,hv⟩
    · intro i; split; exact mul_nonneg (mul_nonneg (Poly.worth h _).le (hi ..)) (Real.exp_pos _).le; exact le_rfl
    intro i; split; next hh=>
       by_cases H : g i.1 i.2=0
       · have he:= (hB (roots t)).1 i; rw [H,mul_zero,zero_mul]; exact he
       rw [if_pos (hv _ _ _ hh H)]
    next=> exact (hB (roots t)).1 i

-- individual modes.Ancestry stronger than needed. charge at actual support p too
variable (hp:Loan J q roots X p σ g s)
include hp
lemma Loan.specific (s':J.Mode) (a:θ) (hx : a ∈ s'.val) : SumBudget (fun i=> Real.exp (σ*coverNumber p.B (X i))*g i s') ((toll q s')⁻¹ * s):=by
    let f i : I×J.Mode:=(i,s')
    have ht := Poly.worth h s'
    convert budget_scale (inv_nonneg.mpr ht.le) (budget_pull f (fun i j hf=> congr_arg Prod.fst hf) (hp.ancestry a)) using 1
    ext i; rw [if_pos hx]; change _=(toll q s')⁻¹ * (toll q s'* g i s'*Real.exp _); field_simp; ring

end YM.RemainderComparison.CoefficientPrices
