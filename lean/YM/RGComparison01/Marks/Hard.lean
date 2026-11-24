import YM.RGComparison01.Marks.Cost
import YM.MergeProof.Steps
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Pledge
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter Mixed Reserves
open PhysicalNext PhysicalNext.Repeat Packets Art Silica Poll Pond Shield Eider Gas Ursell Trees Height Sail
open PhysicalNext.Repeat.Lotus Team Merge
open AnalyticBridge VerifiedReset Collection Quotes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge} {ι : Type} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : RG.Rep G f}
    {n : ℕ} {W a r σ Λ μ s κ w c' C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
    {H : Cash W s μ L Q o C T R} {d C' A B e δ t D D' v K :ℝ} {j k ℓ:ℕ} {χ:Chi} {Ω : Utopia H j v d r C' χ}
    {Ψ : ℕ → Prop} {x:ℕ→ℝ}
namespace Resin
open Multiple OmitClusters Palette Switch Daisy
variable [Fintype ι]
variable (M:ι→Leaf R) (ρ:ι→ℝ) (H:Cash W s μ L Q o C T R)
local notation "q" => Q.mark L μ s
local notation "Pp" => H.faresP
local notation "Xg" => Palette.sign M S
lemma simpler (p:Molecule S)(i:ℕ) : tune M H ρ i 0 p=if H.ticketsP 0 i 0 p then (∏ j∈p, toll M H ρ j) else 0:=by
  unfold Palette.tune Mixed.selected; by_cases hh:H.ticketsP 0 i 0 p; swap
  · rw [if_neg (show ¬Allowed S Q.halo (radiusB s) (swing Q L μ R.beta s C) H.birth (ConnectedActivityE6.lengths T R) 0 i 0 p from hh),if_neg hh]
  rw [if_pos (show Allowed S Q.halo (radiusB s) (swing Q L μ R.beta s C) _ _ 0 i 0 p from hh),if_pos hh,Mixed.Price,pow_zero,mul_one]
  apply prod_congr rfl; intro j _; rcases j with j|j
  · unfold Palette.toll Tickets.extra; rw [sum_eq_zero,add_zero]; · rfl
    intro i _; exact if_neg (fun h=> by have hf:=(show .inr _ = Palette.sign M S i from Daisy.sparkPath ..).trans h; contradiction)
  unfold Palette.toll Tickets.extra Cash.text Mixed.costs pitch Tickets.extra
  dsimp only [Sum.elim]; simp_rw [← show ∀ i,(.inr (Palette.mark M (c:=c) i):Head S)=Palette.sign M S i from fun i=> Daisy.sparkPath ..]; simp only [Sum.inr.injEq]

def Hired (H:Cash W s μ L Q o C T R)(v:ℝ):= Ready H.supportP (radiusB s) (tariff (toll M H ρ) (stairs H) (tolling H) Q.ε) (Q.exp+2*Q.ε) v Q.δ (1/2)

set_option quotPrecheck false
local notation "p₀"=> fun i:H.ThinP=> tune M H ρ 0 0 i.val
local notation "p₁"=> fun i:H.ThickP=> tune M H ρ 1 0 i.val

-- full pre-attachment rollout price for forced and real amplitude.
def Slides (Q:ConnectedActivityE6.Target G P) (w:ℝ) := extract Q.ε 0 0 0 * treeYield w (1/2) 0

lemma rates (hh:Hired M ρ H v)(he:∀ i,0≤ρ i) (ht:a+δ+δ≤Q.exp)(hδ:0<δ)(hw:Slides Q v ≤ w)(hy:0 < w) (hB:degreePrice (radiusB s) w δ ≤ 1/2) :
    Ready H.smallAt (radiusB s) p₀ (a+δ) w δ (1/2) ∧ Ac.Hit H.largeAt (radiusB s) p₁ (a+δ) (Real.exp (-q)*w) := by
  have hf := fun i:H.ThinP=> (votes M H (χ:=Chi.canonical) ρ he i.val 0 0 (Nat.zero_le _)).rocket
  have hv' := fun i:H.ThickP=> (votes M H (χ:=Chi.canonical) ρ he i.val 1 0 (Cash.forced_cost i.val i.prop.2)).rocket
  let F := streamB H (toll M H ρ) 0
  have hp : Ac.Hit H.unionP (radiusB s) F Q.exp (Slides Q v):=by
    refine streamBudget _ hh (fun j=>add_nonneg (H.positive _) ?_) _; apply sum_nonneg; intro i _; split; exact mul_nonneg (he i) (M i).profit; exact le_rfl
  let st:= fun p:Molecule S=> Real.exp (q * Cash.numP p) * Real.exp (Q.ε*H.shapeW p)
  have h0 (p:H.ThinP):p₀ p ≤ F p.val := by
    have h₀ : Real.exp (q * Cash.numP p.val) ≥ 1:= Real.one_le_exp (mul_nonneg H.laws.acquired.marked (Nat.cast_nonneg _))
    have hf' : (p₀) p *(st p.val)= F p.val := by
      unfold F streamB st; dsimp only; rw [simpler]
      split_ifs <;> ring
    rw [← hf']; exact le_mul_of_one_le_right (hf _) (one_le_mul_of_one_le_of_one_le h₀ (Real.one_le_exp (mul_nonneg Q.usable.le (H.positive_volume _))))
  have h1 (p:H.ThickP): p₁ p ≤ Real.exp (-q)*F p.val := by
    have hv : Cash.numP p.val ≥ 1 := Cash.forced_cost _ p.prop.2
    have h₀ : Real.exp (q * Cash.numP p.val) ≥ Real.exp q:= Real.exp_monotone (le_mul_of_one_le_right H.laws.acquired.marked (by exact_mod_cast hv))
    have hx : (p₁) p * (st p.val)=F p.val:=by
      unfold F streamB st; dsimp only; rw [simpler]
      have hx : H.ticketsP 0 0 0 p.val↔ H.ticketsP 0 1 0 p.val:= by
        constructor; intro hh; exact ⟨hh.1,hh.2.1,hv,hh.2.2.2⟩; exact fun ht => (H.attends _).2 ht.1
      rw [hx]; split_ifs <;> ring
    rw [Real.exp_neg, le_inv_mul_iff₀ (Real.exp_pos _),← hx,mul_comm]; exact mul_le_mul_of_nonneg_left (h₀.trans (le_mul_of_one_le_right (Real.exp_pos _).le (Real.one_le_exp (mul_nonneg Q.usable.le (H.positive_volume _))))) (hv' _)
  refine ⟨⟨hy,hδ,hB,(by norm_num),hf,fun x=> ?_⟩,fun x=> ?_⟩
  · have he' := budget_pull (fun i:H.ThinP=> i.val) Subtype.val_injective (hp x)
    refine budget_loosen (budget_mono he' (fun i => ?_) (fun i=>?_)) hw
    · split; exact mul_nonneg (hf _) (Real.exp_nonneg _); rfl
    dsimp only; split
    next hi=> rw [if_pos (show x∈ H.unionP i.val from hi)]
              exact mul_le_mul (h0 i) (Real.exp_monotone (mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg _))) (Real.exp_nonneg _) ((hf i).trans (h0 i))
    next=> exact he'.1 _
  have he' := budget_scale (Real.exp_pos (-q)).le (budget_pull (fun i:H.ThickP=> i.val) Subtype.val_injective (hp x))
  refine budget_loosen (budget_mono he' (fun i=> ?_) (fun i=>?_)) (mul_le_mul_of_nonneg_left hw (Real.exp_nonneg _))
  · split; exact mul_nonneg (hv' _) (Real.exp_nonneg _); rfl
  dsimp only; split
  next hi=>
    rw [if_pos (show x∈ H.unionP i.val from hi), ← mul_assoc]
    exact mul_le_mul (h1 i) (Real.exp_monotone (mul_le_mul_of_nonneg_right (le_trans (le_add_of_nonneg_right hδ.le) ht) (Nat.cast_nonneg _))) (Real.exp_nonneg _) ((hv' i).trans (h1 i))
  next=> exact he'.1 i
end Resin
end YM.RGComparison01.Pledge
