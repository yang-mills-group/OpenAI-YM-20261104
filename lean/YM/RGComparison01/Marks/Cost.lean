import YM.RGComparison01.Marks.Arches
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
local notation "Z" => H.faresP
local notation "bZ" => H.birth
local notation "TZ" => Tree.Forest S.ratio
variable {P':ℝ} {M:ι→Leaf R} {rA : ι→ℝ}
local notation "X" => Palette.sign M S
local notation "wA" => Palette.wages M rA
local notation "I" => (Q.mark L μ s)
local notation "B0" => (radiusB s)
section aux
lemma markTot (p:Molecule S): (∏ i∈p,Real.exp (tolling H i)) = Real.exp (I*Cash.numP p) := by
  rw [← Real.exp_sum]; apply congrArg; unfold tolling Mixed.stamp; rw [← mul_sum]; simp_rw [Cash.numP,Nat.cast_sum]; rfl
lemma stair (i:Head S): 0 ≤ stairs H i:= by rcases i with i|i; exact mul_nonneg H.laws.acquired.extra (Nat.cast_nonneg _); exact Nat.cast_nonneg _
lemma pipeline (A:Leaf R): tolling H (A.turn.badge S)=0:= by cases i:A.turn <;> simp [tolling,Mixed.stamp,Mixed.shares,Wing.badge]
lemma eXtra (M:ι→Leaf R)(p:Tickets (Palette.sign M S)): (∏ i∈ p.reach,Real.exp (tolling H i))=1:= by
    refine prod_eq_one fun i hi=> ?_; obtain ⟨j,h,rfl⟩:= mem_image.mp hi; unfold Palette.sign; rw [pipeline,Real.exp_zero]
-- Polynomials after the tally. Use cheaper apartment. v includes === of every Leaf. 
end aux
variable (u:Head S→ℝ)
def streamB (H:Cash W s μ L Q o C T R)(u:Head S→ℝ)(j:ℕ)(p:Molecule S):= if H.ticketsP 0 0 0 p then
    (∏ i∈ p, u i)*Real.exp (Q.mark L μ s*Cash.numP p)*(1+H.shapeW p)^j* Real.exp (Q.ε*H.shapeW p) else 0

lemma streamBudget (hr : Ready H.supportP B0 (tariff u (stairs H) (tolling H) Q.ε) (Q.exp+2*Q.ε) w Q.δ (1/2)) (hu :∀ i,0≤u i)(j:ℕ): Ac.Hit H.unionP B0 (streamB H u j) Q.exp (extract Q.ε j 0 0 *treeYield w (1/2) 0):=by
  intro x
  let v i:= u i*Real.exp (tolling H i)
  have ha i : 0≤ v i:= mul_nonneg (hu i) (Real.exp_nonneg _)
  have hz : (tariff u (stairs H) (tolling H) Q.ε)=(tariff v (stairs H) 0 Q.ε):= by ext; unfold v tariff; simp only [Pi.zero_apply,add_zero,Real.exp_add]; ring
  rw [hz] at hr
  convert Sail.strongerSet (ι:=Head S) (n:=j) H.supportP B0 v (stairs H) Q.exp Q.ε ha stair Q.bound Q.usable hr x using 1
  ext p; unfold rooted; split
  next ht=>
    rw [streamB,H.attends]
    split
    next hh=>
      rw [if_pos ⟨hh,ht⟩]; unfold v Trees.currency; rw [Finset.prod_mul_distrib, markTot, show setPrice H.supportP B0 (stairs H) p=H.shapeW p from rfl]
      change _= ((_*_)*Real.exp (Q.exp*coverNumber B0 (H.unionP p)))*_*_; ring
    next he=> rw [if_neg fun h=> he h.1]; ring
  next he=> rw [if_neg fun h=> he h.2]; ring
-- decoration
section decoration
variable {ι : Type} [Fintype ι] (M:ι→Leaf R)(H:Cash W s μ L Q o C T R) {rA:ι→ℝ}
local notation "Q'" => Palette.sign M S
abbrev Caked:= Molecule S × Tickets (Palette.sign M S) -- H not used
abbrev reaches (p:Caked M (S:=S)):= H.unionP p.1
abbrev Cake (_H: Cash W s μ L Q o C T R):= _H.ThinP × Tickets (Palette.sign M S)
def eaten (F: Head S → ℝ) (rA:ι→ℝ) (p:Molecule S) (j:Tickets Q'):=
   if H.ticketsP 0 0 0 p ∧ j.reach⊆ p then (∏ i∈ j.val,rA i)*(Palette.team M j).weight*∏ i∈p\j.reach,F i else 0
lemma cub (F: Head S→ℝ) (p:Molecule S) : (∑ i:Tickets Q',eaten M H F rA p i)= if H.ticketsP 0 0 0 p then
   ∏ i∈ p, (F i+Tickets.extra Q' (Palette.wages M rA) i) else 0:= by
  unfold eaten; by_cases he:H.ticketsP 0 0 0 p
  · rw [if_pos he,Tickets.expanded]; apply Finset.sum_congr rfl; intro i hi; rw [Palette.worth]; simp only [he,true_and,Palette.wages,prod_mul_distrib]
  simp_rw [if_neg he]; simp [he]

def glorious (F: Head S→ℝ) (rA:ι→ℝ) (j:ℕ) (x:Caked M (S:=S)):= eaten M H F rA x.1 x.2 *Real.exp (Q.mark L μ s*Cash.numP x.1)*(1+H.shapeW x.1)^j* Real.exp (Q.ε*H.shapeW x.1)
omit [Fintype ι] in
lemma rollUp {F:Head S→ℝ} (ha:∀ i,0 ≤ F i) (hw:∀ i,0≤rA i) (j:ℕ) : ∀ i,0≤ glorious M H F rA j i:= by intro i; unfold glorious; refine mul_nonneg (mul_nonneg (mul_nonneg ?_ (Real.exp_pos _).le) (pow_nonneg (add_nonneg zero_le_one (H.positive_volume i.1)) _)) (Real.exp_nonneg _); unfold eaten; split; exact mul_nonneg (mul_nonneg (prod_nonneg fun _ _=> hw _) (profit _)) (prod_nonneg fun _ _=> ha _); exact le_rfl
lemma hit_cakes {F:Head S→ℝ} (ha:∀ i,0 ≤ F i) (hw:∀ i,0≤rA i)
   (hq:Ready H.supportP (radiusB s) (tariff (fun i=>F i+Tickets.extra Q' (Palette.wages M rA) i) (stairs H) (tolling H) Q.ε) (Q.exp+2*Q.ε) w Q.δ (1/2))(j:ℕ): Ac.Hit (reaches M H) (radiusB s) (glorious M H F rA j) Q.exp (extract Q.ε j 0 0 *treeYield w (1/2) 0):=by
   let v:= (fun i=> F i+Tickets.extra Q' (Palette.wages M rA) i)
   have hz i:0≤v i:= by unfold v Tickets.extra; refine add_nonneg (ha _) (sum_nonneg fun i _=>?_); split; exact mul_nonneg (hw i) (M i).profit; exact le_rfl
   have hs:= streamBudget (H:=H) v hq hz j
   have hp(p:Molecule S): (∑ i:Tickets Q', glorious M H F rA j (p,i))= streamB H v j p:=by unfold glorious; simp only [← sum_mul]; rw [cub]; unfold streamB; split_ifs; rfl; ring
   intro p; let g x:= if p∈H.unionP x then streamB H v j x*Real.exp (Q.exp*coverNumber (radiusB s) (H.unionP x)) else 0
   let f i:= if p∈ reaches M H i then glorious M H F rA j i*Real.exp (Q.exp*coverNumber (radiusB s) (reaches M H i)) else 0; have hf i : 0≤ f i:= by unfold f; split; exact mul_nonneg (rollUp M H ha hw _ i) (Real.exp_pos _).le; exact le_rfl
   change SumBudget f _; apply budget_of_sum hf; intro u;
   let S':= u.image Prod.fst
   have h : (∑ x∈ S',∑ j,f (x,j))=∑ x∈ S',g x:= by
     apply sum_congr rfl; intro i hi; unfold f g reaches; split_ifs; · rw [← hp,Finset.sum_mul]
     exact sum_const_zero
   have hu : u⊆ S'×ˢuniv:= fun i hi=>by rw [Finset.mem_product]; exact ⟨mem_image_of_mem _ hi,mem_univ _⟩
   apply le_trans (sum_le_sum_of_subset_of_nonneg hu (fun i _ _=> hf i)); rw [Finset.sum_product,h]; exact budget_sum (hs p) _

end decoration
end YM.RGComparison01.Pledge
