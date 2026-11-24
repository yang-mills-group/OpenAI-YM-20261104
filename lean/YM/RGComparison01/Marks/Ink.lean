import YM.RGComparison01.Marks.Ropes
import YM.MergeProof.Appl
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
/-!
# Angular arcs on the *whole product*, leg reimbursements

 Precise log representative before confronting the tensor prescription. Lives
 on all signed terms incl overlapping reads. Single MarkerParams along t=0
 enforce shared-square zero.Untiweighted here uses Lens. -/
namespace Ink
open Foreman Checks Baked Palette Pillow Resin Season
open Switch
variable [Fintype ι]
variable (M:ι→Leaf R)(g:ι→ℝ) (H:Cash W s μ L Q o C T R)(V:Config G c)
local notation "Pt"=> Q.mark L μ s
local notation "CL"=> Cl M H
local notation "CM"=> Cake M H
-- repetitions allowed, including c empty
abbrev printer (p:CL)(x:ℝ)(v:Finset ι) := ∏ i,Switch.click (p.2 i).2.val 1 x v
def paths (p:CL)(V:Config G c)(x:ℝ)(v:Finset ι) := printer M H p x v*pottery M g χ p V
def yielded (p:CL)(V:Config G c)(x:ℝ)(v:Finset ι) := if Season.allot p≠0 then paths M g H p V x v (χ:=χ) else 0
omit [Fintype ι] in lemma blanker (p:CL)(x:Finset ι) : yielded M g H (χ:=χ) p V 0 x=0:=by
  unfold yielded; split; swap; · rfl
  next ht=>
  have hv :∃ i,(p.2 i).2.val.card≠0:=by by_contra! h; exact ht (sum_eq_zero fun i _=>h i)
  obtain ⟨j,hj⟩:=hv; unfold paths; rw [printer, prod_eq_zero (mem_univ j) (show click _ _ _ _=0 from ?_), zero_mul]
  unfold click; split_ifs; rw [zero_pow hj,zero_mul]; rfl

-- fiber assembly: undecorated log common signature.Bij
abbrev spore (H:Cash W s μ L Q o C T R) (p:H.fragrances):= Tuple (Tickets (Palette.sign M S)) p.1

abbrev pollen (p:H.fragrances)(x:spore M H p): CL:= ⟨p.1,fun i=> (p.2 i,x i)⟩
def span : CL≃ Σ p,spore M H p where
  toFun p:= ⟨⟨p.1,Prod.fst ∘ p.2⟩,Prod.snd ∘ p.2⟩
  invFun y:= pollen M H y.1 y.2
  left_inv _:= rfl
  right_inv _:= rfl

lemma tally (p: H.fragrances) (x:ℝ)(v:Finset ι): (∑ i:spore M H p, paths M g H (χ:=χ) (pollen M H p i) V x v)= Palette.song M H χ g p V x v:=by
   let W:=Palette.ways g x v; let k:=p.2; let z j (i:Tickets (Palette.sign M S)) := click i.val 1 x v * Pillow.emberP M g (H:=H) χ (p.2 j,i) V; let c:=coefficient H.seam p.2/(p.1+1).factorial
   have he (i:spore M H p):paths M g H (χ:=χ) (pollen M H p i) V x v = c*∏ j,z j (i j):=by
     have hX : coefficient H.seam p.2=coefficient (seam M H) (pollen M H p i).2:= Meadow.movement _ _ _ _ (fun i j=> Iff.rfl) -- need equivalence
     unfold paths printer pottery Gas.term; rw [← hX]; unfold c z; dsimp only [pollen]; simp_rw [prod_mul_distrib]; ring
   have h (j): (∑ i,z j i)= Palette.vote M H χ g (p.2 j).val V x v:=by
     unfold Palette.vote Palette.color; simp_rw [amplitudes g]; refine sum_congr rfl fun i _=>?_ ; unfold z Pillow.emberP divAmt Palette.act; unfold click; split_ifs <;> push_cast <;> ring
   simp_rw [he]; unfold song Cash.trainedMill Gas.term; rw [← Finset.mul_sum, ← Fintype.prod_sum z]; simp_rw [h]; change c * _ = coefficient H.seam p.2*(∏ j, Palette.vote M H χ g (p.2 j).val V x v)/_; unfold c; ring
omit [Fintype ι] in
lemma units (p:CL)(i:ℝ)(x:Finset ι) : yielded M g H (χ:=χ) p V i x= paths M g H (χ:=χ) p V i x-paths M g H (χ:=χ) p V 0 ∅:= by
   unfold yielded; by_cases h: Season.allot p=0; swap
   · rw [if_pos h, show paths M g H (χ:=χ) p V 0 ∅= yielded M g H (χ:=χ) p V 0 ∅ from (if_pos h).symm, blanker,sub_zero]
   have ht j : (p.2 j).2.val=∅:= card_eq_zero.mp (Nat.eq_zero_of_le_zero (single_le_sum (s:=univ) (fun i _=> Nat.zero_le _) (mem_univ j)|>.trans (show ∑i,(p.2 i).2.val.card ≤0 from h.le))) -- fix
   unfold paths; rw [if_neg (not_not.mpr h)]; simp [printer,ht,click]

-- Paid kernel representative. support mass in mask cost.
lemma backed (p:CL) (P:BudgetPoint) {b:ℝ} (_hf:P.threshold = Pressure.temp s) (hz: ∀ i∈origins M H p,P.supBounds i (origins M H p) (glass M g χ p) b)
    (he:pottery M g χ p=masked P.threshold (origins M H p) (glass M g χ p)) : Paid (fun U=>paths M g H (χ:=χ) p U) b:= by
   obtain ⟨i,hi⟩:= (show (origins M H p).Nonempty from Finset.Nonempty.mono (subset_biUnion_of_mem (raised M H ∘ p.2) (Finset.mem_univ none)) (p.2 none).1.2.1)
   have ht : Paid (ι:=ι) (fun i:Config G c=>fun _ _=>pottery M g χ p i) b:= Switch.constant _ (hz i hi|>.1) (fun v=> he.symm ▸ CouplingShape.mask_cost (hz i hi) v)
   have hp (j : Option (Fin p.1)): Paid (fun _:Config G c=> click (p.2 j).2.val 1) 1:= paidClick _ zero_le_one (fun _=> (norm_one (α:=ℝ)).le)
   have hk := (Paid.prod univ (fun j (_:Config G c)=> click (p.2 j).2.val 1) (fun _=>1) (fun j _=> hp j)).mul ht
   rw [prod_const_one,one_mul] at hk; refine Paid.congr hk (fun q t v=>?_); ext i; simp only [paths,printer,Pi.mul_apply,Finset.prod_apply]
end Ink
end YM.RGComparison01.Pledge
