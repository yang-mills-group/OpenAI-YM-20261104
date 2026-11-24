import YM.RGComparison01.Bouquet

/-!
# Detailed reconstruction after angular reflection

 Finance differences *after subtraction* in a genuine support norm.
 Requires a model renderer in the reflected gauges, and its standalone
 budget paid for both AUX and real; do not infer that one from unmasked
 pre-blocks. Align at guarded supports. -/

set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Purity
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter
open PhysicalNext PhysicalNext.Repeat Deck Stellar Mint Greenbelt Boulevard Trio
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration Song Refrain Reserves OmitClusters
open Divides Input Org Supply PriceCompiler Next.Scheduling Progress.DirectedRecipe Time Opera Slide
open RG.Supply RG.Shoot Push.Uniform Sienna Pane
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {U : Stars→Side} {g t V' u W m m' p θ : ℝ} {n k k' b z w r: ℕ} {c C F L:Side} {K : Teller G} {Y : ℝ} {Q : ConnectedActivityE6.Target G K} {o : Target.Order G Y}
section pencil
variable {f : Side} {S : StepData c f} {T : Tube G S} {R : RG.Rep G f} {κ : Chi}
  {H : Cash Y u t L Q o W T R} {ι:Type} (D : Cabinet ι H b) (P : BudgetPoint)
  (n k : ℕ) (g : ℝ) (κ : Chi) (A : ∀ i, (U i).val=2*(w+i.val)) (z : ℕ)
  (V M : ∀ i:Stars, Trio.Offer G (U i))
  (F : Trio.Offer G c)
set_option quotPrecheck false
local notation "h" => D.tot κ n k g
local notation "B" => Cabinet.studio b n (radiusB u)
local notation "oW" => (plusone H (selfA H) κ g)
local notation "Θ" => ((Beam.marquee H P).read)
local notation "P'" => D.leftward κ g n k
local notation "g'" => (h-F)
local notation "σ" => Trio.ornament (c:=c) A (V-M)

def steam (i : Site c) (x : Config G c) := D.earned P κ g n k i x - (masked P.threshold (neighbors z i) (F i) x) - g' i 1 - Trio.unearned P A z (Trio.rip (V-M)) i x

variable (ho: Collection.Local (Beam.marquee H P) P (plusone H (selfA H) κ g) m m')
    (hM : Trio.Mirrors F) (hH: P.B=radiusB u) (hA : 2*Cabinet.studio b n (radiusB u) ≤ w) (he:w+4≤z)
local notation "Σv" => steam D P n k g κ A z V M F
include ho hM
lemma transfers (x : Config G c) : (Θ oW).additive P x= (Θ P').additive P x+
    Fintype.card (Site c)*g' 0 1 + (∑ i, masked P.threshold (neighbors z i) ((σ+F) i) x) + ∑ i, Σv i x:= by
  have hF i: g' i 1=g' 0 1:= by
    let u:= h; change u _ _-F _ _=u _ _-F _ _; rw [show i=Lattice.affine 1 i (0:Site c) by simp [Lattice.affine], ← hM]
    have he: Lattice.pull (1:Signed) i (1: Config G c)=1:= by rw [pull_one]; rfl
    unfold u; rw [← Cabinet.rotates,he]
  rw [D.unearned P ho n k]; let f i:= masked P.threshold (neighbors z i) (F i) x; let k':=V-M; let a i:= masked P.threshold (neighbors z i) (σ i) x
  have ht i: masked P.threshold (neighbors z i) ((σ+F) i) x=a i+ f i:= by
    by_cases he : Healthy P.threshold (neighbors z i) x
    · unfold f a; rw [masked_eq _ _ _ _ he,masked_eq _ _ _ _ he,masked_eq _ _ _ _ he]; rfl
    unfold f a; rw [masked_ne _ _ _ _ he,masked_ne _ _ _ _ he,masked_ne _ _ _ _ he,add_zero]
  have he: ∑ i,a i=∑ i,Trio.unearned P A z (Trio.rip (V-M)) i x:= Trio.parade P A z (Trio.rip _) x
  unfold steam; simp_rw [ht,hF]; rw [sum_add_distrib,sum_sub_distrib,sum_sub_distrib,sum_sub_distrib,sum_const,nsmul_eq_mul,card_univ]; rw [he]; unfold f; ring

variable (hZ : ∀ i,P.Regular (neighbors z i) (F i)) (hq : ∀ i j,P.Regular univ (V i j)) (hp : ∀ i j,P.Regular univ (M i j))
omit hM ho
include hH hA he
lemma resolves (i : Site c) (hx:4*B+16≤c.val)
    (ht : Trio.CompatibleP P B h V) (hu : Trio.CompatibleP P B F M) (X : Config G c) (hm:Healthy P.threshold (neighbors (2*z) i) X) : Σv i X=0:= by
  let f:=g'; have hd:Trio.CompatibleP P B (h-F) (V-M):= by
    refine ⟨fun i t b k Y=> congr_arg₂ (·-·) (ht.moves i t b k Y) (hu.moves i t b k Y),fun i k x y U V hp hq hz=> congr_arg₂ (·-·) (ht.pace i k x y U V hp hq hz) (hu.pace i k x y U V hp hq hz),fun i x y U V ha hb hh=> congr_arg₂ (·-·) (ht.forks i x y U V ha hb hh) (hu.forks i x y U V ha hb hh), fun i x y hi=> congr_arg₂ (·-·) (ht.visitL i x y hi) (hu.visitL i x y hi)⟩
  have hp:= Trio.cruising P A z (Trio.rip (V-M)) X i he hA le_rfl hx hm (fun i' => Boulevard.stillA (f i')) (Trio.tinted _ _ hd) (by unfold Cabinet.studio; have hh := P.B_pos; rw [hH] at hh; omega)
  unfold steam; rw [hp,masked_eq _ _ _ _ (hm.mono_left (fun i hi=> (neighbors_mem ..).2 (((neighbors_mem ..).1 hi).trans (by omega)))), Cabinet.total D P n k X i hH (hm.mono_left (fun i hi=> (neighbors_mem ..).2 (((neighbors_mem ..).1 hi).trans (by omega))))]; exact sub_self _

include hZ hp hq ho
lemma tides (i : Site c) : Trio.Tidy P (neighbors (2*z) i) (Σv i) := by
  let A': Config G c→ℝ:= Trio.unearned P A z (Trio.rip (V-M)) i; let f x:= D.earned P κ g n k i x; let F₀:= masked P.threshold (neighbors z i) (F i)
  apply Trio.tidy_sub (v:=A') P; swap; · exact Trio.tidy_sum _ _ _ _ fun j _=> Trio.tidy_scale _ _ (Trio.tidy_sum _ _ _ _ fun u _=> Trio.tidy_mask _ (Trio.unit_m P A z (V-M) (fun s t=> CouplingShape.reg_sub (hq _ _) (hp _ _)) he (emerge A j u i) j u) (Trio.patch A z he j u i le_rfl))
  apply Trio.tidy_sub (u:=f-F₀) P _ (Trio.tidy_const ..)
  apply Trio.tidy_sub P _ (Trio.tidy_mask _ (hZ i) (fun j hj=> (neighbors_mem ..).2 (((neighbors_mem ..).1 hj).trans (by omega))))
  refine Trio.tidy_sum _ _ (D.board n k) _ fun j hj=>?_ ; by_cases hB: Meadow.garnerAt H P i j=0; · simp only [hB,zero_mul]; exact Trio.tidy_const ..
  exact Trio.tidy_scale _ _ (Trio.tidy_mask _ (ho.smooth j) (fun p hp=> (neighbors_mem ..).2 (((neighbors_mem ..).1 ((D.billed P j hj hH i hB).2 hp)).trans (by omega))))

omit ho hH hA hZ in
lemma holy (x : Site c): P.Regular (neighbors z x) (σ x) := by
  rw [Trio.orchard]; apply Meadow.regularA; intro i _
  let f:= (Trio.froth ((V-M) i)); have ht : P.Regular univ f := by rw [show f=∑ j,(V-M) i j from funext fun i'=> (Finset.sum_apply ..).symm]; exact Meadow.regularA _ fun j _=> CouplingShape.reg_sub (hq _ _) (hp _ _)
  refine CouplingShape.reg_scale _ (Slide.regular (pad A i) x (show P.Regular univ (Boulevard.stillA f) from CouplingShape.reg_sub ht (CouplingShape.reg_const _)) (fun j=> (neighbors_mem ..).2 ((Slide.village (C:=U i) (A i|>.ge) x j).trans (by have hk := i.isLt; omega))))

omit hZ hp hq hA
lemma desk (x : Site c) (v:Stars→ℝ)
    (hf : ∀ i,P.supBounds i (neighbors z i) (F i) p)
    (hp: ∀ i (y:Config G (U i)), flags P.threshold y=∅→∀ x, ‖(V-M) i x y‖≤ v i)
    (Y : Config G c) : ‖Σv x Y‖ ≤ let f:=(ballCost B:ℝ)*m; f+p+(f+p)+ ∑ i:Stars, |Slide.ray i| *((Fintype.card (Site (U i)):ℝ)*(v i+v i)) := by
  have hV:(1:Config G c) ∈ Boulevard.sunny P:= Pencils.blue _; have he':= Boulevard.smoky hV
  let f:= Σv; have hg : ‖h x 1‖ ≤ (ballCost B:ℝ)*m:= by rw [← Cabinet.total D P n k 1 x hH (by unfold Healthy; rw [he']; simp)]; exact D.chalk P ho _ _ 1 x hH
  have hs : ‖g' x 1‖ ≤ (ballCost B:ℝ)*m + p:= by
    change ‖h x 1-F x 1‖≤_; refine (norm_sub_le ..).trans (add_le_add hg ?_); rw [← masked_eq P.threshold (neighbors z x) (F x) 1 (by unfold Healthy; rw [he']; simp)]; exact CouplingShape.mask_cost (hf x) 1
  unfold steam; apply (norm_sub_le ..).trans; exact add_le_add ((norm_sub_le ..).trans (add_le_add ((norm_sub_le ..).trans (add_le_add (D.chalk P ho _ _ Y x hH) (CouplingShape.mask_cost (hf x) Y))) hs)) (Trio.stipends P Y A z _ _ hp he x)
end pencil
end YM.RGComparison01.Purity
