import YM.RGComparison01.Fiber

/-!
# Vertex sum and the source coordinates before mask change

 Keep E identities from chosen panel EXACT. Cannot move masks on tot
 with same price; later Trio for healthy stacks.
 -/

set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Cabinet
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter
open PhysicalNext PhysicalNext.Repeat Deck Stellar Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration Song Refrain Reserves OmitClusters
open Divides
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {ℓ M n k b : ℕ} {ι χ : Type} {K : Teller G} {P : Patch}
variable {s W a U u : ℝ} {X : ConnectedActivityE6.Target G K} {o : Target.Order G W}
    {κ: Chi} {c f C F L₀: Side} {S:StepData c f} {T : Tube G S} {R : RG.Rep G f}
    {I : Cash W s a L₀ X o U T R}
variable (D : Cabinet ι I b) (Y : BudgetPoint) {κ:Chi} {γ t w : ℝ}
local notation "B" => radiusB s
local notation "X'" => selfA I
local notation "Y'" => Beam.marquee I Y

abbrev studio (b ℓ B' : ℕ) := Cabinet.garage b ℓ + 2*B'
local notation "y" => Cabinet.studio b ℓ B

lemma modest (i : Magazine I) (hv : i∈ D.catalogue ℓ k) (hB:Y.B=B) (x:Site c) (ht : Meadow.share I Y x i ≠0) :
    x∈(Beam.contents I Y i).support ∧ (Beam.contents I Y i).support⊆neighbors y x := by
  rcases i with i|i
  · obtain ⟨z,hz,rfl⟩:= mem_map.mp (inl_mem_disjSum.mp hv)
    have he: x∈ Song.perf I ((D.bureau ℓ) z) := by contrapose! ht; exact if_neg ht
    change x∈ (Beam.dashboard I _).support ∧ (Beam.dashboard I _).support ⊆_; rw [Beam.see]
    exact ⟨he,fun i hi=>(neighbors_mem ..).2 (((neighbors_mem ..).1 (extent D z x he hi)).trans (Nat.le_add_right ..))⟩
  obtain ⟨⟨θ,k'⟩,he,rfl⟩:= mem_map.mp (inr_mem_disjSum.mp hv); have hf : Meadow.melody T.down k'≤ B:= (mem_filter.mp ((mem_product.mp he).2)).2
  let k:= strings T.down Y (Meadow.legs θ k'); have he:k.site=x := by contrapose! ht; exact if_neg ht
  change x∈k.support ∧ k.support⊆_
  refine ⟨he ▸ k.anchor,?_⟩; rw [show x=θ.2 from he.symm.trans (Meadow.tunesAnchor ..)]; intro x hx; have h:= (neighbors_mem ..).1 (Meadow.yarn T.down Y θ k' hx); apply (neighbors_mem ..).2; dsimp only [studio]; omega

lemma billed (i:ℕ) (h:i∈ D.board ℓ k) (hB:Y.B=B) (x:Site c) (hp : Meadow.garnerAt I Y x i≠0) :
    x∈ ((Y').reg i).support ∧ ((Y').reg i).support ⊆ neighbors y x := by
  let p:=Song.pennant I i; let θ:=Meadow.spin p.1; let u:=θ.symm x
  obtain ⟨hz,ht⟩:= modest D Y p.2 ((D.earns i).1 h) hB u hp
  change x∈ Finset.image θ _ ∧ Finset.image θ (Beam.contents I Y p.2).support⊆ _
  refine ⟨mem_image.mpr ⟨u,hz,θ.apply_symm_apply x⟩,fun i hi=>?_⟩; obtain ⟨k,hk,rfl⟩:=mem_image.mp hi; apply (neighbors_mem ..).2
  rw [show x=θ u from (θ.apply_symm_apply x).symm, show separation (θ u) (θ k)=separation u k from ?_]
  exact (neighbors_mem ..).mp (ht hk)
  change separation (p.1.1.act u+p.1.2) (p.1.1.act k+p.1.2)=_; rw [separation_translate,separation_signed]

local notation "Ih" => Song.plusone I X' κ γ
include D Y
lemma payee (κ : Chi) (γ : ℝ) (ℓ k : ℕ) (x:Site c) (V : Config G c):
    ∑ i∈ D.catalogue ℓ k, Meadow.share I Y x i * opus I (X') κ γ i V=D.offered κ ℓ k x V + Meadow.garner T.down T.low R.beta γ B k x V:= by
  unfold catalogue; rw [sum_disjSum,sum_map,sum_map]
  apply congr_arg₂ HAdd.hAdd
  · unfold offered; rw [Finset.sum_filter]; apply sum_congr rfl; intro i hi
    unfold Meadow.share opus; simp only [Sum.elim,Song.sequence,Pi.smul_apply,smul_eq_mul,farther]
    split_ifs with h hp hp
    · unfold payable vote; change (_:ℝ) * ((-1:ℝ)*stream I κ V (covers D i)) = -(_ : ℝ)*stream I κ V (covers D i); change ((D.ground i.val).card:ℝ)⁻¹ * ((-1:ℝ)*stream I κ V (covers D i)) = _; ring
    · exact (hp h).elim
    · exact (h hp).elim
    exact zero_mul _
  rw [Meadow.garner, Finset.sum_product]; dsimp only [Equiv.toEmbedding_apply]
  change (∑ s:Seat c,∑ i∈_, (if (strings T.down Y (Meadow.legs s i)).site=x then (1:ℝ) else 0) * opus I (X') κ γ (.inr (Meadow.legs s i)) V)=_
  rw [Fintype.sum_prod_type]; simp_rw [Meadow.tunesAnchor]; apply sum_congr rfl; intro i _
  rw [Finset.sum_comm]; apply sum_congr rfl; intro j _; simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', mem_univ, ↓reduceIte]; rfl

lemma primers (κ:Chi) (γ:ℝ) (ℓ k : ℕ) (x:Site c) : D.tot κ ℓ k γ x = ∑ i∈ D.board ℓ k, Meadow.garnerAt I Y x i • ((Song.plusone I X' κ γ).logRead i) := by
  ext V; unfold tot Meadow.atlas; simp only [Pi.add_apply,Pi.smul_apply,Finset.sum_apply]; unfold Pond.likely; unfold Cabinet.board
  rw [sum_map,sum_product]; simp only [Equiv.toEmbedding_apply]; simp_rw [← D.payee Y κ γ ℓ k]; rw [Finset.mul_sum]; apply sum_congr rfl; intro θ _
  rw [Finset.mul_sum]; apply sum_congr rfl; intro i _
  dsimp only [plusone,Meadow.garnerAt,Function.comp_apply,smul_eq_mul]; rw [Equiv.apply_symm_apply]
  let v:=opus I (X') κ γ i (θ.view V); let w:= Meadow.share I Y ((Meadow.spin θ).symm x) i; change Rim c*(w*v)=w*(Rim c*v); ring

section other
variable (hF : Collection.Local (Beam.marquee I Y) Y (Song.plusone I (Divides.selfA I) κ γ) t w)
include hF
lemma fire (n k : ℕ) (x : Site c) (hB:Y.B=B) : Y.Regular (neighbors (studio b n B) x) (D.tot κ n k γ x):= by
  rw [D.primers Y κ γ]; apply Meadow.regularA; intro i hi; by_cases hv : Meadow.garnerAt I Y x i=0
  · rw [hv,zero_smul]; exact CouplingShape.reg_const _
  exact CouplingShape.reg_scale _ (CouplingShape.reg_extend (hF.smooth i) (D.billed Y i hi hB x hv).2)

-- All regular leftovers. Don't average Y norms directly!
def leftward (κ : Chi) (γ : ℝ) (n k : ℕ) : Collection.Source G c :=
    { (Song.plusone I (X') κ γ) with logRead := fun i=> if i ∈ D.board n k then 0 else (Song.plusone I (X') κ γ).logRead i }

def earned (κ : Chi) (γ : ℝ) (n k : ℕ) (x : Site c) (V : Config G c): ℝ :=
    ∑ i∈D.board n k, Meadow.garnerAt I Y x i * ((Beam.marquee I Y).read (Song.plusone I X' κ γ)|>.regularOccurrence Y i V)

lemma unearned (n k : ℕ) (V : Config G c) :
    ((Y').read Ih).additive Y V=((Y').read (leftward D κ γ n k)).additive Y V + ∑ x, earned D Y κ γ n k x V := by
  let F i:= ((Y').read Ih).regularOccurrence Y i V; let G i:= ((Y').read (D.leftward κ γ n k)).regularOccurrence Y i V; let t i:= if i∈D.board n k then F i else 0
  have he : G=F-t:= by
    funext i; change masked _ _ (if i∈ D.board n k then _ else _) V= F i - (if i∈D.board n k then _ else _); split
    · rw [sub_self]; simp [masked]
    rw [sub_zero]; rfl
  have hs: Summable F := Roof.Embrasure.series _ _ hF V
  have h' : HasSum t (∑ i∈ D.board n k,F i):= by
    convert hasSum_sum_of_ne_finset_zero (s:= D.board n k) (f:=t) (fun i hi=> if_neg hi) using 1; exact sum_congr rfl fun i hi=> (if_pos hi).symm
    infer_instance
  unfold Cabinet.earned; rw [sum_comm]; have hz : ∀ i,(∑ x,Meadow.garnerAt I Y x i* F i)=F i:= by intro i; rw [← sum_mul,Meadow.paysOne,one_mul]
  change (∑' i,F i)=(∑' i,G i) + ∑ i∈ D.board n k, ∑ x,_*F i; simp_rw [hz]
  rw [he]; change _=(∑' i, (F i-t i))+_; rw [(hs.hasSum.sub h').tsum_eq,sub_add_cancel]

omit hF in
lemma total (n k : ℕ) (V:Config G c) (x : Site c) (hB:Y.B=B) (ht : Healthy Y.threshold (neighbors (studio b n B) x) V) : earned D Y κ γ n k x V=D.tot κ n k γ x V := by
  unfold Cabinet.earned; rw [primers D Y κ γ,Finset.sum_apply]; apply sum_congr rfl; intro i hi
  by_cases hV : Meadow.garnerAt I Y x i=0; · rw [hV]; simp
  exact congr_arg _ (masked_eq _ _ _ _ (show _ from ht.mono_left (D.billed Y i hi hB x hV).2))

lemma chalk (n k : ℕ) (V: Config G c) (x : Site c) (hB:Y.B=B) : ‖earned D Y κ γ n k x V‖ ≤ (ballCost (studio b n B):ℝ)*t := by
  obtain ⟨u,hu,hZ⟩:= hF.cheap
  let S:= (Y'); let f i:= (S.read Ih).regularOccurrence Y i V
  let C i:= Meadow.garnerAt I Y x i; let s:= neighbors (studio b n B) x; let E i x:= if (S.reg i).site=x then u i * Real.exp (preExponent Y * coverNumber Y.B (S.reg i).support) else 0
  unfold Cabinet.earned; apply le_trans (norm_sum_le ..)
  calc _ ≤ ∑ i∈D.board n k, ∑ y'∈s,E i y':= by
           apply sum_le_sum; intro i hi; have hp : 0≤∑ x∈s,E i x:=sum_nonneg fun x _=> (hZ x).1 i
           change ‖C i*f i‖ ≤ _; by_cases ht:C i=0; · rw [ht,zero_mul,norm_zero]; exact hp
           have he:= (D.billed Y i hi hB x ht).2
           rw [norm_mul, Real.norm_of_nonneg (Meadow.nonnegative ..)]; apply (mul_le_of_le_one_left (norm_nonneg (f i)) (Meadow.portions ..)).trans; apply (CouplingShape.mask_cost (hu i) V).trans
           apply (le_mul_of_one_le_right (hu i|>.1) (Real.one_le_exp (show 0≤preExponent Y * coverNumber Y.B (S.reg i).support from mul_nonneg (Song.headline Y).exponent_pos.le (Nat.cast_nonneg _)))).trans
           unfold E; rw [sum_ite_eq,if_pos (he (S.reg i).anchor)]
       _ ≤ _ := by
           rw [sum_comm]; apply le_trans (sum_le_sum (fun x _=> budget_sum (hZ x) (D.board n k)))
           rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast neighbors_card ..) hF.H_nonneg
end other
end YM.RGComparison01.Cabinet
