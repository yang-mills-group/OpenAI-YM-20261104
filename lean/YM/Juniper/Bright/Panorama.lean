import YM.Juniper.Bright.Light
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Duet
/-!
 # Completing outer sym (all V) of the finite selection from the REAL Ledger

 Include PATH & previous lower reset contribution (signed with γ). Supports
 numbered by the original Pennant using the *same* Chit locals; we can choose
 path tails exactly. Build faithful tail budget. Still need mask attachments.
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Bright
open ConnectedActivityE6 Blaze Silica March Captain PhysicalNext PhysicalNext.Repeat Height
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Shoot SliceRows Control Pulse Mask Raw Matter Pond Gas Ursell Trees Reserves Greenbelt Deck Mint Shield Stained
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Extra.Iteration Animals Corona Match Song Meadow
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G: Gauge} {c f L : Side} {P:Teller G}
      {W μ x C s t δ:ℝ} {χ:Chi}{Q: ConnectedActivityE6.Target G P} {o:Target.Order G W}
      {j n k m:ℕ} {S : StepData c f} {T:Tube G S} {R: Rep G f}
   {I:Cash W x μ L Q o C T R}

abbrev blank (I:Cash W x μ L Q o C T R): Alliance I I 1 0:= Match.staple rfl rfl rfl
lemma every (z:I.fragrances): (blank I).furrow z=z:=by rcases z with ⟨a,v⟩; congr

def living (χ:Chi) (I:Cash W x μ L Q o C T R)(k:ℕ) {n:ℕ}(Y:Shelf I n)(p:ℕ)(m:ℕ)(v:ℝ) := Meadow.atlas (Bright.Ledger k Y χ + Meadow.garner T.down T.low R.beta v p m)
noncomputable abbrev lightBook (p m:ℕ)(T: PathData G)(c:Side):= ((univ ×ˢ (Meadow.ripened T p m))).map (Meadow.rollers c).toEmbedding
abbrev selection (Y:Shelf I n)(k p m:ℕ) := disjSum (Y.slate k) (lightBook p m T.down c)
noncomputable abbrev lantern (I:Cash W x μ L Q o C T R) (K: Finset (Song.Magazine I)) := (univ ×ˢ K).map (pennant I).symm.toEmbedding
lemma garden_walk (K: Finset (Magazine I))(i:ℕ): i∈ lantern I K ↔ (pennant I i).2 ∈ K := by simp [lantern,mem_map_equiv]

variable (B : BudgetPoint)
lemma splicing (v:ℝ)(a:Site c)(k p m:ℕ)(χ : Chi) (Y:Shelf I n)(V:Config G c):
    Bright.Ledger k Y χ a V + Meadow.garner T.down T.low R.beta v p m a V = ∑ i∈selection Y k p m, Meadow.share I B a i * opus I (blank I) χ v i V:=by
    rw [selection, Finset.sum_disjSum]
    apply congr_arg₂ (·+·)
    · unfold Bright.Ledger; rw [Finset.sum_filter]; apply sum_congr rfl; intro i hi
      have hp: opus I (blank I) χ v (Sum.inl i) V= -(stream I χ V i):= by simp [opus, Song.sequence,Bright.every]
      by_cases he:a∈Captain.reachability i; · rw [if_pos he,hp]; unfold beaconLeft; change _= (if _ then (↑(Captain.reachability i).card:ℝ)⁻¹ else 0)*_; rw [if_pos (show a∈Song.perf I i from he)]; ring
      rw [if_neg he,show Meadow.share I B a (.inl i)= (0:ℝ) from if_neg he,zero_mul]
    unfold Meadow.garner; rw [lightBook, Finset.sum_map, Finset.sum_product]; change _=∑ s:Seat c,∑ i∈_, (if (strings T.down B (legs s i)).site=a then (1:ℝ) else 0) * opus I (blank I) χ v (.inr (legs s i)) V
    rw [Fintype.sum_prod_type]; simp_rw [Meadow.tunesAnchor]; apply sum_congr rfl; intro i _; rw [Finset.sum_comm]; apply sum_congr rfl; intro j _; simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',mem_univ,↓reduceIte]; rfl
lemma candles (v:ℝ)(a:Site c)(k p m:ℕ)(χ : Chi) (Y:Shelf I n) :
    living χ I k Y p m v a= ∑ i∈lantern I (selection Y k p m), Meadow.garnerAt I B a i • (plusone I (blank I) χ v).logRead i:=by
  ext x; unfold living Meadow.atlas; simp only [Pi.add_apply,Pi.smul_apply,Finset.sum_apply]; unfold Pond.likely; rw [lantern, Finset.sum_map, Finset.sum_product]; simp only [Equiv.toEmbedding_apply]; simp_rw [splicing B v _ k p m χ Y, Finset.mul_sum]; apply sum_congr rfl; intro θ _; apply sum_congr rfl; intro i hi; dsimp only [plusone,Meadow.garnerAt, Meadow.honor, Function.comp_apply,smul_eq_mul]; rw [Equiv.apply_symm_apply]; change Rim c * (_ * _) = _ * (Rim c * _); exact mul_left_comm _ _ _
lemma candles_size (hk:B.B=radiusB x) (Y:Shelf I n)(h₀:Shelf.terrace n k ≤ j)(hm:2*radiusB x ≤ j)(a:Site c)(J:ℕ)(hi:J∈ lantern I (selection Y k B.B m))(h:Meadow.garnerAt I B a J ≠ 0):
    a∈ ((posting B I).reg J).support ∧ ((posting B I).reg J).support ⊆ neighbors j a:=by
   let p:= pennant I J; let o:= (Meadow.spin p.1).symm a
   have he:Meadow.share I B o p.2≠0:= h; have ht:p.2∈selection Y k B.B m:= (garden_walk ..).1 hi
   have hu: o∈(scaleT B I p.2).support ∧ (scaleT B I p.2).support⊆neighbors j o:= by
      cases H:p.2 with
      | inl v =>
        rw [H] at he ht; have h₂:o∈Captain.reachability v:= of_not_not (fun h'=> he (if_neg h'))
        exact ⟨h₂, (fun i hi=> (neighbors_mem ..).2 (((neighbors_mem ..).1 (Y.fit ((Shelf.in_slate Y).1 (inl_mem_disjSum.mp ht)) o h₂ hi)).trans h₀))⟩
      | inr i =>
        rw [H] at he ht; obtain ⟨⟨a,u⟩,hy,hS⟩:=mem_map.mp (inr_mem_disjSum.mp ht); subst i
        have he:(strings T.down B (legs a u)).site=o:=of_not_not (fun h'=>he (if_neg h')); have hx: melody T.down u ≤ B.B:= (mem_filter.mp (mem_product.mp hy).2).2
        refine ⟨he ▸ ((strings T.down B (legs a u)).anchor),fun i hi=> ?_ ⟩; rw [show o=a.2 from he.symm.trans (tunesAnchor ..)]
        have hq := (neighbors_mem ..).1 (Meadow.yarn T.down B a u hi); exact (neighbors_mem ..).2 (hq.trans (by omega))
   let φ:= spin p.1; refine ⟨?_ ,?_ ⟩
   · exact mem_image.mpr ⟨o,hu.1,(φ).apply_symm_apply _⟩
   intro i hi; obtain ⟨y,hY,rfl⟩:=mem_image.mp hi; apply (neighbors_mem ..).2; change separation a (φ y) ≤ _; rw [show a=φ o from (φ.apply_symm_apply _).symm] -- danger o def
   have hy : separation (φ o) (φ y)=separation o y:= by change separation (p.1.1.act o+p.1.2) (p.1.1.act y+p.1.2)=_; rw [separation_translate,separation_signed]
   rw [hy]; exact (neighbors_mem ..).1 (hu.2 hY)
lemma seen (hk:B.B=radiusB x) (Y:Shelf I n)(h₀:Shelf.terrace n k ≤ j)(hm:2*radiusB x≤ j)(a:Site c)(h : Collection.Local (posting B I) B (plusone I (blank I) χ s) t δ):
    B.Regular (neighbors j a) (living χ I k Y B.B m s a):=by
  rw [candles B]; refine Meadow.regularA _ fun i hi=> ?_; by_cases he: Meadow.garnerAt I B a i=0; · rw [he,zero_smul]; exact CouplingShape.reg_const _
  exact CouplingShape.reg_scale _ (CouplingShape.reg_extend (h.smooth i) (candles_size B hk Y h₀ hm a i hi he).2)
end YM.Juniper.Bright
