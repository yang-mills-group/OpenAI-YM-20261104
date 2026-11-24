import YM.RG01Estimate.GemMint
/-!
 # Supply stencil from surviving short crew: represents all canon lowers with coverage
 (price exponents orientation occupancy exact). E analyst never presumes adding unmasked
 terms globally. Packet authors supply all short kernels & tilt gauge cross-basis.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Evoc
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter PhysicalNext.Repeat Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March Song
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration Meadow Abacus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{Γ: Type}{c f C F L'': Side}{P: Patch}{M D':ℕ}{K:Teller G}
variable {S:StepData c f}{T:Tube G S}{R: RG.Rep G f} {ρ W a u:ℝ}
variable {X:ConnectedActivityE6.Target G K}{o:ConnectedActivityE6.Target.Order G W}
    (I: Cash W ρ a L'' X o u T R)(Q:Lex Γ f)(m:ℕ)
local notation "B" => radiusB ρ

def board (V:Finset Γ)(k:ℕ): Finset (Magazine I):= disjSum ((titleQ I Q (Fate.steps m) V k).map (cask I Q (Fate.steps m))) ((univ ×ˢ (ripened T.down B k)).map (rollers c).toEmbedding)
variable (E:Set ℕ)(h:Record Γ S R Q E)

local notation "M'" => (Match.staple (H:=I) (J:=I) rfl rfl rfl)
-- confirm defeq
lemma pillar (z:I.fragrances): (M').furrow z=z:= by obtain ⟨i,u⟩:= z; congr -- edit

include h
lemma membership (V:Finset Γ)(k:ℕ)(z:Magazine I)(hp:z∈board I Q m V k): Pruned.chosen I (M') E m z:= by
   unfold board at hp; unfold Pruned.chosen; rcases z with z|z
   · obtain ⟨i,hi,hz⟩:=mem_map.mp (inl_mem_disjSum.mp hp); dsimp only [Sum.elim]; rw [pillar I]
     exact (Evoc.scroll I Q (Fate.steps m) _ h _).2 ⟨i,hz⟩
   exact le_of_not_gt (show ¬ B< arc T.down z from Meadow.notKept (I:=I) (.inr z) (m:=k) (inr_mem_disjSum.mpr (inr_mem_disjSum.mp hp))) -- use proof

lemma exhausts (V:ℕ→ Finset Γ)(hv:∀ i, ∀ᶠ k in atTop,i∈ V k) (z:Magazine I) (ht: Pruned.chosen I (M') E m z): ∀ᶠ k in atTop, z ∈ board I Q m (V k) k:= by
   rcases z with z|z
   · unfold Pruned.chosen at ht; dsimp only [Sum.elim_inl] at ht; rw [pillar I] at ht
     obtain ⟨z,hz⟩:= (Evoc.scroll I Q (Fate.steps m) E h _).1 ht; subst hz -- error
     filter_upwards [retiring I Q (Fate.steps m) V hv z] with i hi; exact inl_mem_disjSum.mpr (mem_map_of_mem _ hi)
   filter_upwards [Meadow.unfurls (I:=I) (.inr z) (show ¬ B< arc T.down z from not_lt.mpr ht)] with i hi; exact inr_mem_disjSum.mpr (inr_mem_disjSum.mp hi)

variable (χ:Chi)(P: BudgetPoint)(γ:ℝ)(k:ℕ)(Z:Finset Γ)
     {d n:ℕ} (hq:StageMask R S Q d) (he:P.B=radiusB ρ)
-- exposure for both ξ
lemma pollen (x:Site c)(V:Config G c):
    ∑ i∈board I Q m Z k, Meadow.share I P x i * Pruned.regLow I χ (M') E m γ i V =
    garnet I Q (Fate.steps m) χ Z k x V+Meadow.garner T.down T.low R.beta γ B k x V:= by
    let t:=board I Q m Z k; have hj : ∀ i∈t,Pruned.regLow I χ (M') E m γ i= opus I (M') χ γ i:= fun i hi=> if_pos (membership I Q m E h Z k i hi)
    rw [Finset.sum_congr (s₂:=t) (g:=fun i=>Meadow.share I P x i* opus I (M') χ γ i V) rfl (fun i hi=>congr_arg _ (congr_fun (hj i hi) V))]
    unfold t board; rw [sum_disjSum,sum_map,sum_map]; apply congr_arg₂ _
    · unfold garnet; rw [Finset.sum_filter]; refine Finset.sum_congr rfl fun i hi=> ?_
      let u:= cask I Q (Fate.steps m) i; let f:=Song.perf I u; have he:f=arborX I Q i.val:=rfl
      change (if x∈f then (f.card:ℝ)⁻¹ else 0)* ((-1:ℝ)*stream I χ V ((M').furrow u))= _
      rw [he,pillar I u]; split_ifs
      · change _= _ * stream I χ V u; ring
      rw [zero_mul]
    unfold Meadow.garner; rw [Finset.sum_product]; dsimp only [Meadow.share,Sum.elim]; change (∑ s:Seat c,∑ i∈_, (if (strings T.down P (legs s i)).site=x then (1:ℝ) else 0) * opus I M' χ γ (.inr (legs s i)) V)= _
    rw [Fintype.sum_prod_type]; simp_rw [Meadow.tunesAnchor]; apply sum_congr rfl; intro i _
    rw [Finset.sum_comm]; apply sum_congr rfl; intro j _; simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', mem_univ, ↓reduceIte]; rfl

local notation "q" => (board I Q m Z k)
-- geometry purchase through factor with required shell
variable (hn: house X.halo (radiusB ρ) d (Fate.steps m) ≤ n) (hy: Meadow.studio X.halo (radiusB ρ) ≤ n)
include hq hn hy he
omit h in
lemma sits : ∀ i∈ q, ∀ x : Site c, Meadow.share I P x i ≠ 0 → (Beam.contents I P i).support ⊆ neighbors n x := by
   rintro (i|i) hi x ht
   · obtain ⟨w,hw,rfl⟩:= mem_map.mp (inl_mem_disjSum.mp hi); change (Beam.dashboard I _).support ⊆ _; rw [Beam.see]; let u:=arborX I Q w.val
     have hp:x∈u:= by_cases (fun h:x∈u=> h) (fun h=> False.elim (ht (show (if x∈ Song.perf I ((Evoc.cask I Q (Fate.steps m)) w) then _ else 0)=0 from if_neg h))) -- type amounts
     intro j hj; exact (neighbors_mem ..).mpr (((neighbors_mem ..).mp (within I Q _ hq x w.property hp (show j∈u from hj))).trans hn)
   intro j hj; exact (neighbors_mem ..).mpr (((neighbors_mem ..).mp ((Meadow.modest I P x (.inr i) (m:=k) (inr_mem_disjSum.mpr (inr_mem_disjSum.mp hi)) he ht).2 hj)).trans hy)

def node : Abacus.Rack (Beam.marquee I P) n (Caddy.cut χ I M' γ E m (board I Q m Z k)):= Caddy.rack P χ I M' γ E m n (board I Q m Z k) (sits I Q m P k Z hq he hn hy)
-- arguments check h unused
lemma pasture : (node I Q m E χ P γ k Z hq he hn hy).polygon=Evoc.aspect I Q (Fate.steps m) χ γ Z k:= by
   funext x V; unfold aspect Meadow.atlas Abacus.Rack.polygon node
   simp only [Caddy.rack,Caddy.entries,Finset.sum_apply]; rw [Finset.sum_map,Finset.sum_product];
   unfold likely; simp only [Pi.add_apply,Finset.mul_sum]; refine sum_congr rfl (fun θ ht=>?_)
   let W:= P; let y:= (Meadow.spin θ).symm x
   rw [show (garnet I Q (Fate.steps m) χ Z k y (θ.view V))+Meadow.garner T.down T.low R.beta γ (radiusB ρ) k y (θ.view V)= _ from (pollen I Q m E h χ P γ k Z y (θ.view V)).symm]
   rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun i hi=>?_); unfold Caddy.cut Meadow.garnerAt
   simp only [Equiv.toEmbedding_apply,Function.comp_apply, Pi.smul_apply,smul_eq_mul,pennant, Equiv.apply_symm_apply]; change Meadow.share I P y i *(Rim c*_)=Rim c*(Meadow.share I P y i * _); simp only [Function.comp_apply,if_pos hi]; ring
end YM.RG01Estimate.Evoc
