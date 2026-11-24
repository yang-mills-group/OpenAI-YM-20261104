import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Mantel
/-! Local LTE high-order representation/compatibility on supported tiles. Adapts
`PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Mantel`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Meadow
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F L : Side} {P : Patch} {J₀ M D' : ℕ} {K : Teller G}
variable {S : StepData c f} {T : Tube G S} {p : ℝ} {R R' : RG.Rep G f}
    {a v W q K₀ : ℝ} {J : ConnectedActivityE6.Target G K} {o : ConnectedActivityE6.Target.Order G W} (H : Cash W p a L J o K₀ T R) {χ : Chi}
local notation "B" => radiusB p

structure SeedN (J₀:ℕ) (p:Park c f) : Prop where
  hot : Ac.Spark H.supportP (Mint.hatch S p)
  sizes : p.card≤ J₀
  earns i : i∈p → Mint.verse R.path i≤B -- p rename
structure StirN (J₀:ℕ) (z:Vines c f) : Prop where
  small : z.fst≤ J₀
  each i : SeedN H J₀ (z.2 i)
  moves : coefficient (blocked (Meadow.ground H)) z.2≠0
variable {H}
lemma family_neN {x : Park c f} (hq:SeedN H J₀ x) : x.Nonempty:= by obtain ⟨p,hp⟩:= hq.hot.1; obtain ⟨i,hi,rfl⟩:=mem_map.mp hp; exact ⟨i,hi⟩
lemma ground_neN {x} (hq:SeedN H J₀ x): (Meadow.ground H x).Nonempty:= by
  obtain ⟨i,hi⟩:= family_neN hq; have hz:= Mint.centered J.halo B B (lt_of_lt_of_le (by norm_num) H.laws.data.room.sight.1) i S T R (hq.earns i hi)
  exact ⟨pace S i,Finset.mem_biUnion.mpr ⟨_,mem_map_of_mem _ hi,hz.1⟩⟩
lemma centersN {x} (hq:SeedN H J₀ x) {i} (hi:i∈x): pace S i∈Meadow.ground H x:= Finset.mem_biUnion.mpr ⟨Mint.disc S i, mem_map_of_mem _ hi, (Mint.centered J.halo B B (lt_of_lt_of_le (by norm_num) H.laws.data.room.sight.1) i S T R (hq.earns i hi)).1⟩
def HeirN (y : Park c f) (ht : SeedN H J₀ y) : H.ThinP := ⟨Mint.hatch S y,ground_neN ht,by rw [Mint.unrostered]⟩
lemma seed_heightN {x y:Park c f} (he:SeedN H J₀ x) (hp:SeedN H J₀ y) (h:HeirN x he=HeirN y hp): x=y:= Finset.map_injective (Mint.disc S) (congr_arg Subtype.val h)
def vintageN (z:Vines c f) (hz:StirN H J₀ z): H.fragrances:= ⟨z.1,fun i=>HeirN (z.2 i) (hz.each i)⟩
lemma enrollmentN : Injective (fun i : {z:Vines c f// StirN H J₀ z}=> vintageN i.val i.property):= by
  rintro ⟨⟨i,z⟩,hp⟩ ⟨⟨j,k⟩,hx⟩ he
  change Sigma.mk i _=Sigma.mk j _ at he; obtain rfl : i=j:= congr_arg Sigma.fst he
  injection he with he hh
  have h': z=k:= funext fun i=> seed_heightN (hp.each i) (hx.each i) (congr_fun hh i)
  cases h'; rfl
lemma manaN {p : Vines c f} (h : StirN H J₀ p): coefficient (blocked (Meadow.ground H)) p.2=coefficient H.seam (vintageN p h).2:= by
  apply movement; intro i j; apply or_congr _ Iff.rfl
  exact ⟨fun he=> Subtype.ext (congr_arg (Mint.hatch S) he),seed_heightN (h.each i) (h.each j)⟩

local notation "D" => Mint.width J.halo B B
-- diameter via coverNumber, cluster, startup uses R covariance floor
lemma cover_locN {z} (h : SeedN H J₀ z): coverNumber D (Meadow.ground H z) ≤ J₀:= by
  set A:= Mint.hatch S z
  refine (Ac.cover _ _ h.hot).trans ((sum_le_sum (g:=fun _=>1) (fun i hi=> ?_)).trans ?_)
  · obtain ⟨i,hi,rfl⟩:=mem_map.mp hi; have hx:=h.earns i (by assumption)
    let p:= pace S i
    have he:neighbors D p=halo D ({p}: Finset _):= by ext i; simp only [halo_spec,neighbors_mem]; simp only [mem_singleton]; grind
    have hp : covers D (H.supportP (Mint.disc S i)) {p}:= ⟨he ▸ (Mint.centered J.halo B B (lt_of_lt_of_le (by norm_num) H.laws.data.room.sight.1) i S T R hx).2, Corona.ship_halo _ (fun i hi j hj=> by rw [mem_singleton.mp hi,mem_singleton.mp hj])⟩
    exact (Corona.list_cost _ hp).trans_eq (card_singleton _)
  simp only [sum_const,smul_eq_mul,mul_one,Mint.hatch, Finset.card_map]; exact h.sizes
lemma wagesN {z} (h : StirN H J₀ z) : coverNumber D (Meadow.pasture H z) ≤ (J₀+1)*J₀ := by
  let p:=vintageN z h
  have hx:= connected_pay H.seam H.smallAt D H.testS p.2 zero_le_one (show coefficient H.seam p.2≠0 from manaN h ▸ h.moves)
  unfold Trees.currency at hx; simp_rw [one_mul,← Real.exp_sum,Real.exp_le_exp] at hx; have h(i): (coverNumber D (H.smallAt (p.2 i)):ℝ)≤↑J₀:= by exact_mod_cast cover_locN (h.each i)
  have he:(coverNumber D (Meadow.pasture H z):ℝ)≤↑((J₀+1)*J₀):= by
    refine le_trans hx ((Finset.sum_le_sum (fun i _=> h i)).trans ?_)
    rw [sum_const,nsmul_eq_mul]; simp only [card_univ,Fintype.card_option,Fintype.card_fin]; have hp : p.fst+1≤J₀+1:= by linarith [show p.fst≤J₀ from ‹StirN H J₀ z›.small]
    apply le_trans (mul_le_mul_of_nonneg_right (show ((p.fst+1:ℕ):ℝ) ≤ ↑(J₀+1) from by exact_mod_cast hp) (by positivity : (0:ℝ)≤↑J₀)); norm_num
  exact_mod_cast he

def roomSizeN (J₀ l b:ℕ) := (2*Mint.width l b b)+((J₀+1)*J₀)*(4*Mint.width l b b+2)+2*Mint.width l b b+8
lemma enteredN {z} (h : StirN H J₀ z) (x:Site c) (hx:x∈ Meadow.pasture H z): Meadow.pasture H z ⊆ neighbors (roomSizeN J₀ J.halo B) x:= by
  intro i hi; apply (neighbors_mem ..).2
  have he := wagesN h; apply (Corona.extent _ D hx hi).trans; unfold roomSizeN; exact (add_le_add_left (Nat.mul_le_mul_right _ he) (2*_)).trans (by omega)
end YM.PhysicalNext.Repeat.Meadow
