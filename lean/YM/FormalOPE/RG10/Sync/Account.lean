import YM.FormalOPE.RG10.Sync.Rank
/-!
 # Open recurrent chart transfers remain finite rank at fixed horizon
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Sync
open Filter Topology MeasureTheory Function
open PertExtension.GaussianScore MultiGauge MultiGauge.Splice MultiGauge.Papers
open YM.Multi.Vacuum.Gauss
open Route PowerSeries Finset MarkovChain MarkovChain.Warp OpenSlots
open scoped Classical ContDiff Topology BigOperators ENNReal
variable {F K:Type}[NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F][MeasurableSpace F][BorelSpace F]
 [NormedAddCommGroup K][NormedSpace ℝ K]
open stock
lemma calculated (Γ:Law F)(μ:Measure F)[Measure.IsAddHaarMeasure μ] {w:Ticket (F×K)}{j:ℕ}(h: stock j w): stock j (simpleMean Γ μ w):= by
 intro B H L r; let i:=LinearMap.id (R:=ℝ) (M:=F)
 have he:= moving Γ ordinary L i μ w; rw [show boost (accompany i) w=w from by apply Stack.into; intro x; rw [caught]; rfl] at he; rw [←he]; exact Guard.moved _ _ (h _ _ _)

open PertExtension Precision Inherit Push.Loops Chart Lattice RG PowerSeries BlockGauge MultiGauge.Blocking Fabric OpenSlots.Quadratic
variable {G: Gauge} {c f : Side}
variable {S: StepData c f}
variable {I B:Type}[Fintype I] [Fintype B]
variable (J:ChartRatio G) (t:S.Choices)(P:Inside S.ratio)
variable (L:Layout I (Flats G f))(Q: Layout B (Flats G c))
variable (w:PowerSeries ℝ) (U:Unmasked G f)
lemma root : stock 0 (initialFull G f w).W:= stock.owned w firstBill first_held
local notation "K"=> gated P U t w
local notation "F"=> Cross (G:=G) S P
variable (u: stock 0 U.W) (H:S.patch.Branches S.kernel G)
include u H
lemma reinforced : stock 0 (receipt P t J w U):= stock.mul (stock.mul (bought (blankRight P) u) (bought _ (revived G J (Blocking.Index S P)))) (owned w _ (subStill P t H))
lemma powered (h:(core K).RespectsPrice) : stock 0 (Update P t J w U h).W:= by unfold Update; rw [stationed]; exact calculated _ _ (bought _ (reinforced J t P w U u H))
lemma eligible (h:(core (gated P U t w)).RespectsPrice)(r:ℕ): Episode.Eligible (Engine J t P L Q w U h) r where
 rank:= bought _ (canteen (bought (Quadratic.center _ h) (reinforced J t P w U u H))) _ (across L Q) r -- inspect order
 spur i:= spur_rank L (across L Q) (shelter t P w U h) i r
lemma transfers (h:(core K).RespectsPrice)(hJ:LocalRatio J)(up: incline U.W){A: Ticket (Flats G f)}{d:ℕ}(ha:stock d A): stock d (Broadcast P t J w U h (boost (blankRight P) A)):= by
 intro I H0 Q r; rw [available J t P ordinary Q w U hJ up]; exact Episode.Eligible.forward _ r _ (eligible J t P ordinary Q w U u H h r) (ha _ _ _)
-- upright rank without assuming any extent estimates
 def Coherent {n:Side}{L:Fabric G n}(T:Cloth L) (J:ChartRatio G)(U:Unmasked G n)(A: Ticket (Flats G n))(w:L.Cost→PowerSeries ℝ)(h:Commission J T U w)(j:ℕ): Prop:=
 stock j A ∧ stock 0 U.W ∧ match T with
 | .floor _ _ _=> True
 | .inLayer (t:=t) P C=> Coherent C J (Update P t J (w none) U (Exists.choose h)) (Broadcast P t J (w none) U (Exists.choose h) (boost (blankRight P) A)) (w∘some) (Exists.choose_spec h) j
omit u H
lemma persist {n:Side}{L:Fabric G n} (B:Cloth L)(w:L.Cost→PowerSeries ℝ) (U:Unmasked G n)(h:Commission J B U w)(hJ:LocalRatio J)(A:Ticket (Flats G n))(j:ℕ)(hp:stock j A)(hu:stock 0 U.W)(hc:incline U.W): Coherent B J U A w h j:= by
 cases B with
 | floor=> exact ⟨hp,hu,trivial⟩
 | @inLayer c f S H t hf L P C=>
   rw [Coherent]; exact ⟨hp,hu,persist C _ _ _ hJ _ j (transfers J t P _ U hu H _ hJ hc hp) (powered J t P _ U hu H _) (funded hJ _ hc _)⟩ -- argument order
termination_by structural B
end YM.FormalOPE.RG10.Sync
