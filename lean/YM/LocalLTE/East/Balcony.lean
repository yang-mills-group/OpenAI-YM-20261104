import YM.LocalLTE.East.Frequencies
/-! Orbit radius inward. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.East
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March Match
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open Height LocalLTE.Fan Pastel -- namespace edit
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f L : Side} {T₀ : Patch} {ℓ k j n: ℕ} {K : Teller G} {s a W U V g C' y A M K₀ r β δ q b v σ t w Λ γ: ℝ} {m : ℕ}
variable {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
variable {S:StepData c f} {T:Tube G S} {R R' : RG.Rep G f} (H : Cash W s a L X o U T R) {I: Cash W s a L X o U T R'} {χ : Chi}
local notation "B" => radiusB s
def ratioX (b : ℕ) := b+13
local notation "D"=> ratioX X.halo * B
-- outward shore cost Kro.
lemma stanza (Y:Finset (EBill c f))(p:H.ThinP)(he:Credits H p Y ℓ) : ∀ i∈ Y, let x:= East.traceO S R i
    x∈ H.supportP (elastic i) ∧ H.supportP (elastic i) ⊆ neighbors D x:=by
   have hB:0 < B:= Brim.paidB H
   intro i hi x
   rcases i with i|i; swap
   · have hh:= Mint.centered X.halo B B hB i S T R (he.stretch i hi)
     have hx: elastic (Sum.inr i)=Mint.disc S i:=by rcases i with i|i|i|i <;>rfl
     rw [hx]; refine ⟨hh.1,Subset.trans hh.2 fun z hz=> (neighbors_mem ..).mpr (((neighbors_mem ..).mp hz).trans ?_)⟩; unfold ratioX Mint.width; nlinarith
   let p:= R.activities.reg i; let q:= S.ratio
   change x∈(Brim.plate H i).support ∧ _; refine ⟨(Brim.plate H i).anchor,fun z hz=>?_⟩
   obtain ⟨u,hu,hh⟩:= halo_spec.mp (Footprint.inspected_price q X.halo B p.support hB hz)
   obtain ⟨u,hu₁,rfl⟩:= mem_image.mp hu
   have hc: separation x (q.parent u) ≤ B+1:= Nat.le_of_mul_le_mul_left ((Corona.foreshorten q p.site u).trans (by rw [mul_add,mul_one]; exact Nat.add_le_add_right ((neighbors_mem ..).mp (he.track i hi hu₁)) _)) q.count.property
   apply (neighbors_mem ..).mpr ((separation_triangle x (q.parent u) z).trans _); unfold ratioX; nlinarith only [hh,hc,hB]
lemma zoom (Y:Finset (EBill c f))(p:H.ThinP)(he:Credits H p Y ℓ) : coverNumber D (H.unionP p.val) ≤ ℓ:= by
    have hp: p.val.card=Y.card:= by rw [he.lift,arm,card_image_of_injective _ runOut]
    refine (Ac.cover _ _ he.burns).trans ((sum_le_sum (g:=fun _=>1) (fun i hi=>?_)).trans ?_)
    · rw [he.lift] at hi; obtain ⟨v,hv,rfl⟩:=mem_image.mp hi; let u:= East.traceO S R v
      refine (Corona.list_cost _ (show covers D (H.supportP (elastic v)) {u} from ?_)).trans_eq (card_singleton _)
      have h:= stanza H Y p he v hv; exact ⟨fun y hy=> halo_spec.mpr ⟨u,mem_singleton_self _,(neighbors_mem ..).mp (h.2 hy)⟩, Corona.ship_halo _ (fun i hi j hj=> by rw [mem_singleton.mp hi,mem_singleton.mp hj])⟩
    rw [sum_const,hp]; simpa using he.received

def stagnate (m l:ℕ):ℕ:= 2*ratioX l+(m+1)*m*(4*ratioX l+2)
lemma stations (ℓ :ℕ)(u:H.fragrances)(h:Orchestra H u ℓ) (x:Site c) (hx:x∈ Captain.reachability u): Captain.reachability u ⊆ neighbors (stagnate ℓ X.halo*B) x:=by
  have hz(i): (coverNumber D (H.smallAt (u.2 i)):ℝ)≤↑ℓ:= by exact_mod_cast zoom H _ _ (h.each i)
  have hu:=(connected_pay H.seam H.smallAt D H.testS u.2 zero_le_one h.nonempty)
  unfold Trees.currency at hu; simp_rw [one_mul,← Real.exp_sum,Real.exp_le_exp] at hu
  have hf:(coverNumber D (Captain.reachability u):ℝ)≤ ↑((ℓ+1)*ℓ):= by
     refine hu.trans ((sum_le_sum (fun i _=> hz i)).trans ?_); rw [sum_const,nsmul_eq_mul, card_univ,Fintype.card_option,Fintype.card_fin,Nat.cast_mul]; exact mul_le_mul_of_nonneg_right (show ((u.fst+1:ℕ):ℝ) ≤ ↑(ℓ+1) from by exact_mod_cast Nat.succ_le_succ h.length) (by positivity)
  have hg: coverNumber D (Captain.reachability u) ≤(ℓ+1)*ℓ := by exact_mod_cast hf
  intro y hy; apply (neighbors_mem ..).2
  refine (Corona.extent _ D hx hy).trans ?_; unfold stagnate
  refine le_trans (add_le_add_left (Nat.mul_le_mul_right _ hg) _) ?_; have hB:=Brim.paidB H; nlinarith only [hB,Nat.mul_le_mul_left ((ℓ+1)*ℓ) (show 1≤B from hB)]
lemma speaker (u:H.fragrances) (ℓ:ℕ) (h: Orchestra H u ℓ) (j)(i) (hi:i∈ East.docket H u j) (o:Site c)(hp:o∈Captain.reachability u) : separation o (traceO S R i) ≤ stagnate ℓ X.halo * B:= by
   have he:=h.each j
   apply (neighbors_mem ..).1 (stations H ℓ u h o hp (?_)); exact mem_biUnion.mpr ⟨j,mem_univ _, show traceO S R i∈H.unionP (u.2 j).val from mem_biUnion.mpr ⟨elastic i,he.lift.symm ▸ (mem_image_of_mem _ hi), (stanza H _ _ he i hi).1⟩⟩ -- edits
end YM.PhysicalNext.Repeat.East
