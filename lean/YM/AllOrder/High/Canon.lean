import YM.AllOrder.High.Ship
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Trio.Tir

/-!
# Bouquet and Clark valuation with all strata. Transfer within Hull by
aligned Career (identity) before the beta-read; pointwise. For applications
with Coast binding Y-axis family across β can instead follow Trio.Card via
catalog choices. Don't assert analytic matching on the indicated Budget yet.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.High
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open PhysicalNext Repeat Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F L₀ : Side} {P : Patch} {M k j m π u d: ℕ} {K : Teller G} {p a W U V g : ℝ} {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
local notation "B" => radiusB p
local notation "τ" => Mint.width X.halo (radiusB p) (radiusB p)
open Meadow (Park spin)

section plane
variable {S:StepData c f} {T: Tube G S} {R : RG.Rep G f} {H : Cash W p a L₀ X o U T R}
variable (F : Finset H.fragrances) (χ:Chi)
local notation "Θ" => (Match.staple (H:=H) (J:=H) rfl rfl rfl)

lemma flip_noop (H : Cash W p a L₀ X o U T R) (x : H.fragrances) : (Match.staple (H:=H) (J:=H) rfl rfl rfl).furrow x=x := by rcases x with ⟨i,k⟩; rfl -- quotation H conflicts

def blossom (k:ℕ): Finset (Magazine H):= disjSum F ((univ ×ˢ (Meadow.ripened T.down B k)).map (Meadow.rollers c).toEmbedding)
def foliage (k:ℕ): Finset ℕ:= (univ ×ˢ (blossom F k)).map (pennant H).symm.toEmbedding
lemma leaves (i:ℕ) : i∈foliage F k ↔ (pennant H i).2∈blossom F k:= by
  unfold foliage; simp only [mem_map_equiv,mem_product]; simp

def heir (γ : ℝ) := opus H Θ χ γ
/-- Symmetrization independent of BudgetPoint choice (`paths.site = s.2`). -/
def chamber (k:ℕ) (γ : ℝ) := Meadow.atlas ((fun x V=> ∑ i∈F.filter (fun i=> x∈perf H i), -(((perf H i).card:ℝ))⁻¹* stream H χ V i)+ Meadow.garner T.down T.low R.beta γ B k)
lemma turns (k:ℕ) (γ:ℝ) : Trio.Mirrors (chamber F χ k γ):= fun _i s v _U=> Meadow.astrolabe _ _ _ (s,v)

def unheard (k:ℕ) (γ: ℝ) (z:Magazine H) : Config G c→ℝ := if z∈blossom F k then 0 else opus H Θ χ γ z
def leftover (k:ℕ) (γ:ℝ) : Collection.Source G c:= ⟨choir (unheard F χ k γ) ∘ pennant H,(plusone H Θ χ γ).hardRead⟩

lemma ledger (γ:ℝ) (i:ℕ) : (leftover F χ k γ).logRead i=(if i∈ foliage F k then 0 else (plusone H Θ χ γ).logRead i) := by
  unfold leftover plusone choir; let y:= Song.pennant H i; change Rim c • ((unheard _ _ _ _ _) ∘ y.1.view)=_; unfold unheard; split
  · rename_i he; rw [if_pos ((leaves ..).2 he)]; ext; simp
  next hz=> rw [if_neg (fun h=> hz ((leaves ..).1 h))]; rfl

variable (Y : BudgetPoint)
lemma coffer (γ:ℝ) (x:Site c) (V:Config G c) :
    (∑ i∈F.filter (fun i=> x∈perf H i), -(((perf H i).card:ℝ))⁻¹* stream H χ V i) + Meadow.garner T.down T.low R.beta γ B k x V=∑ i∈blossom F k, Meadow.share H Y x i * opus H Θ χ γ i V:= by
  unfold blossom; rw [sum_disjSum,sum_map]; apply congr_arg₂ HAdd.hAdd
  · rw [sum_filter]; apply sum_congr rfl; intro i hi
    change _=(if x∈ perf H i then _ else _) * (-1*stream H χ V ((Match.staple (H:=H) (J:=H) rfl rfl rfl).furrow i)); rw [flip_noop]; split_ifs <;> ring
  unfold Meadow.garner; rw [Finset.sum_product]; dsimp only [Meadow.share,Sum.elim]; change _=∑ s:Seat c,∑ i∈_, (if (strings T.down Y (Meadow.legs s i)).site=x then (1:ℝ) else 0)* opus H Θ χ γ (.inr (Meadow.legs s i)) V
  rw [Fintype.sum_prod_type]; simp_rw [Meadow.tunesAnchor]; apply sum_congr rfl; intro i _; rw [sum_comm]; apply sum_congr rfl; intro _ _; simp only [ite_mul,one_mul,zero_mul,sum_ite_eq',mem_univ,↓reduceIte]; rfl
lemma bound_frame (γ:ℝ) (x:Site c): chamber F χ k γ x= ∑ i∈foliage F k, Meadow.garnerAt H Y x i • ((plusone H Θ χ γ).logRead i) := by
  funext V; unfold chamber Meadow.atlas; simp only [Pi.add_apply,Pi.smul_apply,Finset.sum_apply]; unfold likely; unfold foliage; rw [sum_map,sum_product]; simp only [Equiv.toEmbedding_apply]; simp_rw [coffer F χ Y γ, Finset.mul_sum]; apply sum_congr rfl; intro θ _; apply sum_congr rfl; intro i _
  dsimp only [plusone, Meadow.garnerAt, Meadow.honor,Function.comp_apply,smul_eq_mul]; rw [Equiv.apply_symm_apply]; let q:= Meadow.share H Y ((spin θ).symm x) i; let v:=opus H Θ χ γ i (θ.view V); change Rim c*(q*v)=q*(Rim c*v); ring
variable (hB:Y.B=radiusB p) (hc:∀ i∈F,∀ x∈perf H i,perf H i ⊆ neighbors d x) (h : radiusB p + radiusB p ≤ d)
include hc h hB
lemma momentum (x:Site c) (i: Magazine H) (hv: i∈blossom F m) (ht: Meadow.share H Y x i≠0): x∈(Beam.contents H Y i).support ∧ (Beam.contents H Y i).support⊆ neighbors d x := by
  rcases i with i|i
  · have he: x∈perf H i:= by contrapose! ht; exact if_neg ht
    change x∈(Beam.dashboard H i).support ∧ (Beam.dashboard H i).support ⊆_; rw [Beam.see]; exact ⟨he, hc i (inl_mem_disjSum.mp hv) x he⟩
  obtain ⟨⟨s,i'⟩,he,rfl⟩:=mem_map.mp (inr_mem_disjSum.mp hv); have hf : Meadow.melody T.down i'≤ B:= (mem_filter.mp ((mem_product.mp he).2)).2
  let k:= strings T.down Y (Meadow.legs s i'); have he:k.site=x:= by contrapose! ht; exact if_neg ht
  change x∈k.support∧ k.support⊆_
  refine ⟨he ▸ k.anchor,?_⟩; rw [show x=s.2 from he.symm.trans (Meadow.tunesAnchor ..)]; intro x hx; have ht:= (neighbors_mem ..).1 (Meadow.yarn T.down Y s i' hx); apply (neighbors_mem ..).2; omega
lemma artists (x:Site c) (i:ℕ) (hv : i∈foliage F m) (hp:Meadow.garnerAt H Y x i≠0):x∈((Beam.marquee H Y).reg i).support ∧ ((Beam.marquee H Y).reg i).support⊆ neighbors d x:= by
  let p:=Song.pennant H i; let θ:=spin p.1; let u:=θ.symm x
  obtain ⟨hy,hz⟩:=momentum F Y hB hc h u p.2 ((leaves F i).1 hv) hp
  change x∈ Finset.image θ _ ∧ Finset.image θ (Beam.contents H Y p.2).support⊆ _
  refine ⟨mem_image.mpr ⟨u,hy,θ.apply_symm_apply x⟩,fun i hi=>?_⟩; obtain ⟨k,hk,rfl⟩:=mem_image.mp hi; apply (neighbors_mem ..).2
  rw [show x=θ u from (θ.apply_symm_apply x).symm, show separation (θ u) (θ k)=separation u k from ?_]; exact (neighbors_mem ..).mp (hz hk)
  change separation (p.1.1.act u+p.1.2) (p.1.1.act k+p.1.2)=_; rw [separation_translate,separation_signed]
lemma section_frame (γ:ℝ) {y t:ℝ} (hp : Collection.Local (posting Y H) Y (plusone H Θ χ γ) t y) (x:Site c): Y.Regular (neighbors d x) (chamber F χ k γ x) := by
  rw [bound_frame F χ Y]; apply Meadow.regularA _; intro i hi; by_cases hF:Meadow.garnerAt H Y x i=0; · rw [hF,zero_smul]; exact CouplingShape.reg_const _
  have hM:= (artists F Y hB hc h x i hi hF).2; rw [Beam.rewrite_rule] at hM; exact CouplingShape.reg_scale _ (CouplingShape.reg_extend (hp.smooth i) hM)
end plane

section currency
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q: KernelChoices} {hC:C.val=c.val*M} {he:2 ≤ c.val}
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
variable {T : Tube G (stepped Q h)} {T' : Tube G (stepped Q H)} {R:RG.Rep G f} {R':RG.Rep G F}
    {I : Cash W p a L₀ X o U T R} {I' : Cash W p a L₀ X o V T' R'}
    (hC he) (hp:R'.path=R.path) (ht:T'=Deck.re T) (hq:R'.p= R.p) (hζ:R'.beta=R.beta) (χ:Chi) (A:Config G c) (ha:RG.flags (Pressure.temp p) A=∅)
local notation "Z" => splitter (Deck.divides hC)
local notation "R₀" => radiusB p
variable {ℓ n v:ℕ} {r' r s₁ t C' w z e b₁ b₂ b₃ b₄ b₅ b₀ a₁ a₂ a₃ a₄ :ℝ}
    (N : Captain I n r s₁ t C' w z e b₀ a₁ ℓ χ) (N' : Captain I' j r' g b₅ a₂ b₁ b₂ b₃ b₄ a₃ v χ) -- tentative duplicate a expensive fix
include hC he hp ht hq hζ ha χ I I' N N'
lemma compared (π k:ℕ) (X':Site C) (v:ℝ) (hr : clusterBound π τ π + τ ≤ m) (hm:4*m<c.val) :
    chamber (strands π (steady I' π k)) χ k v X' ((L).low.links A)= chamber (strands π (steady I π k)) χ k v ((Z) X') A := by
  let B':= (L).low.links A; have hB (A:Config G c) (ha: RG.flags (Pressure.temp p) A=∅):RG.flags (Pressure.temp p) ((L).low.links A)=∅:= by
    ext i; rw [show i∈RG.flags (Pressure.temp p) ((L).low.links A)↔_ from Deck.flagged hC A i (show c.val>4 from (by have hv:= I.laws.data.room.buys; omega)) (Pressure.temp p),ha]; simp
  let S0:= strands π (steady I π k); let S1:=strands π (steady I' π k) -- 
  have hv E (he':RG.flags (Pressure.temp p) E=∅) i: stream I χ E i= I.trainedPool χ E i:= Eq.symm ((congr_fun (N.permitAverage i).2.2.2.1 E).trans (masked_eq _ _ _ _ (by unfold Healthy; rw [he']; simp)))
  have hh i E (he':RG.flags (Pressure.temp p) E=∅): stream I' χ E i= I'.trainedPool χ E i:= Eq.symm ((congr_fun (N'.permitAverage i).2.2.2.1 E).trans (masked_eq _ _ _ _ (by unfold Healthy; rw [he']; simp)))
  let f (W : Site c) (V : Config G c) := (∑ i∈S0.filter (fun i=>W∈perf I i), -(((perf I i).card:ℝ))⁻¹*stream I χ V i)+Meadow.garner T.down T.low R.beta v B k W V
  let b (θ:Seat c):= f ((spin θ).symm (Z X')) (θ.view A)
  unfold chamber Meadow.atlas; change _=likely b; rw [← Meadow.revolving hC b]; apply congr_arg likely; funext θ
  simp only [b,f,Pi.add_apply]; rw [show θ.view ((L).low.links A)=(L).low.links ((Meadow.pinch hC θ).view A) from Meadow.estuary hC A θ,← Meadow.inverts hC θ]; apply congr_arg₂ HAdd.hAdd
  · let V:=(Meadow.pinch hC θ).view A; have hE: RG.flags (Pressure.temp p) V=∅:= Meadow.covers_field _ _ ha; simp_rw [show (Meadow.pinch hC θ).view A=V from rfl, hh _ _ (hB V hE), hv V hE]
    let x:=(spin θ).symm X'; let hq:= rendition (I:=I) (I':=I') hC he x hp ht hq hζ χ V hE π k hr hm
    exact sumshares (Classical.choice hq) _ _ _ check_steady check_steady (Meadow.garden hC x (by omega)) le_rfl (by omega)
  rw [hζ]; subst T'; exact Meadow.garner_pack hC ..
end currency
end YM.AllOrder.High
