import YM.LocalLTE.Ballot.Hits
import YM.LocalLTE.Port.Gems
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Blush.Ribbon
/-! Keyed canonical on output. Orientation credit before watermark. Replicated at one chosen root across ALL contribution lamps.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Blush
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Blaze.March Captain Mask Raw Matter Frond Coat Vine
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Brush Foramen
variable {v z r W w s t y η γ B a μ: ℝ} {j n m : ℕ} {Q: YM.ConnectedActivityE6.Target G P}{o: Target.Order G W}{R:Rep G f}
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus
open YM.LocalLTE FrameBox Fan Merge Merge.Palette
open Ovens Trio Gas Ursell Greenbelt Refrain Blaze.March Next.Foundations Progress.DirectedRecipe Daisy Daisy.Charity
-- cost.S.Reals.Inst. Warp for any oriented support with X trombone.
variable (H: Cash W t μ L Q o a T R) (U:Cloud R) (M₀ M₁: Config G f→ℝ)
variable (κ:ℝ)(k l' q r p dα:ℕ)(e:ℕ→ℕ)(X:Grove (0:Site c)) (P':BudgetPoint)
variable (hp:2*(2*(East.stagnate q Q.halo*radiusB t)) ≤ c.val)
noncomputable def cloudBeam (M:Leaf R)(φ: Config G f→ℝ): H.fragrances→ Config G c→ℝ:=fun i=> Fan.beamP (fun _:Unit=> M) (fun _=>φ) H Chi.canonical i κ q k e (fun _=>True) X () r dα hp -- K remove
noncomputable def hull (z:ℂ):ℕ→ Config G c→ℂ:= stuff (enter H) (fun i=> z • (Complex.ofReal ∘ (cloudBeam H κ k q r dα e X hp U.live M₀ i) + Complex.I • (Complex.ofReal ∘ (cloudBeam H κ k q r dα e X hp U.pale M₁ i)))) -- order?
local notation "h0"=> LocalLTE.Dilation.sill P'.supportExponent l'
variable (z:ℂ)
-- Wages. Terrain. Lift from each single plaque. Need cross orientation h.K.High.
local notation "A'"=> Dilation.silhouette (0:Site c) P' l' (scope H U (0:Site c))
local notation "u" i=> locus U.live H 0 i
local notation "Tz" i=> Dilation.silhouette (0:Site c) P' l' (fun _=> locus U.live H 0 i) 0
local notation "u1"=> (cloudBeam H κ k q r dα e X hp U.live M₀)
local notation "u2"=> (cloudBeam H κ k q r dα e X hp U.pale M₁)
local notation "f0" => hull H U M₀ M₁ κ k q r dα e X hp z
local notation "fa" i=> (pane H U z i)
local notation "V₀"=> (Blush.fields H U z)
local notation "P₀"=> (fun i=> z • (Complex.ofReal ∘ (u1 i) + Complex.I • (Complex.ofReal ∘ (u2 i))))
lemma geoT (i: H.fragrances) : A' (enter H i)= Tz i:=by
    unfold LocalLTE.Dilation.silhouette
    rw [show Blush.scope H U 0 (enter H i)= Charity.locus U.live H 0 i from (enter H).injective.extend_apply ..]
variable (hb:P'.B= Pressure.radiusB t)(hh:East.stagnate q Q.halo*radiusB t< l'*radiusB t)(hg:10*(l'*radiusB t)< c.val)(hi:0∈U.live.crest.image S.ratio.parent)
open AnalyticBridge VerifiedReset Collection.Price
-- Root signal.Remembers actual coordinates.
include hi hh hg hb
lemma projected : ∀ i, (∀ k:Bool,Replicated X (East.stagnate q Q.halo*radiusB t) κ (dα+1) (Port.scaleQ k ∘ (f0 i)))∧(f0 i≠0→A' i= neighbors (l'* Pressure.radiusB t) 0):=by
    intro i; have h :0 ∈ U.pale.crest.image S.ratio.parent:= U.turnout ▸ hi; by_cases hx:i∈ Set.range (enter H); swap
    · rw [show f0 i=0 from blank (enter H) (P₀) hx]; exact ⟨fun k=>by rw [show Port.scaleQ k ∘ (0:Config G c→ℂ)=0 from funext fun x=>map_zero _]; exact rp_zero _, fun h=>(h rfl).elim⟩
    obtain ⟨i,rfl⟩:=hx; obtain ⟨h1,h3⟩:= Fan.track (fun _:Unit=> U.live) (fun _:Unit=> M₀) H Chi.canonical i κ q k e (fun _=>True) X P' hb () hi l' r dα hg hp hh -- order
    obtain ⟨h2,h4⟩:=Fan.track (fun _:Unit=> U.pale) (fun _:Unit=> M₁) H Chi.canonical i κ q k e (fun _=>True) X P' hb () h l' r dα hg hp hh
    rw [show f0 (enter H i)= _ from (stuffed (enter H) P₀ i)]
    rw [show A' (enter H i)= _ from geoT H U l' P' i]; constructor
    · intro j; let a:= u1 i; let b:=u2 i
      change Replicated X _ _ _ (Port.scaleQ j ∘ (z • (Complex.ofReal ∘ a+Complex.I • (Complex.ofReal ∘ b))))
      rw [show (Port.scaleQ j ∘ (z • (Complex.ofReal ∘ a+Complex.I • (Complex.ofReal ∘ b))))= Port.scaleQ j z • a + Port.scaleQ j (z*Complex.I) • b from (by funext i; cases j <;>simp [Port.scaleQ,Complex.mul_re,Complex.mul_im])]
      exact rp_add _ (rp_scale _ _ h1) (rp_scale _ _ h2)
    intro hp; by_cases hx:u1 i=0; swap; exact h3 hx
    have hv: u2 i≠0:=fun h=>hp (by rw [hx,h];simp only [show Complex.ofReal ∘ (0:Config G c→ℝ)=0 from funext fun i=> Complex.ofReal_zero,smul_zero,add_zero]); rw [arches H U 0 i]; exact h4 hv
omit hi hh hg hb
-- transition bulk estimate
variable {w':ℝ}
lemma measure (g:ℝ) (h:∃ a:H.fragrances→ℝ, SumBudget (fun i=>Push.Local.reservedMass P' (Dilation.silhouette (0:Site c) P' l' (fun _=>locus U.live H 0 i) 0) (a i)) g∧∀ i,P'.Regular (Dilation.silhouette (0:Site c) P' l' (fun _=>locus U.live H 0 i) 0) (matin U.live H i Chi.canonical-cloudBeam H κ k q r dα e X hp U.live M₀ i)∧ P'.supBounds 0 (Dilation.silhouette (0:Site c) P' l' (fun _=>locus U.live H 0 i) 0) (matin U.live H i Chi.canonical-cloudBeam H κ k q r dα e X hp U.live M₀ i) (a i))
    (h':∃ a:H.fragrances→ℝ, SumBudget (fun i=>Push.Local.reservedMass P' (Dilation.silhouette (0:Site c) P' l' (fun _=>locus U.pale H 0 i) 0) (a i)) g∧∀ i,P'.Regular (Dilation.silhouette (0:Site c) P' l' (fun _=>locus U.pale H 0 i) 0) (matin U.pale H i Chi.canonical-cloudBeam H κ k q r dα e X hp U.pale M₁ i)∧ P'.supBounds 0 (Dilation.silhouette (0:Site c) P' l' (fun _=>locus U.pale H 0 i) 0) (matin U.pale H i Chi.canonical-cloudBeam H κ k q r dα e X hp U.pale M₁ i) (a i)):∃ a:ℕ→ℝ,SumBudget (fun i=> Push.Local.reservedMass P' (A' i) (a i)) (‖z‖*(g+g))∧∀ i,P'.Regular (A' i) ((V₀ - f0) i)∧ P'.supBounds 0 (A' i) ((V₀-f0) i) (a i):=by
   obtain ⟨b,hb,hB⟩:=h; obtain ⟨a,ha,hE⟩:=h'; simp_rw [← arches H U] at ha hE; let v i:= ‖z‖*(a i+b i); have ht:= budget_scale (norm_nonneg z) (budget_plus ha hb)
   let N:= enter H; refine ⟨stuff N v, ?_,fun i=>?_⟩
   · refine transfer_budget N (g:=fun i=>‖z‖*(Push.Local.reservedMass P' (Tz i) (a i)+Push.Local.reservedMass P' (Tz i) (b i))) ?_ ?_ ht
     · intro i; rw [show A' (N i)= _ from geoT H U l' P' i,stuffed]; unfold Push.Local.reservedMass v; ring
     intro i hi; rw [blank _ _ hi, Push.Local.reservedMass,mul_zero]
   by_cases hv:i∈Set.range N; swap
   · rw [Pi.sub_apply, show V₀ i=0 from blank _ _ hv, show f0 i=0 from blank _ _ hv,zero_sub,neg_zero,blank _ _ hv]; exact ⟨Push.Local.regular_const _,by simpa only [norm_zero] using! Push.Local.bound_const (B:=P') (X:= (A' i)) (o:=0) (G:=G) (0:ℂ)⟩ -- edit
   obtain ⟨i,rfl⟩:=hv
   rw [Pi.sub_apply,show V₀ (N i)= _ from (stuffed N (pane H U z) i),show f0 (N i)= _ from (stuffed N (P₀) i),show A' (N i)= _ from geoT H U l' P' i,stuffed]
   let p:= matin U.live H i Chi.canonical - u1 i; let q:= matin U.pale H i Chi.canonical - u2 i
   rw [show pane H U z i- P₀ i=z • (Complex.ofReal ∘ p+ Complex.I • (Complex.ofReal ∘ q)) from (by ext U; simp [pane,p,q]; ring)]
   have hh:= bound_smul Complex.I (pricingG (hE i|>.1) (hE i|>.2)); rw [Complex.norm_I,one_mul] at hh
   have he':=bound_smul z (bound_add (ornate (hB i|>.1)) (regular_smul _ (ornate (hE i|>.1))) (pricingG (hB i|>.1) (hB i|>.2)) hh)
   exact ⟨regular_smul _ (regular_add (ornate (hB i|>.1)) (regular_smul _ (ornate (hE i|>.1)))), by unfold v; rw [add_comm (a i) (b i)]; exact he'⟩
end YM.PhysicalNext.Repeat.Blush
