import YM.MSbar.Tonic.Rave
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Tonic
open Function Filter Whisk Lis Measuring Cacao Push Uniform Lattice RG
open Precision Gauge Midpoint Rolling Exterior Wilson Wave
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}{c f:Side}{S:StepData c f}
local notation "J"=> Positions (Primary c G)
local notation "X"=> Primary c G
local notation "Q"=> Config G f
variable (β t:ℝ)(U:Config G f)(M:Config G c)(v:S.Choices)
local notation "B₀"=> tribe S β t U v
local notation "Φ"=> wing S U v
variable (x:Positions (Primary c G))(L:List (Primary c G))(i j:Primary c G)(e:Bond c)
variable (hc:S.patch.Branches S.kernel G)
local notation "H"=>prior G f
include hc
variable (R: Rep G f)(τ A B C D:ℝ)(hR:R.Lawful τ A B C D)
-- density old milk U-term derivative `S likelihood`.
local notation "W"=> fun x:J=> postcard G c t x
local notation "i!"=>R.eval
local notation "q!"=> lid S β t G R v
include hR
variable (hβ:β=R.beta)(hs:∀ U, 0 < R.eval U)
include hs
local notation "Z!"=>rave S β t R L x
open Heath Heath.Stock Heath.Cottage Next.Fluctuations ConnectedActivityE6 Bulk
variable (F:Forest S.ratio)
local notation "Xc"=> Heath.canoe
variable (I Y: Support f)(J': Voice G)(p: Palisade) (ν:Positions (Key F G)){a b r K:ℝ}{n q j:ℕ} (g: Clear G J')
local notation "V₀"=> W x
local notation "Θ"=> hotel F I Y J' V₀ ν a b
local notation "z"=> chambers F Y J' V₀ ν
variable (hP: Posture p J' F a b r K n q I Y (t • x) ν R.p) (ht:∀ i∈L, S.ratio.embed (Measuring.chart c G i) ∈ I)
structure Picked (G:Gauge)(S:StepData c f) (F: Forest S.ratio)(K:ℝ):Prop where
    kind (x:Positions (Joint F G)) : ‖x‖ ≤K→ ∀ t t': S.Choices,S.prediction (fine G F x) t= S.prediction (fine G F x) t'
variable (hp: Picked G S F K)
include g hP ht hp
lemma commit (t':S.Choices)(hh:U∈ Θ) : ∀ i∈L, S.prediction U t' (Lis.rope i)=S.prediction (z U) v (Lis.rope i):=by
   obtain ⟨hb,hs,h,hM,hU⟩:= Cottage.Posture.pose g hP hh; let V':= Heath.canoe (S:=S) F U; intro i hi; let y:= Lis.rope i
   have hp:S.prediction (z U) t'= S.prediction (z U) v:=by
       let P:=rented F Y J' V₀ ν U; let A:=meetVar (t •x) P; have he:z U=fine G F A:=by unfold chambers fine A; rw [paint_meet];rfl
       rw [he]; exact hp.1 _ hs t' v
   have hv:S.prediction V' t'= S.prediction U t':=by unfold V' Heath.canoe; have hz:= (Push.SectorMeasure.choice_gauge hc U t' (F.foldAt U)).2; rw [hz]; ext i; simp [Function.comp,Lattice.gauge,F.fold_root] -- search
   rw [← hv, ←hp]; have h':AgreeNear S.ratio.parent y.1 (predReach S.patch+1) V' (z U):=by
       intro k hK
       obtain ⟨h₁,h₂⟩:=Heath.closeB S hK; have hQ:= ht i hi; have ht:halo (necklace S.patch) {S.ratio.embed y.1} ⊆Y:= (Corona.halo_mono (hP.solid.trans (by omega)) (Finset.singleton_subset_iff.mpr hQ)).trans hP.gazes; exact h k (ht h₁) (ht h₂)
   exact (Emblems.choices V' (z U) y t' t' hc rfl rfl rfl h').2.2
lemma equity (U:Q)(h:U∈ Θ): rave S β t R L x U=strap S β t v x L (z U):=by
    have ht(z':S.Choices) : strap S β t z' x L U= strap S β t v x L (z U):=by apply weave β t U _ x L (z U) v _ rfl; exact fun i hi=> (Tonic.commit t U v x L hc R τ A B C D hR hs F I Y J' p ν g hP ht hp _ h i hi).symm -- order
    apply mul_right_cancel₀ (wealth β t hc R τ A B C D hR hs U x|>.ne'); rw [rents_r β t x L hc R τ A B C D hR hs]; simp_rw [ht, ← Finset.sum_mul]; exact mul_comm ..
variable (hA:Measurable (rave S β t R L x))
lemma scopeY (e:Envelope (rave S β t R L x)) (z':S.Choices) : GaugeLocal S (youth F Y) (Set.indicator Θ (rave S β t R L x)):=by
    let Z:= Set.indicator Θ (rave S β t R L x); let V' := strap S β t z' x L; have hv:=Heath.Cottage.garden_main (A:=a) (B:=b) F I Y J' V₀ ν g hP.extendsX; have hp₁(U:Q)(h:U∈Θ) :Z U= V' (chambers F Y J' V₀ ν U):=(Set.indicator_of_mem h Z!).trans (equity β t z' x L hc R τ A B C D hR hs F I Y J' p ν g hP ht hp U h); refine ⟨Envelope.piece hv.from_here e (Envelope.const _),fun t he i=>?_,fun U V h=>?_⟩
    · by_cases he':i∈ Θ; rw [show Set.indicator _ _ (gauge t i)= _ from hp₁ _ (hv.within t he _|>.mp he'), show Set.indicator _ _ i=_ from hp₁ _ he', Heath.Cottage.invites F I Y J' V₀ ν g hP.extendsX t he]; rw [Set.indicator_of_notMem he',Set.indicator_of_notMem (by intro hc; exact he' (hv.within t he i|>.mpr hc))]
    have hU:U∈ Θ↔V∈ Θ:= Iff.of_eq (hv.localized U V h); by_cases ht:U∈ Θ; exact (hp₁ _ ht).trans ((congr_arg V' (informed F I Y J' V₀ ν g hP.extendsX|>.2.2 U V h)).trans (hp₁ _ (hU.1 ht)).symm); rw [Set.indicator_of_notMem ht,Set.indicator_of_notMem (mt hU.2 ht)]
end YM.MSbar.Tonic
