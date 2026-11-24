import YM.MSbar.DeltaM.Town
import YM.MSbar.Pulse.Spot
import YM.MSbar.Lease.Bench
import YM.MSbar.Folia.Script
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Bakery.Film
open Function Filter MeasureTheory Cacao Whisk Kelvin RG Lattice Wilson Tree
open scoped Topology BigOperators Classical ContDiff
open Matrix Further.GaussianScalar Analysis Bakery Lattice Precision Push.Uniform
open Next.SectorChange Heath Bulk Heath.Stock Heath.Cottage
variable {G : Gauge} {c f:Side}{S:StepData c f}{p a :ℕ}
    {T W A B t s u α β Z:ℝ}
set_option quotPrecheck false
variable (J:Voice G) (F : Forest S.ratio)
variable (X Y: Support f) (V: Config G c) (U : Config G f)
local notation "I"=> board F X
local notation "A!"=>↥(board F X)
local notation "ρ!"=> fence F (board F X) G -- ambiguous
local notation "Z!"=> Config G f
local notation "W!"=>IV F (board F X) G
local notation "X!"=> SpaceP F X G
variable (m: SpaceP F X G)
local notation "K!"=>draw F X U m t
variable (ν : Positions (Key F G))(γ:ChartRatio G)
local notation "Y!"=> hotel F X Y J V ν A B
variable (R:Rep G f)(i:S.Choices)
local notation "L"=> rental F J R Y i V ν
local notation "z!"=> clipM F X Y Y! γ t m U
variable (g:LocalRatio γ) (C:Matrix (↥(board F X)× G.ColorIndex) (↥(board F X)× G.ColorIndex) ℝ) 
local notation "φ!"=> fLog F X γ t
local notation "Γ"=> Portal.purse z! (fun w:X!=> fLog F X γ t w m U (rental F J R Y i V ν) C)
local notation "ρ"=>fieldLaw C
local notation "q!"=> twirl F (board F X)
include g
variable (e: Config G f → ℝ)
-- The hypotheses include a seal for Y and a map into the covered contour.
variable (hX:Seal S (youth F Y) (hotel F X Y J V ν A B))
variable (hm:Set.MapsTo (fun t:IV F (board F X) G=> t) {v| twirl F (board F X) v U∈hotel F X Y J V ν A B} (covered γ (orbitJ F X U)))
variable (hA: GaugeLocal S (youth F Y) (rental F J R Y i V ν)) (hc:C.PosDef)
variable (ht:0<t)
include hm ht hA hX hc
local notation "E!"=> t^(Fintype.card ((I) × G.ColorIndex))* modeCost C
omit g hm ht hA hX hc in
lemma mspec : Measurable (fun t:IV F (board F X) G => (twirl F (board F X) t U: Config G f)):=by
   let f: IV F (board F X) G × Config G f→ Config G f := fun p=> twirl F (board F X) p.1 p.2
   have he: Measurable f:=(Heath.Cottage.twirlD F (board F X) G).measurable; change Measurable (f ∘ (fun v:IV F (board F X) G => (v,U))); exact he.comp measurable_prodMk_right
set_option maxHeartbeats 200000 in
lemma flow (he: RG.Envelope e) : Integrable (fun v=>Γ v* e (draw F X U m t v)) (fieldLaw C) ∧
   (∫ y:IV F (board F X) G,(spec Y! (q! y U)*Real.exp (L (q! y U)))*e (q! y U)∂ Heath.Cottage.fence F (board F X) G) =
       t^(Fintype.card (↥(board F X)× G.ColorIndex))* modeCost C*(∫ v,Γ v* e (draw F X U m t v)∂ρ) :=by
   let f(j:IV F (board F X) G):= twirl F (board F X) j U; let Φ:= hotel F X Y J V ν A B
   have hv:Measurable f:=mspec F X U
   obtain ⟨hΘ,hH⟩:= exposed f (orbitJ F X U) γ g m C Φ e (rental F J R Y i V ν) hc hX.from_here hv hA.currency he (show f⁻¹' Φ ⊆ covered γ _ from fun i h=> hm h) ht
   have hp(j:W!): palette Φ f (rental F J R Y i V ν) e j = (spec Φ (f j)*Real.exp (L (f j)))*e (f j):=by
       unfold palette; by_cases he:f j∈Φ; rw [show spec Φ (f j)=1 from Set.indicator_of_mem he _,Set.indicator_of_mem he,one_mul]; rw [show spec Φ (f j)=0 from Set.indicator_of_notMem he _,Set.indicator_of_notMem he,zero_mul,zero_mul]
   simp_rw [hp] at hH; exact ⟨hΘ,hH⟩
lemma turning (he: RG.Envelope e)(hp: U∈hotel F X Y J V ν A B) : Rota.resample F (board F X) (woolModel F X J R Y i V ν A B) (hotel F X Y J V ν A B) e U= (∫ y,Portal.purse z! (fun w:X!=> fLog F X γ t w m U (rental F J R Y i V ν) C) y* e (draw F X U m t y)∂fieldLaw C)/(∫ y,Γ y ∂ fieldLaw C):=by
   let f(y:Config G f):= spec Y! y *Real.exp (L y); let I₀:=↥(board F X); let M(U):=∫ t:IV F (board F X) G,f (twirl F (board F X) t U)∂Heath.Cottage.fence F (board F X) G
   have hh(v:IV F (board F X) G) : M (q! v U)=M U:=by unfold M; simp_rw [ends]; exact (climber F (board F X) G v).integral_comp (Homeomorph.mulRight v|>.measurableEmbedding) (fun z=>f (q! z U))
   have hx := (flow J F X Y V U m ν γ R i g C e hX hm hA hc ht he).2; have hs:=(flow J F X Y V U m ν γ R i g C (fun _=>1) hX hm hA hc ht (RG.Envelope.const 1)).2
   let x:ℝ:=t^(Fintype.card (↥(board F X)×G.ColorIndex))*modeCost C; have hK:0<x:=mul_pos (pow_pos ht _) (modeCost_pos hc); simp only [mul_one] at hs
   unfold Rota.resample Rota.ghat; rw [show spec Y! U=1 from Set.indicator_of_mem hp _]; simp_rw [one_mul]
   change (∫ v:IV F (board F X) G,(f (q! v U)/M _)*e _∂_)=_; simp_rw [hh,div_mul_eq_mul_div, integral_div]; rw [show (∫ v:IV F (board F X) G,f (q! v U)*e _∂ Heath.Cottage.fence F (board F X) G)=x* _ from hx,show M U=_ from hs];exact mul_div_mul_left _ _ hK.ne' 
end YM.MSbar.Bakery.Film
