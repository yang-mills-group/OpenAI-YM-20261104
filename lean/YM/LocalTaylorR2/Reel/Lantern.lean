import YM.LocalTaylorR2.Reel.Boon
import YM.UVExt.OpenDais
/-!
 # Principal (includes inherited, mask-op) and FULL inheritance feedback on any shadow E evaluation. Not just where there is no retained field. True hit expenditures of Ω. Marker variation separately after V. `Track` Lip.* applies on admissible post Level with all history clocks frozen. Counts `tuck` at floor `≥3`. Horizon allowed before Cultivation. No assuming theorem about the Reps approximating the law. This pays the stability of all E parts of the main interaction and their pricing from same `Lamp`. No perturbative field-g law claimed.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Reel
open Function Filter Set Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open PhysicalNext PhysicalNext.Repeat
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March Captain
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof
open Progress.DirectedRecipe Ovens Time UVNext UVNext.CouplingReset Daisy.Charity.RG12 Tail
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open CalendarStep
local notation "❖" => Chi.canonical
section anchor
variable {G:Gauge}{M:Metals G}{D:Rolls M.p}{A:Alloy M D}(R: Roost.Factor A){m n N:ℕ}
  {x y: RG.Rep G (A.B.a.S.side (m+1) n)} (hm:m<N)(hh: PartialLives A.B.bake N (m+1) n x)(hb:x.beta∈band A.B.a (m+1))
  (I:Opera.Guide A.B R.shape N m n y) (he : x.path=y.path)(hP:y.activities.reg=x.activities.reg)(hK:y.activities.forced=x.activities.forced)(hp:Mallow.RG12.Earned (ticketD G) R.shape A.delay)(h:Opera.Guide A.B R.shape N m n x) (X:Match.Alliance I h 1 0)
local notation "a"=> A.B.a
local notation "z"=> A.B.a.clock.hatBeta m
local notation "Z"=> A.B.a.clock.hatBeta (m+1)
local notation "v"=> A.B.a.clock.J (m+1)
local notation "B"=> A.B.a.budget m
local notation "R!"=> R.shape
local notation "g"=> A.B.kin.alpha N m
set_option quotPrecheck false
local notation "c"=> A.B.a.S.side m n
local notation "fc"=> Time.forecastE A.B.a m
local notation "hX"=> (Beam.marquee I B).reg
set_option quotPrecheck false
local notation "U"=> (fun i:ℕ=>Height.chosen I (Beam.lit I) (pennant I i).2)
-- SIMPLE gate require for the given degree. Comes after clock.
variable (w:Scroll G (A.B.a.S.side (m+1) n)) (p:ℕ)(h₀: X.units= Equiv.refl _) (hV:p ≤ A.B.a.clock.J (m+1)) (h':2 ≤ p)
local notation "Y"=> (Z ^ requested 3 (CalendarStep.loss v))
local notation "S"=>sight h w X ❖ g p
include he hP hK hp hm hV h' h₀
lemma structurePrices  (J:Opera.Guide A.B R! N m n (bend x w)) (hx:Opera.Price A.B R! N m n (bend x w) J) (hb: (bend x w).beta∈band A.B.a (m+1)) (_hh: PartialLives A.B.bake N (m+1) n (bend x w)) :
    (Meadow.Budget B hX (fun i=> if U i then S true (fun j=> ¬3≤j) i else 0) ((1/16+2*(1/16:ℝ))*fc+Y))∧
      Meadow.Budget B hX (S false (mergePoly p)) Y := by
   let V: Match.Alliance I J 1 0 := Match.staple he.symm hP hK
   have hr:= R.pledging; have hT:=Roof.openChairs hr.conducts hr.peak hr.jewels hr.pipes hr.agenda hm _hh hb I J hx V rfl he.symm hP hK; let W:= A.B.a.S.oneStep m n
   obtain ⟨c₀,d,t,e,b₀,b,k',D,j₀,j₁,v',Z',y₀,θ,l,U',hf⟩:= Capstone.engaged R W.exact_size (show Chartlet R.shape A N m W.exact_size (bend x w) from J) hm hp p hV (CalendarStep.loss v) le_rfl
   let gg j:=Candle.sprig J ❖ j (l:=p); -- local notation g collides
   constructor
   · simp_rw [verges h w X J V rfl h₀ ❖ (A.B.kin.alpha N m) p true (fun i=>¬3 ≤ i) (fun _ h=> by omega)]
     let T0 i:= Height.chosen I (Beam.lit I) (pennant I i).2; let t':= A.B.kin.alpha N m
     let H':=Height.serve I V ❖ (Beam.lit I); let W:= cohort J («χ»:=❖) V t' gg true (fun i=>¬3 ≤ i); let T':= cohort J («χ»:=❖) V t' gg false (fun i=>3 ≤ i)
     have he: (fun i=> if T0 i then W.logRead i else 0)= H'.logRead-(fun i=> if T0 i then T'.logRead i else 0):=by
        have h := YM.LocalTaylorR2.subtract J hf.probed V t' (fun i=>3 ≤ i); funext i; rw [Pi.sub_apply,(show H'.logRead i=_ from (bolted I V ❖ (Beam.lit I) t' i).1)]; change (if T0 i then W.logRead i else 0)=(if T0 i then (plusone I V ❖ t').logRead i else 0) - _; split
        · rw [show (plusone I V ❖ t').logRead i=W.logRead i+T'.logRead i from congr_fun h i,add_sub_cancel_right]
        rw [sub_zero]
     rw [he]; exact Reel.gauges_sub (Capstone.budget_of_local hT) (Reel.reenact _ (Capstone.allocation R _ J hf V (show 3≤p+1 by omega) _ (fun _ hi=>hi)))
   rw [verges h w X J V rfl h₀ ❖ (A.B.kin.alpha N m) p false (mergePoly p) (fun i hp=> by unfold mergePoly at hp; omega)]
   exact Capstone.allocation R _ J hf V (show 3≤p+1 by omega) _ fun _ h=> h.1

open Strand
variable (hc:∀ i:Strand, PartialLives A.B.bake N (m+1) n (bend x (x.activities.E + dial i • w))) 
include hc hb
lemma renting (q:Strand)(hv:0 ≤ dial q): Meadow.Budget B hX (sight h (x.activities.E+dial q • w) X ❖ (A.B.kin.alpha N m) p true (fun i=> ¬p+1 ≤ i)-sight h x.activities.E X ❖ (A.B.kin.alpha N m) p true (fun i=> ¬p+1 ≤ i)) (3*(q:ℝ)*((1/16+2*(1/16:ℝ))*fc+Y)+(spelling p)*(q:ℝ)*Y):= by
   let K:=x.activities.E; let ψ i:=K+dial i • w; let k := A.B.kin.alpha N m
   let A' i:= bend x (ψ i)
   choose H H' using fun i=>Opera.partial_feature A.B R.shape hm R.pledging.conducts.full R.pledging.conducts.income (hc i) (show (A' i).beta∈ _ from hb)
   let f i:=sight h (ψ i) X ❖ k p true (fun i=>¬3 ≤ i)
   let W i j:= if U j then f i j else 0
   let g' i:= sight h (ψ i) X ❖ k p false (mergePoly p)
   have hℓ (i:Strand):= structurePrices R hm I he hP hK hp h X (ψ i) p h₀ hV h' (H i) (H' i) hb (hc i) -- type lots
   let t:= CalendarStep.loss v
   let a₀:= A.B.a.S.oneStep m n
   obtain ⟨C,e,z₀,a',k',t₀,q₀,r,s,E,u,D',s',g'',l,N',hD⟩:= Capstone.engaged R a₀.exact_size (show Chartlet R.shape A N m a₀.exact_size x from h) hm hp p hV t le_rfl
   have hz : ψ Strand.bud=x.activities.E:=by simp [ψ,K,Strand.bud,dial]
   suffices heq:sight h (ψ q) X ❖ k p true (fun i=> ¬p+1≤ i)-sight h x.activities.E X ❖ k p true (fun i=> ¬p+1≤ i)=(W q-W Strand.bud)+(g' q-g' Strand.bud) by
     show Meadow.Budget _ _ (sight h (ψ q) X ❖ k p true _ -sight h _ X ❖ k p true _) _; rw [heq]; refine gauges_add (pursues W (fun _=> (hℓ _).1) q ?_ needle (weft q) (tinyB q hv) (fun V _ h=> Strand.rookie q h)) (pursues g' (fun _=> (hℓ _).2) q ?_ _ _ (legacy q hv p) (fun V _ h=> Strand.rates q h))
     · intro i V hV; unfold W; split
       · exact asSeen h dial Strand.bud Strand.lip rfl rfl x.activities.E w H N' X B rfl _ (fun i h=> by omega) h' k true i V hV -- edit
       exact Filled.steady _ Submodule.mem_top
     intro i V hV; exact asSeen h dial Strand.bud Strand.lip rfl rfl _ w H N' X B rfl _ (fun i h=> by change _ ∧ _ at h; omega) le_rfl k false i V hV -- edit
   -- subtract equality without assuming no off-mask companions
   calc
    _ = (f q-f Strand.bud) + (g' q-g' Strand.bud) := by
       unfold f g'; rw [hz, Reel.separated h p ❖ k (ψ q) X h', Reel.separated h p ❖ k x.activities.E X h']; abel
    _ = _ := by
      congr 1; funext i; unfold W; simp only [Pi.sub_apply]; by_cases hU:U i; rw [if_pos hU]; simp only [if_pos hU]; rw [if_neg hU,if_neg hU]; unfold f; rw [emitsEqual h X (ψ q) (ψ Strand.bud) he hP hK h₀ ❖ k p true _ i hU]; simp
end anchor
end YM.LocalTaylorR2.Reel
