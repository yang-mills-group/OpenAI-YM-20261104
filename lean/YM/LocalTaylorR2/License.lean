import YM.LocalTaylorR2.Balance
/-! # Cost contract for ALL unforced leaves (produced in this file)

Receives physical and schedule parameters. On the SAME universal addresses,
strong enough to pass to both trees. This will sit with schedules compiled in
Delivery. Price before model identification. `funds` exposes sums of ALL
norms, not estimates on pointwise pushed expectation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {W s μ C : ℝ} {R : Rep G f} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable {H : Cash W s μ L Q o C T R}
open Channel Gas Ursell Trees Animals Census Itinerary Port Reserves RG01.Survive PhysicalNext.Repeat
open Charge Candle Tender AnalyticBridge VerifiedReset
variable {j k n l : ℕ} {v r d A a x B D C' ζ η θ c' q w w' δ ρ: ℝ} {χ : Chi}
structure ReadyAll (χ:Chi) {l : ℕ} (x:Expansions H l)
    (v : ℝ) (j : ℕ) (u : H.ThinP → Orders l→ℝ) (total : H.ThinP → ℝ) (ρ : ℝ): Prop where
  letter (i p): GaugeInvariant (x i p) ∧ Measurable (x i p) ∧ LocalOn (H.smallAt i) (x i p)
  budget (i p): ∀ V, Healthy (Pressure.temp s) (H.smallAt i) V → Ore V (x i p) v (u i p) j
  scale : 1 ≤ ρ
  pos (i p): 0 ≤ u i p
  bounds i : (∑ p, u i p * ρ^p.val) ≤ total i
  identity i : ∀ V, leaflet H χ V i=∑ p, x i p V

lemma ReadyAll.consumer {u: H.ThinP→ Orders l→ℝ}{z:H.ThinP→ℝ}{Ξ:Expansions H l}
    (h:ReadyAll χ Ξ v j u z ρ) (m:ℕ) (y:ℝ) : LeafReady χ m y Ξ v j u z ρ :=
  ⟨fun i p _=>h.letter i p,fun i p _=>h.budget i p,h.scale,fun i p _=>h.pos i p,fun i _=>h.bounds i,fun i _=>h.identity i⟩

namespace Price
variable (N:Captain H j C' d v w A a r B q (n+j) χ)
variable (hB: LocalBookingsR2 ζ c' N.conduit) (M:StoresR2 H j v d A D k x n χ)
set_option quotPrecheck false
local notation "Ξ" => N.conduit
variable (h:1≤betaF G s L)(hζ:0≤ζ)(hp:1≤ρ) (hθ:1≤θ)
    (hs:ρ*c'≤1) (hr: ρ^(l+1) ≤ betaF G s L^ζ) (hh:betaF G s L^ζ ≤ Real.exp (Q.mark L μ s))
local notation "σ"=> result N θ ζ ρ D x l
include h hζ hp hθ hB M hs hr hh
lemma credentials (he:Charge.Allows l j θ) : ReadyAll (H:=H) (l:=l) χ (sprig H χ) v j (schemePrice N D x θ) (σ) ρ := by
  refine ⟨indexed H χ,muster N hB M h hζ hp hθ he hs,hp,positional N M hθ,fun i=>?_,fun i V=> equality H χ i V l⟩
  by_cases hf:vetted H i; · exact bounded N hB M h hζ hp hθ hs hr hh i hf
  simp only [schemePrice,live,hf,false_and,and_false,ite_false,zero_mul,sum_const_zero]; exact tall N M h hζ hp hθ i

local notation "K"=> ((l+1:ℝ)*θ*ρ)
omit hr hh hs
variable (hd:degreePrice (radiusB s) (massb Q L μ s θ ρ l c') Q.δ ≤ 1/2)
include hd
-- actual hit budget, support exponent can use ANY post-reserve of Quotes.
def secondQ (Q: YM.ConnectedActivityE6.Target G P)(L:Side) (μ s θ ρ D x B r c':ℝ)(l n j:ℕ):ℝ:=
    2^j*(slope D x B r l j*(Reserves.extract Q.ε (n+j) 0 0* treeYield (massb Q L μ s θ ρ l c') (1/2) 0))
lemma funds {u:ℝ} (hu:u ≤ Q.exp): Ac.Hit H.smallAt (radiusB s) (fun i=>2^j*(σ) i) u (secondQ Q L μ s θ ρ D x B r c' l n j):=by
  apply Quotes.hit_scale (by positivity : 0 ≤ (2:ℝ)^j)
  have he:(1:ℝ) ≤ K:=one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (le_add_of_nonneg_left (Nat.cast_nonneg _)) hθ) hp
  have hQ:0≤ slope D x B r l j:= add_nonneg N.balance (by unfold tubeRate; have hv:= M.sure; have hr:=(Ξ).active; have ht:=M.fuel; positivity)
  have hz:= Quotes.hit_scale hQ (sheet N.conduit h hζ he hB hd (n+j)); intro i; have hv:= budget_pull (fun i:H.ThinP=> i.val) Subtype.val_injective (hz i); apply budget_mono hv ?_ ?_
  · intro j; split
    next=> exact mul_nonneg (tall N M h hζ hp hθ _) (Real.exp_pos _).le
    exact le_rfl
  intro j; dsimp only; split
  next hh=>
    rw [if_pos (show i∈H.unionP j.val from hh)]
    exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right hu (Nat.cast_nonneg _))) (tall N M h hζ hp hθ j)
  exact hv.1 j
lemma secondReady {a:ℝ}(he:a+δ+δ≤Q.exp)(hδ:0<δ)(hv: secondQ Q L μ s θ ρ D x B r c' l n j ≤ w') (hw:0<w')
    (ht : degreePrice (radiusB s) w' δ ≤ 1/2) : Ready H.smallAt (radiusB s) (fun i=>2^j*(σ) i) (a+δ) w' δ (1/2):=
  ⟨hw,hδ,ht,(by norm_num),fun i=>mul_nonneg (by positivity) (tall N M h hζ hp hθ i),fun i=>budget_loosen (funds N hB M h hζ hp hθ hd he i) hv⟩
end Price
end YM.LocalTaylorR2
