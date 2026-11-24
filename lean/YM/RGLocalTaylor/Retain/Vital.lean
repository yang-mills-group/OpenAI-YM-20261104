import YM.FullVolume.C.Paint
import YM.RGLocalTaylor.Consumer.MilestoneThree

/-!
# Normalized testing of inherited analytic remainder
Read SAME layout. Keep all other parts of actual Rep (including forced
sector with all predicates) separately paid. `Proxy` impulse has NO assumed
power-Series interior valuation. Instead use actual `Valid` and pay
proportional to the cap relative to real trajectory. `spatial` is the
auxiliary thermal request in FullVolume.C.Paint: not claiming successor
or normalized measure/trajectory for off-theory Proxy. Definitions HERE
do not change accepted Recipe, tours or algorithms. In particular NO inference
of new coupling/drift or new marks/history on a Proxy rep.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

open PhysicalNext PhysicalNext.Repeat Greenbelt Beam Mallow
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling
open RG.Supply Input UVNext.CouplingReset Org Roost Progress.DirectedRecipe Opera Push.PriceCompiler
open Post Read
namespace Retain
variable {G : Gauge}{f c L:Side}
variable {R : Rep G f}{B:BudgetPoint}{K:ℕ}{w a c' b d:ℝ} {e : Post.glyph G f}

/-- E error `e` à la mildew before pricing repaint. Includes proves support,
reg, normalization/value/quadratic constraints and Moves witnesses; doesn't
need a common moving permutation with the physical activities. The marked
and K data do NOT refer to this proxy.
-/
structure Profile (R:Rep G f)(e:Post.glyph G f)(Q B D:ℝ): Prop where
   budget : (imprint R.activities e).Valid R.p (B*Q)  D
   nonneg : 0<Q
   cap : Q≤1
namespace Profile
variable (h:Profile R e a b d)
include h
lemma boosted : (imprint R.activities (a⁻¹ • e)).Valid R.p b d:= by
  let K:= imprint R.activities e; let B:=R.p; let v:=a⁻¹; have he:0<v:= inv_pos.mpr h.nonneg
  have hr:= h.budget.regular
  have hᵣ : ∀ s o,Nonempty ((imprint R.activities (a⁻¹ • e)).Moves s o):=by
    intro s o; obtain ⟨W⟩:=h.budget.moves s o; exact ⟨⟨W.ep,W.kp,W.reg_site,W.reg_support,W.forced_support,W.forced_inventory,W.forced_tests,(fun i U=> congr_arg (fun a:ℝ=> v*a) (W.valuesE i U)), W.valuesK⟩⟩
  obtain ⟨g,hP,hL⟩:=h.budget.boundE
  refine show (imprint K (v • e)).Valid R.p b d from template.inheritance (v • e) h.budget ⟨fun i=> CouplingShape.reg_scale _ (hr.smooth i),?_,?_⟩ ⟨fun i=>v*g i,fun i=>?_,?_⟩ hᵣ
  · intro i; change v*K.E i 1=0; rw [hr.at_flat,mul_zero]
  · intro i hx x y hu hw
    change iteratedFDeriv ℝ 2 (v • VerifiedReset.germ (K.E i)) 0 _=_ -- n namespace?
    rw [iteratedFDeriv_const_smul_apply (VerifiedReset.germ_diff (hr.smooth i))]; change v • logHessian _ x y=_; rw [hr.vanish i hx _ _ hu hw,smul_zero]
  · simpa only [abs_of_nonneg he.le] using! (CouplingShape.sup_scale v (hP i))
  intro i
  change SumBudget (fun j=> if (K.reg j).site=i then B.mass (K.reg j).support (v*g j) else 0) b
  convert! budget_scale he.le (hL i) using 1
  · ext1 j; split_ifs; exact mul_left_comm ..; rw [mul_zero]
  unfold v; field_simp [ne_of_gt h.nonneg]

end Profile

variable {T: Metals G}{D:Rolls T.p}{A: Alloy T D}{U : Factor A}{N m n : ℕ}
    {X : RG.Rep G (A.B.a.S.side (m+1) n)}
local notation "R"=> A.B.a
local notation "p"=> A.B.a.clock
local notation "f₀" => Post.glyph G (A.B.a.S.side (m+1) n)
variable (e' : Post.glyph G (A.B.a.S.side (m+1) n))(hw: RG.Shoot.Lives A.B.bake N (m+1) n X)
    (h:Profile X e' a (A.B.a.clock.allowance (m+1)) (A.B.a.clock.forcedAllowance (m+1)))

-- call Persona with normalized remainder. same E positions and horizons; preserve true path outside test.
def impulse (X:Rep G f) (f' :Post.glyph G f)(a:ℝ) : Rep G f := {X with activities:=imprint X.activities (a⁻¹ • f') }
local notation "t"=>impulse X e' a

include hw h
lemma rooted : RG.Shoot.Lives (Roof.spatial A).bake N (m+1) n (impulse X e' a):= by
  refine ⟨hw.path,hw.point,hw.clip,⟨hw.valid.paths,h.boosted⟩,trivial⟩
variable (K : Guide A.B U.shape N m n X) (hm:m<N) (hb:X.beta∈ Shoot.band A.B.a (m+1))
include hb hm
lemma aspirates : ∃ V:Guide A.B U.shape N m n t, Price A.B U.shape N m n t V ∧
    let S : Match.Alliance K V 1 0:= Match.staple rfl rfl rfl
    Collection.Local (Beam.marquee K ((R).budget m)) ((R).budget m) (Height.serve K S Chi.canonical (Beam.lit K)) ((3/16:ℝ)*Time.forecastE A.B.a m) ((1/8:ℝ)*Time.forecastK A.B.a m U.scout (t).beta):= by
  obtain ⟨V,hF⟩:= Roof.prepares U.pledging.conducts hm (rooted e' hw h) hb; refine ⟨V,hF,?_⟩; intro S
  rw [show (3/16:ℝ)=1/16+2*(1/16) by ring]
  exact Roof.seats U.pledging.conducts U.pledging.peak U.pledging.jewels U.pledging.pipes U.pledging.agenda hm (rooted e' hw h) hb K V hF S rfl rfl rfl rfl
end Retain
end YM.RGLocalTaylor
