import YM.Gaps1020.Local.MarkedAssign
import YM.Gaps1020.Local.Moment
import YM.MergeProof.TeamFlow
/-!
# Exponent Taylor orders under the shared conditional integral

Reassembly of the exp-power moments holds as an identity of germs on
`Healthy`. Off masked domain our choice will define the residual by exact
subtraction, so need no integrability claims about the extensions there.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Thermal1020.Shared
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open March Next.Foundations YM.GapsLocal.ExpShares
open PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {j n k M : ℕ} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {R : Rep G f}
variable {X : Coat T F} {I : Finset (Bond f)} {η r q Y W A B A' a β b p v d t γ C s C' μ g ρ ℓ : ℝ} {l:ℕ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi} {Ñ : ChartRatio G}
variable {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable {z : Air f G} {V:E→ Config G c}{x:E}

variable {H : Cash W s μ L Q o C T R}

open PhysicalNext.Repeat.Lotus
-- formulas on actual inputs. Non-contributing signs excluded by statute below.
def teamMoment (X:Coat T F) (p:Molecule S) (R:Rep G f)(U:Team R)(π:Assign (others U p) M)(a:ℝ)(Ñ:ChartRatio G) (x:F.Slice G × Air f G):=
  let Z:= X.wrapY x.1; U.paidU Z a (worldZ Z R.beta x.2)* ∏ i:↥(others U p),momentV (π i).val (pole (X.wrapY x.1) R a Ñ x.2 i.val)

def teamMomentBars (X:Coat T F) (p:Molecule S)(R:Rep G f)(U:Team R)(π:Assign (others U p) M)(a:ℝ)(Ñ:ChartRatio G):=
   ∫ y,teamMoment X p R U π a Ñ y ∂(F.order G).prod X.dice

-- as in Aurora
private lemma scalp_one {x C :ℝ} (I : Finset (Bond f)) (h:Canary G A C) (z:Air f G) (hv:0<x) : scalp I X X.V x A z=1 := by
  have hh i : steerJ X A (worldZ X x z) X.V i=1 := by unfold steerJ Silica.action; rw [mul_inv_cancel,G.mat_one]; exact Eider.leaves h ..
  unfold Flux.scalp Flux.jacL; dsimp only; rw [prod_eq_one (fun i _=> hh i), Silica.home X h z hv,one_mul]; apply div_self (fullFuel _ _|>.ne')

variable (p:Molecule S){Ξ:Utopia H j v d r C' χ} (h:HasClutch Ξ A) (hΘ:Oboe H j v B k A b Ξ)
variable (hlog : HeadsAreLog p)(ht:troupe T R Q.halo (radiusB s) p)
    (hX:X.x=s) (hk:X.width=o.K) (he:X.χ=χ) (hP:Healthy (Pressure.temp s) (H.unionP p) X.V)
    (hm:H.shapeW p ≤ ℓ) (hρ: charge Q L s r j ℓ ≤ ρ⁻¹) (hp:2 ≤ ρ) (hV: 0 ≤ v) (U:Team R)(π:Assign (others U p) M)(hχ: U.signs S ⊆ p)
include hχ h hΘ hX hk he hP hm hρ hp hV hlog ht
lemma teamCenterPower (hT:degree (others U p) π ≤ M)(hM:X.manifest) :
    teamWeightRhythm (edgesM S (H.unionP p) (radiusB s)) X X.V A Q.table p R U (assignment (others U p) π) W o.a Q.halo=teamMoment X p R U π o.a Q.table:= by
  funext y
  let Z:=X.wrapY y.1; let q:=y.2; let V:=X.V; let I:=edgesM S (H.unionP p) (radiusB s)
  have hβ:= H.laws.intake.positive
  unfold teamWeightRhythm teamWeightRecoil
  change scalp I Z Z.V R.beta A q*teamWeight p R U _ _ W _ _ (vary Z Z.V) (course Z A R.beta q Z.V) = _
  rw [scalp_one (X:=Z) I hΘ.conduit q hβ,home Z hΘ.conduit q hβ, show vary Z Z.V= Z from rfl,one_mul]
  rw [teamWeight,seats,if_pos hχ]; unfold Polar.floating; rw [mul_assoc]; apply congr_arg (U.paidU Z _ _*·); rw [← prod_attach]; change (∏ i:↥(others U p),row p R Q.table W o.a Q.halo Z y.2 i) * (∏ i:↥(others U p),YM.GapsLocal.ExpShares.share M (π i) (row p R Q.table W o.a Q.halo Z y.2 i))= _
  rw [← Finset.prod_mul_distrib]; apply prod_congr rfl; intro i hpX
  have hv': (π i).val < M+1:= Nat.lt_succ_of_le ((single_le_sum (f:=fun i=> (π i).val) (fun i _=> Nat.zero_le _) hpX).trans hT)
  obtain ⟨i,hi⟩:= i; obtain ⟨t,rfl⟩:=hlog i (sdiff_subset hi); let i:↥(others U p):=⟨_,hi⟩
  change _* YM.GapsLocal.ExpShares.share M (π i).val _= momentV (π i).val _
  rw [YM.GapsLocal.ExpShares.share,if_neg hv'.ne]; unfold momentV
  cases hz:(π i).val with
  | zero=>rw [if_pos rfl]; exact mul_zero _
  | succ m=> rw [if_neg (by omega)]; exact (vertex_value (Ξ:=Ξ) (X:=Z) h hΘ p hlog ht hm hρ hX hk he hM hP hV hp t (sdiff_subset hi) q m).2.2
lemma teamBarsPower (hT:degree (others U p) π ≤ M)(hM:X.manifest): Integrable (teamMoment X p R U π o.a Q.table) ((F.order G).prod X.dice) ∧
    teamWeightBars p (podium S G (H.unionP p) (radiusB s)) X R U (assignment (others U p) π) Q.table W o.a Q.halo = teamMomentBars X p R U π o.a Q.table := by
  let f (_:ℝ):=X.V
  have hv : Mode f 0 j v := ⟨hV,fun i=>a_oneB G _ hV⟩
  have hh:= hΘ.flow F X hX he hk hM ℝ f 0 rfl hv
  have hb:= (teamUnfoldBars (X:=X) H hX hM hk hh hΘ.conduit hΘ.mode p U (assignment (others U p) π) (fun i=> share_contDiff ..)).self_of_nhds
  let I:=edgesM S (H.unionP p) (radiusB s); let V:=teamMoment X p R U π o.a Q.table
  have hP':= ((teamMultiplied (X:=X) H hX hM hk hh hΘ.conduit hΘ.mode p U (assignment (others U p) π) (fun i=> share_contDiff ..) I).2).self_of_nhds
  unfold teamMomentBars; rw [← teamCenterPower p h hΘ hlog ht hX hk he hP hm hρ hp hV U π hχ hT hM]; exact ⟨hP',hb⟩

-- no assertion about unconstrained regrouping of the teamWeight leaves
lemma teamPowerSlice (hD:Ac.Spark H.supportP p) (hF:(roster p).flags=∅) (hT:degree (others U p) π ≤ M) :
    let Z i := (planted X p).taggedL i
    teamWeightFringe X p R U (assignment (others U p) π) Q.table W o.a Q.halo=Pond.likely (fun i => teamMomentBars (Z i) p R U π o.a Q.table) ∧
      ∀ i:S.Choices, Integrable (teamMoment (Z i) p R U π o.a Q.table) ((F.order G).prod (Z i).dice) := by
  let f (_:ℝ):=X.V
  have hv : Mode f 0 j v := ⟨hV,fun i=>a_oneB G _ hV⟩
  intro Z
  have hh i := teamBarsPower (X:=Z i) p h hΘ hlog ht hX hk he hP hm hρ hp hV U π hχ hT (planted_valid X p)
  rw [show teamWeightFringe X p _ _ _ _ _ _ _= _ from (teamWeightRainbow p U (assignment (others U p) π) hΘ hX hk he hF hP hv rfl).self_of_nhds] -- defeq?
  refine ⟨?_,fun i=> (hh i).1⟩
  change teamWeightShelter X p R U (assignment _ π) Q.table W o.a _ = _
  unfold teamWeightShelter; rw [show X.B=radiusB s from congr_arg _ hX,if_pos ⟨hD,ht⟩]
  apply congr_arg likely; funext i; exact (teamWeightSpices p U _ H X hX X.V X.V (fun _ _ _=>rfl) hP hF i).symm.trans (hh i).2

-- Exact masked Team uptake at Healthy. Separate to retain no analytic
-- denominator assumptions about the chosen marks. Works also on exceptional
-- leaves (existing Team.tithe), proved via Healthy Polar rewrites and
-- same scalp=1 based flow. Uses F.order & X.dice exactly in Team.tithe.
variable {U : Team R}
omit h hχ hlog ht hm hρ hp in
lemma teamSame (hD:Ac.Spark H.supportP p) (hT:troupe T R Q.halo (radiusB s) p) (hF:(roster p).flags=∅) (U:Team R) :
    U.bloom X W o.a Q.table Q.halo p= teamWeightFringe X p R U (emptyTeamData _ _) Q.table W o.a Q.halo := by
  let f (_:ℝ):=X.V
  have hv : Mode f 0 j v := ⟨hV,fun i=>a_oneB G _ hV⟩
  have hz:X.B=radiusB s:=congr_arg radiusB hX
  let Z (i:S.Choices):= (planted X p).taggedL i
  have hS: standsIn X R Q.halo p:=by unfold standsIn claimed; rw [hz,hX]; exact ⟨hD,hT,hF.symm ▸ Finset.disjoint_iff_inter_eq_empty.mp (show Disjoint _ _ from hP.symm)⟩
  rw [show teamWeightFringe X p R U (emptyTeamData _ _) _ _ _ _= _ from (teamWeightRainbow p U (emptyTeamData U p) hΘ hX hk he hF hP hv rfl).self_of_nhds];
  change U.bloom X W o.a Q.table Q.halo p= teamWeightShelter X p R U (emptyTeamData _ _) Q.table W o.a Q.halo
  unfold Team.bloom teamWeightShelter; rw [if_pos hS, hz,if_pos ⟨hD,hT⟩]
  apply congr_arg likely; funext i
  have hm : (Z i).manifest:=planted_valid X p; have hh := hΘ.flow F (Z i) hX he hk hm ℝ f 0 rfl hv
  have hv : teamWeightBars p (podium S G (H.unionP p) (radiusB s)) (Z i) R U (emptyTeamData U p) Q.table W o.a Q.halo= _ := (teamUnfoldBars (X:=Z i) H hX hm hk hh hΘ.conduit hΘ.mode p U (emptyTeamData _ _) (fun i=>contDiff_const)).self_of_nhds
  change U.tithe _ _ _ _ _ _ _= _; refine Eq.trans (b:=teamWeightBars p _ (Z i) R U (emptyTeamData _ _) Q.table W o.a Q.halo) ?_ (teamWeightSpices p U _ H X hX X.V X.V (fun _ _ _=>rfl) hP hF i); rw [hv]; unfold Team.tithe
  apply integral_congr_ae; filter_upwards with y
  unfold teamWeightRhythm teamWeightRecoil; let Y:= (Z i).wrapY y.1; have hβ:= H.laws.intake.positive
  rw [show f 0=Y.V from rfl,scalp_one (X:=Y) _ hΘ.conduit y.2 hβ, home Y hΘ.conduit y.2 hβ, one_mul]
  change U.premium Y W _ _ _ _ y.2 p=teamWeight p R U _ _ _ _ _ Y y.2
  rw [lit]; unfold Team.premium seats; split
  next h =>
    have hR:Room P S T X.x:= hX.symm ▸ H.laws.data.room
    rw [show worldZ Y R.beta y.2=Y.liftA R.beta y.2 from (shine Y hR hm _ _).symm]
    refine congr_arg (_*·) (Polar.afterborn Y o.a R W Q.table y.2 (own p) hR hm Q.buys _ (Finset.disjoint_of_subset_left (Finset.biUnion_subset.mpr (fun i hi=>?_)) (show Healthy (Pressure.temp X.x) (ground R T Q.halo X.B p) X.V from ?_)))
    · exact subset_biUnion_of_mem (Matter.areas R T Q.halo X.B) (sdiff_subset hi)
    rw [hz,hX]; exact hP
  next=>rfl

end YM.ConnectedActivityE6.Blaze.Thermal1020.Shared
