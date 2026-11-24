import YM.FVAAlt2.Booth.Cascade
/-! # Periodic RNA cooperation. Programs per torus.S.N. Kernels all ages. Exact budget.P.L.M.Process index. heat constants dropped *after* step, not before unless Price W prepared so. This is not asking convergence. Body contract inspect. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Booth.Arm
open Function Finset MeasureTheory Filter Set Budget Budget.Layer Budget.Packet Budget.Tuple Budget.Deck Motion Matrix Prim PertExtension Series Series.Radial Series.Tested Chart Lattice Tree Gauge Binding Diagram Diagram.Formal RG Wilson Oracle Geometry Quadratic
open PowerSeries Exterior Precision Bid Comparison.RG02 Comparison.RG02.Bulk Comparison.RG02.Adjacent Comparison.RG02.FVAAlt2 Integral
open FreeResolvent (tensor flatten)
open scoped ENNReal NNReal Topology BigOperators Classical PowerSeries ContDiff Matrix Matrix.Norms.Frobenius
variable {c f n:Side}{G:Gauge}{p: RG.Clip}{O:ChartRatio G}{U:PathData G}
variable (S:StepData c f)(F:Forest S.ratio) (L: Binding.Scale) (H:S.patch.Branches S.kernel G)
local notation "X"=>fieldDir G c 1
local notation "Y"=>fieldDir G f 1
local notation "T₁"=> Comparison.RG02.Bulk.Joint S F (G:=G)
local notation "Q"=>Pins f c G
local notation "E"=> Precision.Key F G
local notation "J"=> directive S
local notation "Y'" => Pin f G
local notation "X'"=> Pin c G
variable (K: Comparison.RG02.Bulk.Kernel S p U O)(C:UnitCost) (w:Geometry.Field.Square F)
open Marker Multi Comparison.RG02.Order Comparison.RG02.Moving Comparison.RG02.Moving.Path
open Comparison.RG02.FVAAlt2.Lyric
variable (Z: Branchix→Orders (KFoot G))
variable (V W:Orders (Pin f G))
variable {I:Type}[DecidableEq I]{R:Marker.Census I}
variable (T:Colors R G f)
-- direct.M.Clock
abbrev pub (i:I) : Multi.Hot R:= ⟨ R.fire i,Finset.singleton_nonempty i⟩
def shineM (C:UnitCost)(T:Colors R G f)(i:I)(y: fieldDir G f 1)(t:ℝ):ℂ:= ( (C.rating t) ^ T.power (pub i) )⁻¹ • T.mark (pub i) (C.enter t) (sample t y)
structure Simmer (p:RG.Clip)(U:PathData G)(C:UnitCost)(T:Colors R G f)(V:Orders (Pin f G))(r:ℕ):Prop where
    certified: Well T
    wakes: Vacuum V
    symmetricV : gradedSymmetric V
    cost (e:ℕ)(hx:0<e)(hh:e≤r)(x:fieldDir G f 1): -coeff (e+2) (Prim.tale (Gala.feeAct p U C T x))= coeff e (flavor 2 (flatten x) V)
structure Single (C:UnitCost)(T:Colors R G f)(W:Orders (Pin f G))(i:I)(r m:ℕ):Prop where
    symmetricW : gradedSymmetric W
    grade e: Within (e+m) (W e)
    earned (e:ℕ)(he:e≤r)(x:fieldDir G f 1): motion (shineM C T i x) (T.power (pub i)+e)=(↑(coeff e ( flavor m (flatten x) W )):ℂ)

variable {m:ℕ} [Fintype I]
abbrev layerSet (_:StepData c f) (T:Branchix→Orders (KFoot G))(V:Orders (Pin f G)):= supply V ( Function.Embedding.inl ) (studied T f c)
abbrev columns (_:StepData c f) (V:Orders (Pin f G)):Orders (Pins f c G):=Cluster.present Function.Embedding.inl V

def scriptV := collectO (offshoot (G:=G)) (driftM S F K) (ceaseHeat (Arm.spins S F K) (layerSet S Z V) true)
-- published torus output. When using store.Vacuum.β rank order, ignores its field-independent normalization prior to choosing W(t). (only harmless constant; true conditional denominator use the one-step native algorithm through every order first).
def OutputV := Binding.pulp (scriptV S F K Z V)
def OutputM (m:ℕ): Orders (Pin c G):= collectO offshoot (driftM S F K) (endHeat m (Arm.spins S F K) (logHeat (Arm.spins S F K) (layerSet S Z V) true) (columns S W))
local notation "μ"=> K.covariance F (directive S)
local notation "P'"=>scriptV S F K Z V
local notation "P"=> OutputV S F K Z V
local notation "M"=> OutputM S F K Z V W m

variable (r:ℕ)(hC: Ribbon.Align r L C) (hs: Prim.Sphere S F L Z)(hV:Simmer p U C T V r)
variable (x:fieldDir G c 1) (B:Bed)(hb: YM.FVAAlt2.Period.Rent.Right p U f B)
local notation "Ω"=>translated K F x
local notation "τ"=> Aperture.core K F (directive S) C T
local notation "u"=> layerSet S Z V
local notation "φ"=> kickA S F (G:=G)
local notation "ρ" => environment S F K x
local notation "δ"=> ceaseHeat (Arm.spins S F K) (layerSet S Z V) true
include hV hs
lemma trusted: Vacuum (layerSet S Z V):= order_supply hV.wakes (paying hs)
include w hC hb
lemma tarr : Lyric.CensusT.RiteV (stage K F x) (hinge F) τ u (kickA S F (G:=G)) (environment S F K x) r:= by
    refine ⟨trusted S F L C Z V T r hs hV,sort_supply hV.symmetricV (knowledge hs),fun v e he=> ?_⟩ -- argument order K?
    have hx: (Ω v).1=1:= by rw [Bulk.footing] -- or footing
    change Assembly.vacuumLetter _ (Ω v) e=_; rcases Nat.eq_zero_or_pos e with h|h
    · subst e; unfold Assembly.vacuumLetter; rw [ if_pos rfl ]; exact Eq.symm (flavor_dark _ (vacuum_lo _ (trusted S F L C Z V T r hs hV)) _)
    rw [ arrive ]; unfold layerSet supply; rw [flavor_add,map_add, flavor_offer]
    rw [Gala.comm S F L T K C w (Ω v) hV.certified hC hs B hb e h he hx, hV.cost e h he];rfl

variable (i:I)(hW: Single C T W i r m)
include hW
local notation "σ"=> Aperture.scoreMark F C T
local notation "modeZ"=> R.fire i
omit w hC hb hs
lemma tarrM : Lyric.CensusT.MarkV (stage K F x) (hinge F) T.power σ (columns S W) (kickA S F) (environment S F K x) (R.fire i) m r:= by
    refine ⟨ Cluster.sym_offer _ _ hW.symmetricW, Cluster.ranks_offer _ _ hW.grade,fun z e he=>?_⟩
    have h : (Ω z).1=1:= by rw [Bulk.footing];
    let y:=(Aperture.uniting F (Ω z)).2
    rw [Lyric.CensusT.welcomed, arrive]; unfold columns; rw [flavor_offer]; unfold Assembly.markLetter;
    change Assembly.jet _ (T.power (pub i)+e) (Ω z)= (↑(coeff _ (flavor _ (flatten y) W)):ℂ); rw [← hW.earned e he y]
    let D:= (ContinuousLinearMap.id ℝ ℝ).smulRight (Ω z)
    have ht : Aperture.scoreMark F C T (pub i) ∘ D =shineM C T i y:= by unfold shineM; funext t'; change Aperture.scoreMark F C T (pub i) (t' • (Ω z)) = _; unfold Aperture.scoreMark; rw [show (t' • Ω z).1=t' from (by rw [Bulk.footing]; exact mul_one _)]; unfold Aperture.opens; rw [_root_.map_smul];rfl
    rw [motion, ←ht, Assembly.jet_continuous_right D ((Aperture.born_mark F C T hV.certified _).smooth.of_le le_top),show D 1=Ω z from one_smul ℝ _]
-- result RAN.Heat
local notation "A"=> Aperture.bank K F (directive S) C T x r
include w hC hb hs
lemma known (e:ℕ)(he:e≤r) : Comparison.RG02.Laplace.detail (Comparison.RG02.Order.logMarked A) modeZ e=(↑(coeff e ( flavor m (flatten x) (OutputM S F K Z V W m) )):ℂ):=by
    rw [← logo (Aperture.symmetric ..) (Aperture.units ..) i he]; let Xᵥ:= tarr S F L K C w Z V T r hC hs hV x B hb; -- fix X
    let Z':= logHeat (Arm.spins S F K) (layerSet S Z V) true
    rw [OutputM, ← flavor_collect, enters, intensity]; exact Lyric.CensusT.aboard (stage K F x) _ T.power σ τ (μ) (layerSet S Z V) (columns S W) φ (environment S F K x) (R.fire i) m (K.positive F J) r Xᵥ (tarrM S F K C V W T r hV x i hW) e he
omit hW
lemma accounted (e:ℕ)(he:e≤r) : Comparison.RG02.Laplace.detail (Comparison.RG02.Order.logVac A) R.quiet e= (↑(coeff e (flavor 2 (flatten x) (OutputV S F K Z V))) : ℂ)+↑(coeff e (Binding.out (P'))):=by
    have ht:=tarr S F L K C w Z V T r hC hs hV x B hb; have hv:flavor 2 (environment S F K x) (δ)= flavor 2 (flatten x) P':=by rw [← enters S F K x, flavor_collect]; rfl
    rw [intensity S F K] at hv; dsimp only at hv
    unfold Laplace.detail; rw [show logVac A= _ from (Lyric.CensusT.den (stage K F x) (Bulk.hinge F) T.power σ τ μ u φ (environment S F K x) (K.positive F J) r ht),  observation _ _ _ he, Assembly.realCoeff,Assembly.beads,if_pos rfl, hv, Binding.flavor_pulp P',map_add,Complex.ofReal_add]; rfl -- rewrite afterward
end YM.RegulatorIR.FVAAlt2.Booth.Arm
