import YangMills.WilsonProof.NativeSupport.Commissioned259.Quotes.Out
import YangMills.WilsonProof.NativeSupport.Commissioned259.Pose.Final
import YM.Integration.WilsonPositionHomogeneousCoefficients
/-! # Hypotheses of QScale involving *this* H's construction;
the `Borel` inputs about its formal asymptotic expansion are computed on the
original H supplier (separate Run application). No physics hypothesis in that.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Quotes
open Function Filter Set Asymptotics PowerSeries MeasureTheory
open Extraction Table Spec OPE OPE.Orbits Climb PhysMS
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open Maxwell Maxwell.Free Trace.Pilot XSpace XSpace.Normalize XSpace.Structure1 Dframe
open FVA2.Scale Scale.Jury ScaleCost O.Score Comparing Pose Original
open YM.Integration YM.Integration.WilsonPositionHomogeneousCoefficients
open scoped Topology ContDiff Classical BigOperators
variable {I : Type*}{L:Filter I} {G : Gauge} {d n q m e : ℕ} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (U : Final C f S) (J Y : ℝ→PhysMS.tower S) (N : WilsonPrescription G)
    (A : ∀ d:ℕ, ℝ→Change G d) (t : ℝ→ℝ)
    {sim : G.Simple} (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ : MS.Land.Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match N sim M σ dial)
local notation "late" => 𝓝[>] (0:ℝ)
local notation "δ" => g0 G
local notation "FF" => Paper.point U J
local notation "τ" => Paper.meter U J N.criterion
local notation "Q" => Scale.Measure.adjust N.scheme N.criterion

/-- Inputs stating how the **reached** W and H measurements are related: true
H frame on the genuine measured coupling and order-independent. Not yet giving a step
estimate. In the original `A` is taken from its `Near.field`. -/
structure Realized (J Y:ℝ→PhysMS.tower S) (N: WilsonPrescription G)
    (A:∀ d:ℕ, ℝ→ Change G d) (t:ℝ→ℝ) : Prop where
    relates (d:ℕ) : ∀ᶠ r in late, ∀ v,
      frame Y r d v= frame J r d (stand (A d (t r)) v)
    enough (d:ℕ) : Tendsto (fun i=>guide G d (A d i)) (𝓝 0) (𝓝 0)
    stays {d e:ℕ}(h:d≤e)(i v) : stand (A e i) (up h v)=up h (stand (A d i) v)
    charge (d p:ℕ) : (fun i=> guide G d (A d i) - ∑ n∈Finset.range (p+1), i^n • guide G d (letter N d n))=O[late] fun i=> i^(p+1)

-- housekeeping for this upgrade
variable {N} {A} (P : Realized J Y N A t) (ht : Calibrated G t)
lemma continuous_component (i:Toon G d) (p : Sec G d) : Continuous (fun B: MoveSpace G d=> coord i ( ((guide G d).symm B).val p )) := by
  let L : MoveSpace G d→ₗ[ℝ] ℂ := { toFun B:= coord i (((guide G d).symm B).val p), map_add' := fun a b=> by rw [map_add]; exact map_add (coord i) _ _, map_smul':= by intro a b; rw [map_smul]; exact map_smul ((coord i).restrictScalars ℝ) _ _ }
  exact L.continuous_of_finiteDimensional
lemma linear_component (i:Toon G d) (v:Sec G d) (X:I→Change G d) {g:I→ℝ} (h:(fun i=>guide G d (X i))=O[L] g) :
    (fun k=> coord i ((X k).val v))=O[L] g := (insertCoord _ h i v).congr_left (fun k=> by rw [stood,map_add]; abel)
lemma via_component (x:I→Change G d)(h:Tendsto (fun i=>guide G d (x i)) L (𝓝 0)) :
    Tendsto (fun i=>columns (stand (x i))) L (𝓝 1) := by
  refine tendsto_pi_nhds.mpr fun j=>tendsto_pi_nhds.mpr fun k=>?_
  simp_rw [columns,stood,map_add, show (coord j) (theory k)=_ from (show _=(1:Matrix (Toon G d) (Toon G d) ℂ) j k from ( by rw [pivotδ,Matrix.one_apply]; simp [eq_comm] ))]
  have hp := (continuous_component j (theory k)).continuousAt (x:=0) |>.tendsto.comp h
  simp only [Function.comp_def, LinearEquiv.symm_apply_apply,map_zero,Submodule.coe_zero,LinearMap.zero_apply] at hp
  simpa only [add_zero] using! (tendsto_const_nhds (x:=(1:Matrix (Toon G d) (Toon G d) ℂ) j k)).add hp

lemma accepts_first (V:Normalize.Guard G d)(p:ℕ)(v:ℝ) : accepts V (p+1) v=accepts V p v+(v:ℂ)^(p+1) • coeff (p+1) V := by
  unfold accepts; rw [Finset.sum_range_succ]
include H
lemma actual_points (p:ℕ) (x:ℝ) : stand (∑ k∈Finset.range (p+1), x^k • letter N d k) = accepts (Q d) p x := by
  let h:= (WilsonPositionHomogeneousCoefficients.purchased N H)
  induction p with
  | zero => simp [accepts, (h.scheme d).scale.zero,WilsonPositionHomogeneousCoefficients.letter]
  | succ p ih=>
    rw [accepts_first, ←ih, Finset.sum_range_succ]; unfold stand
    rw [Submodule.coe_add,Submodule.coe_smul_of_tower,← add_assoc,WilsonPositionHomogeneousCoefficients.positive N h d (by omega : p+1≠0),← Complex.ofReal_pow]; rfl
include P ht
variable {r:I→ℝ} (hr:Tendsto r L late)
include hr
lemma peson : (t∘r)=O[L] (g0 G ∘ r) := (candidate_fee N t M H ht).comp_tendsto hr
lemma heading : Tendsto (t∘r) L late := tendsto_nhdsWithin_iff.mpr ⟨(peson J Y t M H P ht hr).trans_tendsto ((g0_zero sim).comp hr), hr.eventually ((coupling_payment sim ht).mono fun i hi=> hi.1)⟩
lemma paper (p:ℕ) : Notes L home (t∘r) (g0 G ∘ r) p home (fun i=> stand (A d ((t∘r) i))) (fun _=> Q d) := by
  intro j k
  let Y' (i:I):= (∑ n∈Finset.range (p+1), ((t∘r) i)^n • letter N d n)
  have hh : (fun i=> guide G d (A d ((t∘r) i) - Y' i))=O[L] fun i=>δ (r i)^(p+1) := by
    simp_rw [map_sub,Y',map_sum,map_smul]; exact ((P.charge d p).comp_tendsto (heading J Y t M H P ht hr)).trans ((peson J Y t M H P ht hr).pow _)
  refine ⟨fun i=> Fare.constant _, (Fare.bare (linear_component j (theory k) _ hh)).congr ?_ |>.extend ?_⟩
  · refine Eventually.of_forall fun i=>?_ ; rw [← sum_coords, ← accepts, ← actual_points M H]; simp_rw [columns,stood,map_add]
    rw [show (A d _-Y' i).val (theory k)=((A d ((t∘r) i)).val-(Y' i).val) (theory k) from rfl,LinearMap.sub_apply,map_sub]; unfold Y'; abel
  exact Eventually.of_forall fun _=>(mul_one _).symm
lemma young : Tendsto (fun i=>columns (stand (A d ((t∘r) i)))) L (𝓝 1) := via_component _ ((P.enough d).comp ((tendsto_nhdsWithin_iff.mp (heading J Y t M H P ht hr)).1))
end YM.FVA2.GradedFar259.Quotes
