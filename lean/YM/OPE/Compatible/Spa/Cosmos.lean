import YM.OPE.Compatible.Spa.Ju
import YM.OPE.Compatible.Spa.Vow
/-!
# Linear sections of the filtered readings

Under the `Bals` and `Floss` hypotheses, `ArtR` constructs a polynomially
controlled linear right inverse for `ReadK` at each degree. The section
intertwines `τΓ` with `Gift`. `TarJ` gives the corresponding `Wealth` bound
for reading an indexed family of flag elements.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
open Quit.PriceZ Quit.Jac Quit Hark Topic StageLight
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P P':Patch}{R:ChartRatio G}{p p':Clip}
variable {v v' b u:ℝ}
variable {H:LocalRatio R}{hs:G.Simple}
open Balsam Nestle Pert.Full
variable {X:Sailing T P p R b}{B:Medal P G K.K P.J} {w:ℝ} {D₀:Stern K P τ l d w}(Hp: Alps.Crest G P K.K m)(Z:Topic H hs X B D₀)(a:Axis)
variable {Y:M→ℝ}{V:(i':M)→ Alps K T i (Y i')}{A':(i:ℕ)→ Submodule ℝ (Bead G l i)}{hq:1 ≤ Y}{hp:4 ≤ i}{U:Z.Ω M Y}
local notation "J!"=> Fin (l+1)
local notation "F!"=> Tracts G d τ
section
variable {L D : Type} [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L]
variable [NormedAddCommGroup D] [NormedSpace ℝ D]

private def sections (t : M → ℝ) (F : M → Submodule ℝ D)
    (read : ∀ i, F i →ₗ[ℝ] Jewel L) (turn : D →L[ℝ] D) : Prop :=
  ∃ g : (i : M) → Jewel L →ₗ[ℝ] F i,
    Wealth (fun i => ((F i).subtype.comp (g i)).toContinuousLinearMap) t 1 ∧
    (∀ i x, read i (g i x) = x) ∧ ∀ i x, turn (g i x).val = (g i (τΓ L x)).val

private lemma build_sections (t : M → ℝ) (F : M → Submodule ℝ D)
    (read : ∀ i, F i →ₗ[ℝ] Jewel L) (turn : D →L[ℝ] D) (hn : ∀ x, turn (turn (turn x)) = 0)
    (ht : 1 ≤ t) (lifts : ∀ x : Jewel L, ∃ g : (i : M) → F i,
      Wealth (fun i => (g i).val) t 1 ∧ ∀ i, read i (g i) = x)
    (transfer : ∀ i, ∃ f : F i →ₗ[ℝ] F i,
      (∀ x, (f x).val = turn x.val) ∧ ∀ x, read i (f x) = τΓ L (read i x)) :
    sections t F read turn := RexE F read turn hn ht lifts transfer
end

private lemma flag_sections {κ : (e : J!) → Mint Z e.val →ₗ[ℝ] Jewel (A' e.val)}
    (C : Bals Hp Z a A' κ) (T' : Z.Floss V U hp (le_trans zero_le_one hq) k Hp a) (e : J!) :
    sections Y (U.flag e.val) (ReadK Z κ U e) (Gift G D₀.aware) := by
  refine build_sections (L := ↥(A' e.val)) (D := Tracts G d τ) Y (U.flag e.val) (ReadK Z κ U e)
    (Gift G D₀.aware) (turn_nil (D₀ := D₀)) hq ?_ ?_
  · exact Gadget Hp Z a C U e
  · exact orbRuns (hq := hq) Hp Z a C T' e

set_option maxHeartbeats 200000 in
lemma ArtR {κ:(e:J!)→ Mint Z e.val →ₗ[ℝ] Jewel (A' e.val)}(C:Bals Hp Z a A' κ)(T':Z.Floss V U hp (le_trans zero_le_one hq) k Hp a)(e:J!):∃ g:(i:M)→ Jewel (A' e.val) →ₗ[ℝ] U.flag e.val i, Wealth (fun i=> ((U.flag e.val i|>.subtype).comp (g i)).toContinuousLinearMap) Y 1 ∧ (∀ i x, ReadK Z κ U e i (g i x)=x) ∧∀ i x, Gift G D₀.aware (g i x|>.val)=(g i (τΓ (A' e.val:Type) x)).val :=by
  exact flag_sections (hq := hq) Hp Z a C T' e

set_option maxHeartbeats 200000 in
lemma TarJ {κ:(e:J!)→Mint Z e.val →ₗ[ℝ] Jewel (A' e.val)} (U:Z.Ω M Y)(e:J!)(W:I→ M)(x:I→ℝ)(f:(i:I)→U.flag e.val (W i))(h:Wealth (fun i=>(f i).val) (Y∘W) x) : Wealth (fun i=>ReadK Z κ U e (W i) (f i)) (Y∘W) x:=by
  let v (i : I) : Mint Z e.val := U.read e.val e.isLt (W i) (f i)
  apply PayF (BoxesΦ Z e.val e.isLt).symm (κ e) (v := v)
  exact (U.branch W).bulk e.isLt f h
end YM.OPE.Stroke
