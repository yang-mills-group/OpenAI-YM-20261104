import YM.RemainderComparison.Serif.Stage
import YM.RemainderComparison.Passion.Permit
import YM.RemainderComparison.Canon.Shadow
/-!
# Unmarked extraction at this origin
Actual denominator here refers to polynomial at marker zero (incl calibration
perturbation at this step). When the input is required to be from actual Family.C,
caller checks UNMARKED at that origin. No globally uniform log of the complex
conditional polynomial.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Serif
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling OmitClusters AnalyticBridge.VerifiedReset
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι α : Type}
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Lotus.Leaf R)(H:Cash W x μ L Q o C T R) {q A B b e u v d L' Gp:ℝ}{j n k s J I:ℕ}(χ:Chi)
open Lyric Mosaic Muse Sleet
variable (Z:Set ι)(l:ι→ℝ) (δ:ℝ)
open Verse Marker Script
variable {β:Type} [DecidableEq β]{Jm:Census β}
variable (U:Pad H j χ)
local notation "Lt"=> sits Z l δ
variable {τ κ K Y γ V T0:ℝ}
variable (h:Roles H χ U k s J I a d e K σ Y γ V T0) (hh:Motto M l δ H τ K Y I)
variable (z:ι→Poly Jm) {fP:β→ℝ} (hZ : Chorus Jm fP Z z k)
open Mallow Ovens Progress.DirectedRecipe
variable [Countable ι] (V:Config G f)
local notation "Mx" => TuneR M Z l δ
local notation "f₀" => fun _ :ι=> (0:Marker.Poly Jm)
local notation "Iv" => Drums M S
include h hh hZ
lemma ingress : Integrable (TuneR M Z l δ z S) (prior G _) ∧ StronglyMeasurable (TuneR M Z l δ z S):=by
    let P i X:= (raw M (i:Iv)).paint Z (sits Z l δ) z X
    obtain ⟨t,hp,hF⟩:= Serif.input_pay M H χ Z l δ U h hh z hZ
    have hb :StronglyMeasurable fun X=> ∑' i : Iv,P i X :=by
       apply StronglyMeasurable.tsum; intro i; let hx:= (team M i).sells H.laws.intake.cap; let C:= controls Z z (raw M i).letters; have hh : Measurable fun X=> ((raw M i).stock Lt)*((team M i).cicada X):= measurable_const.mul hx.1.meas
       exact hh.stronglyMeasurable.smul_const C -- method?
    refine ⟨Integrable.of_bound hb.aestronglyMeasurable (∑' i,t i) (ae_of_all _ (fun X=>?_)),hb⟩
    change ‖∑' i,P i X‖ ≤ _
    have hv : Summable fun i=>‖P i X‖:= hp.of_nonneg_of_le (fun _=>norm_nonneg _) (fun i=> hF i X)
    exact (norm_tsum_le_tsum_norm hv).trans (hv.tsum_le_tsum (fun i=> hF i X) hp)

variable {D:ι→ Finset β} (hp:Passion.Oriented D Jm Z z)
include hp
omit [Countable ι] in
lemma zero_part : Poly.part (TuneR M Z l δ z S V) Jm.quiet= Poly.part (TuneR M Z l δ f₀ S V) Jm.quiet:=by
    have hi: Serif.Chorus Jm fP Z f₀ k:= ⟨hZ.votes,fun _=>by simp, fun _ _=> by simp, fun t ht=> Lacuna.paintless Jm Z t (ne_of_gt (lt_of_le_of_lt (Nat.zero_le _) ht))⟩
    have ht: Summable (fun i:Iv=> (raw M i).paint Z Lt z V):= (Serif.input_pay M H χ Z l δ U h hh z hZ).summable V -- [Countable?]
    have hv: Summable (fun i:Iv=> (raw M i).paint Z Lt f₀ V):= (Serif.input_pay M H χ Z l δ U h hh f₀ hi).summable V
    unfold TuneR; rw [Poly.share ht,Poly.share hv]; refine tsum_congr fun i=> ?_
    unfold paint; let q:= (raw M i).letters; by_cases hh:Verse.load Z q=0
    · rw [Flues.cold Z z _ hh,Flues.cold Z f₀ _ hh]
    rw [Lacuna.paintless Jm Z _ hh,smul_zero,Poly.part_smul,Passion.positive hp _ hh,Poly.part_nil,mul_zero]
-- recovery.Pβ ALL MASTER. Price.Den. when parsing countable sums.PRO
variable (hV:Z=Set.univ)
include hV
omit [Countable ι] in
lemma read_zero : Poly.part (TuneR M Z l δ z S V) Jm.quiet=(R.eval V:ℂ):=by
   rw [zero_part M H χ _ _ _ U h hh z hZ V hp,hV, Canon.null Jm l δ M V]; unfold Lacuna.tint; rw [Poly.part_smul]; simp
end YM.RemainderComparison.Serif
