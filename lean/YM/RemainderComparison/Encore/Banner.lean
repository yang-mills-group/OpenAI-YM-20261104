import YM.RemainderComparison.Encore.Style
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Encore
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling OmitClusters AnalyticBridge.VerifiedReset Solos Lyric Mosaic Serif Marker GridRenewal.Rain
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge} {L f c : Side} {R:Rep G f}{S:StepData c f}
variable {θ ι:Type} [DecidableEq θ]{J:Marker.Census θ}
variable (M:ι→Lotus.Leaf R)(U:Config G f)(B:Set ι)(l:ι→ℝ)(z:ι→Marker.Poly J)
-- λ calibration log input can be used only after exact representation.B.Current. «ℓ» already debited for holder. K copies may carry projections.B.Cloud.Owns.Frame.Consumer contracts. No smallness derived from true exponential path alone at K.
variable {P:Teller G}{Q: ConnectedActivityE6.Target G P}{T:Tube G S}{W x μ a v c' w δ d:ℝ} {p o t : ℕ} {u:ConnectedActivityE6.Target.Order G W}
variable (H:Cash W x μ L Q u v T R)
variable {F:θ→ℝ}(h : Chorus J F B z t)(hp: Muse.Motto M l δ H a c' w p)
set_option quotPrecheck false
local notation "Ψ" => Muse.sits B l δ
local notation "Φ" =>primitive M U B Ψ z
local notation "P₀" => TuneR M B l δ z S
-- Include already-normal global mark exponent (field-free). Same input push, exact on all sectors. Can be singleton unit coefficient or ENTIRE germs kept separately. Doesn't increase RESIDUAL norm in S/K. Doesn't assume integrable or shorten geometry. Consumer adds pieces before reading parameter polynomials. Keep their own source mass.
open Marker
variable (V:Config G c) (P': Marker.Poly J) [Countable ι]
local notation "L'"=> TuneR M B l δ z S
include h hp
lemma oil : Integrable L' (prior G f):=by
    obtain ⟨hg,hL⟩:= luminous M B l H hp
    have hf : Dominated (fun v:Drums M S=> (Mosaic.raw M v).paint B Ψ z):= Serif.dominion M H B Ψ z h hg hL
    haveI :Countable (Drums M S):= inferInstanceAs (Countable (Subtype _)) -- edit
    have hx : Envelope L':=by
       refine ⟨Measurable.tsum (f:=fun i:Drums M S=> (Mosaic.raw M i).paint B Ψ z) ?_ , hf.bound⟩
       intro i
       unfold Verse.paint; have hb:= (((team M i).sells H.laws.intake.cap).1).meas; exact (Complex.continuous_ofReal.measurable.comp (measurable_const.mul hb)).smul measurable_const
    obtain ⟨C,hC⟩:= hx.cost; exact Integrable.of_bound hx.meas.aestronglyMeasurable C (Eventually.of_forall hC)
lemma moved : S.push R.beta (fun U=> cyclone P'*TuneR M B l δ z S U) V=cyclone P' * S.push R.beta L' V:=by
    let g : Marker.Poly J →ₗ[ℂ] Marker.Poly J := Algebra.lmul ℂ (Marker.Poly J) (cyclone P')
    let f := g.toContinuousLinearMap.restrictScalars ℝ
    have hv:= f.integral_comp_comm (StepData.push_slice (S.isKernel (funds_branch H.laws.intake.ready) R.beta) V L' (oil M B l z H h hp))
    unfold StepData.push; simp_rw [f.map_smul] at hv; exact hv
lemma miss {x:ℂ} (Q' R': Marker.Poly J) (hK:S.push R.beta L' V=x • (cyclone Q'*R')) :
    S.push R.beta (fun U=> cyclone P'*TuneR M B l δ z S U) V= x • (cyclone (P'+Q')*R'):=by rw [moved M B l z H h hp V P',hK, GridRenewal.Rain.plus,mul_assoc,mul_smul_comm]
end YM.RemainderComparison.Encore
