import YM.FVAAlt2.Pipeline.Readers
import YM.Comparison.RG02.Cumulants.Parents
import YM.Integration.RunFormalCoefficients
import YM.Integration.LocalFormalAction
/-! # RunFormal.Arch ports for our one-mark witness all periods specialized

(Note Warp uses ALL coefficient Germ for input after vacuum normalization; no recalibrating near elected orientation/phase parameters). Realty Lev.Clock.Body.Plan. No EIR estimate here. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Boot.Revenue
open Function Set Filter Finset MeasureTheory Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Geometry Prim Diagram Diagram.Formal PertExtension Series Series.Radial Series.Tested Chart Binding Ledger Gauge Booth
open Lattice RG Precision Comparison.RG02 Comparison.RG02.Bulk Comparison.RG02.Adjacent Comparison.RG02.FVAAlt2 Integral Wilson Exterior Arm Marker Multi
open PowerSeries Integration Integration.LocalFormal RunFormalChain PhysicalNext.Repeat.Legato
open scoped Topology BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius
variable {m :ℕ} {G:Gauge} {I X:Type} [DecidableEq I] {Q:KernelChoices} {M:X→ℕ} {N:Page M→Side}
open Oracle Period.Field Pipeline Pipeline.See
variable (C:Run G)(p n:ℕ)(H:Marker.Census I)(V:Boot.Scout (G:=G) m)(u:I)
local notation "K"=>fromRun C
local notation "Γ"=> C.family.path
set_option quotPrecheck false
local notation "g"=> C.family.side (n+1) p
local notation "U"=> ink H u Γ (n+1) p V
local notation "S"=> C.family.path.levels.clock.op n p
variable (t:ℝ)(a:Config G (C.family.side (n+1) p))
lemma real_mark : ( (markedLog t a U).part (H.fire u)) = ((t^m)⁻¹ • (↑(V.Vt (C.family.side (n+1) p) a) :ℂ)) := by
    unfold markedLog; rw [show ∀ b : Multi.Hot H→ℂ,(Multi.lit H b).part ( H.fire u )= b (pub u) from fun b=> part_lit b (Arm.pub u)]; unfold ink; simp only [↓reduceIte]
variable [Fintype I]
open Comparison.RG02.Laplace Bare
open YM.Extra.Trajectories (connected)
local notation "S'"=> (fromRun C).step (n+1) n p (Nat.lt_succ_self n)
lemma receiving : Bare.Witnessed U S':= by
    have h:= ( authentic H u Γ K (n+1) p V ).1; refine ⟨h,fun i=> ?_,fun t=>?_ ⟩
    · obtain ⟨M,hM⟩:= (h.prices i 0).cost; exact ⟨0,max 0 M,le_max_left ..,Eventually.of_forall fun t a=> by rw [pow_zero,mul_one]; exact (hM a).trans (le_max_right ..)⟩
    ext1 x; unfold model Bare.top Passes; unfold Integral.weight localClassic; rw [kept0 Γ K _ p]; unfold Wilson.bare ink; congr 2; dsimp only; ring_nf -- linear?
lemma dot_o : (Bare.top U t a).part (H.fire u) = (↑(Wilson.bare (temperature t) a):ℂ)* ((t^m)⁻¹ • (↑(V.Vt (C.family.side (n+1) p) a):ℂ)):=by
    unfold top Passes; rw [Marker.Poly.part_smul]; congr 1; rw [ ← Cumulants.lamp u (Marker.Poly.pass (markedLog t a U)) (Marker.Poly.pass_part _ (part_lit_quiet _)), Cumulants.connected_pass (show (markedLog t a U).part H.quiet=0 from part_lit_quiet _),real_mark]; -- ok
lemma towards (F : Tree.Forest (C.family.path.levels.clock.op n p).ratio)(o:(C.family.path.levels.clock.op n p).Choices)(x:fieldDir G (C.family.side n p) 1)(r:ℕ) :
    let D:LocalFormal.Datum C.family H:= ⟨n+1,p,n,Nat.lt_succ_self n,F,o,U,x⟩; let ρ:=Bare.realMoment S' F U o x
    Fleet.Test ( D.raw ( RunFormalChain.fromRun C ) r ) ρ ∧ Fleet.Test (D.ordinary ( fromRun C ) r) (Order.unitScale ∘ ρ) ∧ Trial (detail ( D.markedLog ( fromRun C ) r) (H.fire u)) (fun t=> (Order.unitScale (ρ t)).part (H.fire u)) r :=by
    intro D ρ; obtain ⟨he,hk,hv,hQ⟩:= Bare.wilson_step_test S' F U o x r ( C.family.path.levels.budget n ) (receiving C p n H V u)
    exact ⟨he,hv, trial_flow (hv (H.fire u)) (fun i hi=> Lyric.logo (Bulk.fk_sym ..) (Bulk.fk_unit ..) u hi) ⟩ -- maybe Lyric namespace ambig
-- Actually normalized quantities, compare $mass$ through all.
end YM.RegulatorIR.FVAAlt2.Boot.Revenue
