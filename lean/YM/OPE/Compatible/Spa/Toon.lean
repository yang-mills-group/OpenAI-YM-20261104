import YM.OPE.Compatible.Spa.Laur
import YM.OPE.Compatible.Spa.Cosmos
/-!
# Sections and remainders for the filtered coordinate maps

`Mantle` combines the right inverses of `ReadK` from `ArtR` with the kernel
description from `Reef`. Under the common clip, cutoff, and compatibility
hypotheses, the resulting `Pipes` data intertwine the shifts and include `Charge Y`
bounds for the sections, readings, and deeper-flag remainders.
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
local notation "JΛ"=> Fin (l+1) 
open Pipes
local notation "Sγ"=> Sapling (V:=V) (H:=H) (hs:=hs) (hq:=hq) (hp:=hp) (a:=a) (D₀:=D₀)
abbrev Dux (G:Gauge)(l:ℕ)(A:(i:ℕ)→Submodule ℝ (Bead G l i))(t: Fin (l+1)):= ↥(A t.val)
private lemma mantleRemainder {κ:(e:J!)→ Mint Z e.val →ₗ[ℝ] Jewel (A' e.val)} (U:Z.Ω M Y)(hX:∀ j,(V j).clip=p')(T': Z.Floss V U hp (le_trans zero_le_one hq) k Hp a)(C:Bals Hp Z a A' κ) (hx : l*l ≤ τ 0) (L : Lance X) (e : J!) (f : I → M)
    (b : I → ℝ) (hb : 0 ≤ b) (x : (i : I) → U.flag e.val (f i))
    (h : Wealth (fun i => (x i).val) (Y ∘ f) b)
    (he : ∀ i, ReadK Z κ U e (f i) (x i) = 0) :
    ∃ y : (i : I) → U.flag (e.val+1) (f i),
      Wealth (fun i => (y i).val) (Y ∘ f) b ∧ ∀ i, (x i).val - (y i).val ∈ Sγ (f i) := by
  obtain ⟨y, hy, hrem⟩ := BayFin (hq:=hq) Hp Z a U hX T' C hx L e f b hb x h he 0 (fun _ => trims.be _)
  exact ⟨y, hy, fun i => (hrem i).1⟩

set_option maxHeartbeats 200000 in
lemma Mantle {κ:(e:J!)→ Mint Z e.val →ₗ[ℝ] Jewel (A' e.val)} (U:Z.Ω M Y)(hX:∀ j,(V j).clip=p')(T': Z.Floss V U hp (le_trans zero_le_one hq) k Hp a)(C:Bals Hp Z a A' κ) (hx:l*l≤ τ 0)(L:Lance X): ∃ R:(e:J!)→(m:M)→ Jewel (A' e.val)→ₗ[ℝ] U.flag e.val m, ∃ H:Pipes (E:=Tracts G d τ) (V:=Dux G l A') U.flag Sγ (ReadK Z κ U) (Gift G D₀.aware).toLinearMap R,H.Charge Y:=by
       choose f hf hF hz using fun e=>ArtR (hq:=hq) Hp Z a C T' e; have h:Pipes (E:=Tracts G d τ) (V:=Dux G l A') U.flag Sγ (ReadK Z κ U) (Gift G D₀.aware).toLinearMap f:=by
          refine ⟨U.first,fun i hi m=> U.moves i m hi, Reef (hq:=hq) Hp Z a U hX T' C hx L,hF,hz,cuspTop' (hq:=hq) Hp Z a U T', fun i x hx=> sapUp (A:=V i) (t:=x) (D₀:=D₀) a hp _ hx⟩
       exact ⟨f, h, hq, hf, fun e _ w b x h => TarJ Z U e w b x h,
         fun e _ f b hb x h he => mantleRemainder (hq:=hq) Hp Z a U hX T' C hx L e f b hb x h he⟩
end YM.OPE.Stroke
