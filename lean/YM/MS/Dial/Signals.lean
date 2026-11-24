import YM.MS.Dial.Watch
/-!
# PT cutoff comparison. Main endpoint. Unique exponent eliminates arbitrary constant.
 Conventions documented in manuscript/proof notes. Positive power margin uniform eft.Mesh
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Dial
open Set Function Filter Finset Metric MeasureTheory Real High
open Plane Koszul Landau Detect Heat Tone Latch Latch.Job Rake Orbit Breeze Book Convolve Flux
open Osc Snap City Job Geo Land Local.Physical Port Tide Vista Fleet
open Vane PeakT Program Menus Swirl Swirl.Near Native Wilsonian
open Puff Engine SplitP Actors Puff.Mom
open scoped Topology ContDiff
variable {W I:Type}{G:Gauge}{B:Deck G}[LinearOrder W] {F:Finset W}
   (φ: LitBook B)(L: W→Label B)(P:Trial I W){O:Booked B}{μ:ℝ} {b:Bool} {A:Prescription B} {V H:Terrify W I}
lemma measure (F:Finset W) (hp: Cutoff φ L P μ b A V)(hx: Cutoff φ L P μ b A H) (i:I): bury i F V=bury i F H:= classicalμ ( τ_nil .. ) (hp i F ) ( hx i F ) -- args
lemma separate (hp:Cutoff φ L P μ b A V)(hx: Cutoff φ L P μ b A H)(hv:V ∅=0)(he:H ∅=0): V=H:= by
   let t (v:Terrify W I)(i:I): Finset W→ T ℂ := fun s k=> v s k i; funext s n i; have hp1(y:Terrify W I)(hy:y ∅=0): Happy (marked W) (t y i):= Tide.pointed _ hy i;
   have hx1(y:Terrify W I)(x:y ∅=0): Puff.Log.Meter Trunk ( marked W ) (fun s=> bury i s y )= t y i:= Puff.Log.recheck _ _ _ (show t y i∈ allIndex _ _ from fun i _=> fun n _=> Submodule.mem_top ) ( hp1 y x );
   have hV := hx1 V hv; rw [funext (fun F=> measure φ L P F hp hx i), hx1 H he] at hV; exact ( congr_fun ( congr_fun hV s ) n ).symm
-- universes. genuine Θ fixed.H no assumptions.Arch + separate assures meaningful.Main.
omit [LinearOrder W]
theorem LPT_to_MS {S:Gauge}{D:Deck S}{A:Booked D}(L:LitBook D)(F: MS_Data S A)(h:S.Simple) : ∃ Ξ: Prescription D, TaylorOK F L Ξ ∧ ∀ (W I:Type) (_:LinearOrder W)(P:Trial I W) (l:Filter I) (μ:ℝ)(u:W→Label D)(b:Bool), Uses P l μ → ∃! V:Terrify W I,coherent A F L u P μ b Ξ l V:= by
   obtain ⟨Ξ,H⟩:= High_stops h F L; refine ⟨Ξ,H,fun W I _ P l μ u b hp=>?_⟩; obtain ⟨V,hV⟩:= check_t F L u P H hp h b; exact ⟨V,hV, fun y hy=> separate _ _ _ hy.cost hV.cost hy.init hV.init⟩
-- hG used solely high.Stencil.horizons
end YM.MS.Dial
