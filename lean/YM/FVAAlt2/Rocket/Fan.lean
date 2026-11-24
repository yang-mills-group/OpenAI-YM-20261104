import YM.FVAAlt2.Rocket.Scale
import YM.RegulatorIR.Atlas.Resonate
/-! Coherence passage. At any shared point (overlap with subfamily) the calibration
    & cover illuminated data have identical coefficients through min budgets. No
    need before applying to cumulative stops or trunc-order frames to set a numerical
    Borel-coupling interpolation independent of order/audits etc. This is the CORE germ
    in the `RegulatorIR.KFrame.Program` calculator. Connected headings on this side. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Rocket
open Function Budget Spatial Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Ledger.Sky Step Matrix StopB Ward Uniform Finset Halo Halo.Sight Gain Profiles Sources Labels Source Clocks
open Oracle Epoch Epoch.League Calibration Kick
open YM.FVAAlt2
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius
variable {X Y I:Type}{u₁ u₂ p q h:ℕ}{M:X→ℕ}{N:Y→ℕ}{m:Page M→Side}{n:Page N→Side}{G:Gauge}
variable (A:Circuit M m)(S:Circuit N n){K:KernelChoices}(P:Oracle.Program K)(Z:∀ U: Patch,U.Branches K G) (g:G.ColorIndex)
variable {x:X→Room}{F:Calibration.Tent M}{H: Calibration.Tent N}
variable (v:Epoch.League.Section A S) (hV:∀ x:X,v.connects ((native M).choose x)=(native N).choose (v.cast_r x))
local notation "ΑΘ"=> A.payroll P G Z (sheet F)
local notation "ΣΘ"=> S.payroll P G Z (sheet H)
-- Gauge Section nominal toll compatibility preserving top
variable (hF: Notebook A P G Z g (native M) F p)(hH:Notebook S P G Z g (native N) H q)
include hV hF hH
lemma binders (e:ℕ)(he:e≤p)(hf:e≤q): (∀ i:Page M, Squares e (tale (sheet F i|>.beta)) (tale (sheet H (v.connects i)|>.beta ))) ∧ ∀ i:Page M,Matches e ((ΑΘ).bulk i) ((ΣΘ).bulk (v.connects i)) :=
    Atlas.alike A G P Z S v hV g hV (shrinks A P G Z g hF he) (shrinks S P G Z g hH hf)
lemma scenes (e:ℕ)(he:e≤p)(hf:e≤q) (A': (ΑΘ).Report h)(S':(ΣΘ).Report h)(h:∀ w:X, Matches e (A'.main (Page.opening M w)) (S'.main ( Page.opening N (v.cast_r w)))):
    ∀ i:Page M, Matches e (A'.main i) (S'.main (v.connects i)):=by
   obtain ⟨h₁,h₂⟩:= binders A S P Z g v hV hF hH e he hf
   have ht:= fun w:X=> (show v.connects (Page.opening M w)= Page.opening N (v.cast_r w) from hV w)
   refine Page.proves (fun w=>?_ ) ?_
   · rw [ht]; exact h w
   intro w hv; rw [v.previous] at hv; have he:=h₂ w.prev; rw [v.previous] at he; rw [v.next,← A'.step_m,← S'.step_m]; exact (Atlas.grainS A G P Z S v ht w (h₁ _)).wave_step he hv
-- placements, same denomination
variable {F':Frames G}{H':Hol G}(R:Lobby.Registry F' H')[LinearOrder I]
lemma Bookkeeping (s:Finset I)(k:I→ℕ)(z:(i:I)→(F'.level (k i)).Index)(J:Choice M)(j:Choice N)(x:Y→I→Cover)
   (hv:∀ w,v.connects (J.choose w)= j.choose (v.cast_r w))(he:u₁≤p)(hh:u₁≤q)(i:X):
    stopped A P Z F R s k z J (x∘v.cast_r) i u₁ = stopped S P Z H R s k z j x (v.cast_r i) u₁ :=by
    have ht:= scenes A S P Z g v hV hF hH u₁ he hh ( Ignite A P Z F R s k z (x∘v.cast_r) ) ( Ignite S P Z H R s k z x) (fun w _ _=> rfl); specialize ht (J.choose i); rw [hv i] at ht; exact congr_arg₂ (fun T _=> note (T 0)) (ht u₁ le_rfl) (rfl:()=()) -- implicit
end YM.RegulatorIR.FVAAlt2.Rocket
