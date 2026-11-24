import YM.FVA2.DerivD.Life
import YM.FVA2.DerivD.Rite
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.DerivD
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick Metric Real TopologicalSpace
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical Matrix ComplexOrder
open FVA2.Scale MS.Rake MS.Theater Level O.Score LogTime MS.Plane MS.Heat MS.Tone Momentum Rake.Geo
open Equator Facets Dframe O.Enh O.Bind O.Project
/-!
 # Actual shape regularity statements (any scheme with Staff)
   Log argument is negative the log of radius in length units of
   normalization. Even joint with radius on open positive length range.
 -/
open O.Canon O.Bind O.Enh O.Read
variable { G:Gauge }{n m k:ℕ}{p:Staff G}{V:Arenas G}{a:ℝ→ Cn}{H:ℝ→ Frames G}{A:Album G}
variable (h:Physical V a H) (he:Influence p (install V))
local notation "V0"=> install V
variable {x:Points n}
include h he
omit h he in
lemma regular_at (h:Influence p A)(p':Scan G n)(k:ℕ)(hp:x∈conf n): ContDiffAt ℝ ∞ ( fun t=>coeff k ( A n t p' )) x:= (Legible ( conf_open n ) ( fun _ ht=> h n _ ht ) p' k).contDiffAt ( (conf_open n).mem_nhds hp )
lemma along_far (hx:x∈conf n)(b:Q G)(k:ℕ)(u:Scan G n): ContDiffAt ℝ ∞ (fun x=> coeff k ( FarCoefficients V u x b )) x:= ( Legible ( F:=fun x (p:Scan G n)=> FarCoefficients V p x b ) (conf_open n) (fun _ hP=> establish h hP he b ) u k ).contDiffAt ((conf_open n).mem_nhds hx)
lemma goes_tag (hx:x∈conf n)(b:Q G)(k:ℕ)(u:Scan G n)(r:ℝ): ContDiffAt ℝ ∞ ( fun q:Points n×ℝ=> coeff k ( OPECoefficients V u q.2 q.1 b )) ( x,r ):= by
    have ht : ContDiffAt ℝ ∞ ( fun q:Points n×ℝ=> coeff k ( FarCoefficients V u ( squeeze q.2 q.1 ) b ) ) (x,r) := ( along_far h he ( squeeze_away hx r ) b k u ).comp (g:=fun q=>coeff k ( FarCoefficients V u q b )) ( f:=fun q:Points n×ℝ=> squeeze q.2 q.1 ) (x,r) ( by unfold squeeze; fun_prop );
    exact ht.congr_of_eventuallyEq ( ( continuousAt_fst ( p:=(x,r) )|>.eventually ((conf_open n).mem_nhds hx) ).mono (fun q hp=> congr_arg _ ( congr_fun ( Physical.shapes h q.2 q.1 hp ) b )))
lemma line_t (hx:x∈ conf n)(b:Q G)(k:ℕ)(u:Scan G n)(r:ℝ): ContDiffAt ℝ ∞ ( fun q:Points n×ℝ=> coeff k ( LogPricing V u q.2 q.1 b )) (x,r):= by
    have hx':ContDiffAt ℝ ∞ ( fun (q:Points n×ℝ)=> ( O.Score.fee ( -q.2 ) ( ( heft b:ℝ ) - ( totalG u:ℝ ) ) ) * ( coeff k ( OPECoefficients V u q.2 q.1 b ) ) ) (x,r):= ((Complex.ofRealCLM.contDiff.comp ( f:=fun t:Points n×ℝ=> Real.exp (- -t.2 * ( ( heft b:ℝ ) - ( totalG u:ℝ ) ) ) ) ( by fun_prop ) ).contDiffAt ).mul ( goes_tag h he hx b k u r );
    have hp(t:Points n)(r:ℝ): coeff k ( LogPricing V u r t b )= ( O.Score.fee ( - r ) ( ( heft b:ℝ ) - ( totalG u:ℝ ) ) ) * ( coeff k ( OPECoefficients V u r t b ) ) := by unfold OPECoefficients QuoteP O.Project.pack; rw [ coeff_C_mul, ← mul_assoc,mul_comm (O.Score.fee (- r) _), fee_mul,one_mul ];
    simp_rw [hp]; exact hx'
end YM.FVA2.DerivD
