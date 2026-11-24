import YM.MS.Dial.Loom
import YM.MS.FlatJet
/-!
# Higher momentum jets in separated continuum labels

To prepare for the quadrature estimate: use the *same* pinned momentum calculus
on additional derivative demands. Derive via multiplying external Fourier waves
(not recursing a continuity allowance on the cutoff).
-/
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
namespace YM.FVA2.Poesy
open YM.MS Function Set Filter Topology MeasureTheory Real
open MS.Plane MS.Koszul MS.Landau Detect MS.Heat MS.Tone MS.Latch MS.Latch.Job MS.Rake MS.Orbit MS.Breeze MS.Book MS.Book.Convolve Flux -- names fix
open MS.Osc MS.Osc.Snap MS.City MS.Rake.Geo MS.Land MS.Local.Physical MS.Port MS.Tide MS.Vista MS.Vane Wire
open scoped BigOperators ContDiff
variable {G: Gauge} {I W: Type} [LinearOrder W] (v:ℝ)
variable {A: Deck G}{B:Booked A}(S:MS_Data G B)
variable (d:ℕ)

def strike (d:QP): QP→L[ℝ]ℂ:= Complex.I • Complex.ofRealCLM.comp ( ∑ i:Axis, d i • ( ContinuousLinearMap.proj ( R:=ℝ ) i : QP →L[ℝ] ℝ) )
lemma strike_beam (d:QP)(e:QP): strike d e=Complex.I*( Momentum.pairing d e ):= by simp [strike, Momentum.pairing]
lemma drives {f:ℝ→QP} {d:QP} {p:ℝ}(h: HasDerivAt f d p)(v:QP) : HasDerivAt (fun t:ℝ=> bill ( f t ) v) ( bill (f p) v * strike d v ) p:= by
    have H (z:QP): strike d z=strike z d:=by rw [strike_beam,strike_beam ]; simp only [Momentum.pairing,mul_comm]; -- theorem.
    rw [H]; convert ((strike v).hasFDerivAt.comp_hasDerivAt p h).cexp using 1 <;> first|rfl| funext t; rw [ rights,bill,Function.comp_apply,strike_beam ] | rw [rights,bill,Function.comp_apply,strike_beam]; simp only [strike_beam]
section grads
variable {g:I→Measure QP}
def poleDer (d:QP) (F:Law G): Law G:= fun w=> strike d ( net w ) * F w
def rise (d:QP) (F:MS.Rake.Site G I): Site G I := fun n k j=> poleDer d ( F n k j )
lemma treeDer (d:QP) (f h: Law G)(p:Edge G): Plane.Flux.tree parity p f (poleDer d h)= poleDer d ( Plane.Flux.tree parity p f h ):= by
    funext l; let x:= net l; let z:= strike d (net l);
    unfold poleDer; change scatter _ _ _ = z • allocate _ _ (Plane.Flux.attaches ( Landau.parity (A:=Axis) (C:=G.ColorIndex) ) p f h); rw [ ← map_smul ]; refine scatter_congr _ _ _ _ (fun A B h=>?_ );simp_rw [Pi.smul_apply,Plane.Flux.attaches,neg_neg,net_cons,split_net h]; dsimp only [z]; simp_rw [smul_eq_mul, Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring
lemma cycleDer (d:QP)(F:Law G) (p:Edge G)(μ:Measure QP): Plane.Flux.cycle p μ (poleDer d F)=poleDer d ( Plane.Flux.cycle p μ F ):= by
    funext l; unfold Plane.Flux.cycle poleDer; simp only [Plane.Flux.at_trc,net_cons]
    rw [← integral_const_mul ]; simp only [add_neg_cancel_left, mul_left_comm (p _ _ _), Finset.mul_sum]
section CostL
variable {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E] (R:Scale I)
lemma boundE (F:E→L[ℝ]ℂ): Bound R (fun _=> F) (fun i=> (R.length i)⁻¹) := by
    have H: Bound R (fun i (_:E) => ( R.length i )⁻¹) (fun i=> (R.length i )⁻¹):= Costs.scalar ( Cost.of_le fun i x _=>by rw [norm_of_nonneg (inv_nonneg.mpr (R.pos i).le)])
    convert ( H.smul ( Scale.rescaled R (f:=F) F.hasTemperateGrowth ) ) using 1
    · ext i x; change F x=(R.length i)⁻¹ • F ( R.length i • x ); rw [ map_smul, inv_smul_smul₀ ( R.pos i|>.ne' ) ];
    ext i; simp
variable {b:Bool}{F:I→ Law G}{q:I→ℝ}
lemma budgetDer (d:QP)(h:Lease false b R F q): Lease false b R (fun i=> poleDer d ( F i ) ) ( fun i=> q i * ( R.length i )⁻¹ ):= by
    intro E _ _ w hw he; have hp := h E w hw he; have hx:= boundE R ((strike d).comp ( net w )); unfold Cape Plane.Chart poleDer; simp_rw [ sail_net ]; convert hx.mul hp using 1 <;> first| rfl| (ext; ring)
end CostL
variable {P:Belt I}
lemma rateDer (d:QP)(k:ℕ){F:Glade G I} {b:Bool}(h:Here false b P F (rateS P k)): Here false b P (fun i t=> poleDer d ( F i t )) (rateS P ↑(k+1)) := by
    convert budgetDer _ d h using 1; · rfl
    ext i; unfold rateS; push_cast; rw [neg_add', zpow_sub₀ (P.price.pos i).ne', zpow_one ,div_eq_mul_inv]
lemma warmDer (d:QP){F:Glade G I}(h:Warm F false): Warm ( fun i t=> poleDer d ( F i t )) false:= by
    constructor
    · intro i t ht; let T:= Job.single (camp t); have hh:= budgetDer _ d ( h.cost i t ht ); have hE : (fun i=> (1:ℝ)*( T.length i )⁻¹)=(1:camp t→ℝ):= by ext i; change 1*(1:ℝ)⁻¹=1; simp
      rw [show ( fun q:camp t=> (1:camp t→ℝ) q * _)= _ from hE ] at hh; exact hh
    intro i u hu; exact Continuous.const_mul ( h.walk i u hu ) _
lemma tip_der (d:QP){P:Geo I}{Z:Glade G I}{k:ℕ}(h: Tip P false false k Z): Tip P false false (k+1) (fun i t=>poleDer d ( Z i t )) := by refine ⟨?_, warmDer d h.2.1, rateDer d _ h.2.2 ⟩; obtain ⟨n,h⟩:= h.1; exact ⟨ n,fun i t w hw=> show _*Z i t w=0 by rw [ h i t w hw, mul_zero ] ⟩
lemma venDer (d:QP){f X:MS.Rake.Site G I}{K L:Planet G I}(h:Ven g K L X f): Ven g K L X ( rise d f ) := by
    intro n; refine ⟨ warmDer d ( h n ).smooth,fun i t p=>?_ ⟩; let a:= strike d (net t); apply ( show HasDerivAt ( fun u:ℝ=> a*f n i u t ) _ p from HasDerivAt.const_mul a ( h n|>.motion i t p ) ).congr_deriv; rw [Pi.add_apply, Pi.add_apply, Pi.add_apply, Pi.add_apply, Pi.add_apply, Pi.add_apply]; unfold sailP lonely expJ rise; simp_rw [Finset.sum_apply, treeDer, cycleDer,poleDer]; rw [mul_add,Finset.mul_sum]
end grads
end YM.FVA2.Poesy
