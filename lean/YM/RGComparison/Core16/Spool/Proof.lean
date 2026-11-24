import YM.RGComparison.Core16.Spool.Wages
/-!
# Uniform period estimate, TOP SEAM estimator Eng. coupling-field PColours

`Peer.θ` by full T law at one coarse link config. Prices from family AFTER patch & direction cap,
before actual φ state. This is not readout on unconditional torus measure.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Spool
open Function Filter Lattice RG Tree Wilson MeasureTheory Pressure Metric Forge
open PertExtension PertExtension.Series Tested Radial Therm Precision
open Lumen Lumen.Planet Parcel Parcel.Oven Next.Fluctuations Finset Complex Asymptotics
open Lumen.Stage
open scoped Topology ContDiff BigOperators Classical InnerProductSpace Matrix.Norms.Frobenius
variable {G:Gauge} {ι:Type}[Fintype ι] {c f : Side}
variable (J:ι→ Lamp G)
variable (S : StepData c f)(u:Directions G c)(p:ι→ Site f) (V:Config G c) (g:ℝ)

def column (U : Config G f) :ℂ:= tally J p U
-- σ reader not dropping normalization at any time, identical output polynomial used in `Marks.lean`.
def survey := S.push (g⁻¹^2) (fun U=>bare (g⁻¹ ^ 2) U • column J p U) (slice u g) -- f & G inference
-- actual vacuum (outside gas posterior recompression)
def spinVac:= S.push (g⁻¹^2) (bare (g⁻¹^2)) (slice u g)
def reads := g⁻¹^(power J) • ((spinVac S u g)⁻¹ • survey J S u p g)
lemma descended {β : ℕ → ℝ}(T:Forest S.ratio) (hβ:β 1=g⁻¹^2) : reads J S u p g=g⁻¹^(power J) • ((Descent.push S T Descent.nil).conditioned β (column J p) (slice u g)) := by
    unfold reads survey spinVac Descent.conditioned Descent.vacuum Descent.weighted; rw [Descent.output_push,Descent.depth,Descent.depth,Descent.output_push]; simp only [Descent.output_nil]; rw [←hβ]; rfl

local notation "s!"=> slice u g
variable {g}
lemma on_line (T:Forest S.ratio)(h:S.patch.Branches S.kernel G)(i:Bool) :
    look i (survey J S u p g) = Next.Fluctuations.Sector.prefactor S G (g^2)⁻¹ * ∫ y:Sky G T.Free,(Hut.seam S T s!).output g y * look i (column J p (T.drape y))∂skillet G T.Free:=by
    let β:=g⁻¹^2
    let F (U:Config G f):= bare β U • column J p U; let L:=skillet G T.Free; let W:=look i
    have hx : Continuous F:= (bare_cont β).smul (tally_cont J p); have hi: GaugeInvariant F:= fun k U=> congr_arg₂ (· • ·) (bare_gauge ..) (tally_invariant J p k U)
    let f':=(W ∘ F)
    have he: Integrable f' (Wilson.prior G f):= ((W.continuous.comp hx).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    change W (S.push β F s!)= _; rw [show W (S.push β F s!)=S.push β f' s! from ?_]; swap
    · unfold StepData.push; have hv:= (look i).integral_comp_comm (μ:=Wilson.prior G f) (φ:=fun x=> S.density β x s! • F x) (StepData.push_slice (S.isKernel h β) s! F (hx.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))) -- order signature
      simp_rw [map_smul] at hv; exact hv.symm
    rw [T.pushing (S.isKernel h _) _ _ (fun k x=> congr_arg W (hi k x)) he (fun k U=> S.covary h k _ U s!), ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x=> ?_); unfold f' F; dsimp only [Function.comp_apply]; rw [map_smul,smul_eq_mul,smul_eq_mul,←mul_assoc,show β= (g^2)⁻¹ from inv_pow ..,Hut.bill]; rw [mul_assoc]
lemma quiet (T:Forest S.ratio)(h:S.patch.Branches S.kernel G): spinVac S u g= Next.Fluctuations.Sector.prefactor S G (g^2)⁻¹ * ∫ y:Sky G T.Free, (Hut.seam S T s!).output g y ∂skillet G T.Free:=by
    unfold spinVac; rw [T.pushing (S.isKernel h _) _ _ (fun k x=> bare_gauge ..) (bare_integrable _) (fun k U=> S.covary h k _ U s!), ← integral_const_mul, inv_pow]; apply integral_congr_ae; filter_upwards with i; exact Hut.bill ..

section estimates
variable {S:StepData c f} {P:Oven S.patch} {X:Shelf G (PlaqAxes⊕ Axis) P.Xways}
-- define Y definally equal to S.Parcel... S might η; proof types

def lens (X:Shelf G (PlaqAxes⊕ Axis) P.Xways) (T: Forest S.ratio) : Planet X f T.Free (Hut.Rooms c f) S.Choices := Oven.parcela S.kernel X T u

end estimates
end YM.RGComparison.Core16.Spool
