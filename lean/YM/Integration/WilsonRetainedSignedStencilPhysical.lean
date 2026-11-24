import YM.Integration.WilsonRetainedSignedStencilBooks
import YM.Integration.WilsonRetainedSignedStencilMass
import YM.Integration.WilsonRetainedStencilPhysical

/-! Charge the product of the actual independently read real Wilson leaves on the clear sample. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonRetainedSignedStencilPhysical
open Function Lattice RG Pressure Tree Wilson Source ConnectedActivityE6
open RGLocalTaylor RGLocalTaylor.Insert PhysicalNext.Repeat.Legato Finset
open Dict06.Series AnalyticBridge.LocalGaussianLaws Precision
open WilsonCoherentMayerProjection (restrict)
open WilsonRetainedSignedStencilTaylor WilsonRetainedSignedStencilBooks
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G:Gauge} {c f:Side} {S:StepData c f} {T:Tube G S} {F:Forest S.ratio}
variable (R:Run G) {I:Type} [Fintype I] (d:I→ℕ) (φ:I→Reading) (θ:ℝ) (y:∀i,R.family.label (d i)) (o:I→Site f)

def marked (X:Coat T F)(β:ℝ)(z:momentSpace X)(t:ℝ):ℝ:=
  let Y:=X.wrapY z.1
  ∏i,φ i (Push.Local.presented (R.family.localSection (d i)) (o i) θ (y i)
    (Y.input ((t*(Coat.gStep β)⁻¹) • Y.liftA β z.2)))

theorem actual (X:Coat T F){β:ℝ}(pos:0<β)(z:momentSpace X):
    marked R d φ θ y o X β z (Coat.gStep β)=
      ∏i,φ i (Push.Local.presented (R.family.localSection (d i)) (o i) θ (y i)
        ((X.wrapY z.1).input ((X.wrapY z.1).liftA β z.2))):=by
  have hg:Coat.gStep β≠0:=inv_ne_zero (Real.sqrt_pos.mpr pos).ne'
  simp [marked,mul_inv_cancel₀ hg]

theorem path {P:Teller G}(fund:P.Funds S T)(X:Coat T F)(V:X.V=1)
    (clear:Assembly.Clear S X.x X.seeds F){β:ℝ}(pos:0<β)(z:momentSpace X)(t:ℝ):
    marked R d φ θ y o X β z t=row R d φ θ y (t • restrict R d F o z.2):=by
  unfold marked row
  dsimp only
  apply prod_congr rfl
  intro i _
  apply congrArg (φ i)
  have clean:=WilsonRetainedStencilPhysical.path R (fun _:Unit=>d i) θ (fun _:Unit=>y i)
    (fun _:Unit=>o i) fund X V clear pos z t
  have coordinate:((t • restrict R (fun _:Unit=>d i) F (fun _:Unit=>o i) z.2) default)=
      (t • restrict R d F o z.2) i:=by
    funext e
    rfl
  simpa only [WilsonCoherentMayerField.marked,WilsonCoherentMayerProjection.content,Fintype.prod_unique,
    coordinate] using clean

theorem received {P:Teller G}(fund:P.Funds S T)(X:Coat T F)(V:X.V=1)
    (clear:Assembly.Clear S X.x X.seeds F){β:ℝ}(pos:0<β)(z:momentSpace X):
    ContDiffAt ℝ ∞ (marked R d φ θ y o X β z) 0 ∧
      ps (marked R d φ θ y o X β z)=books R d F o φ θ y z.2:=by
  rw [show marked R d φ θ y o X β z=(fun t=>row R d φ θ y (t•restrict R d F o z.2)) from
    funext (path R d φ θ y o fund X V clear pos z)]
  exact issued R d F o φ θ y z.2

def Coupon (p:ℕ)(C:ℝ):Prop:=
  ∀θ:ℝ,∀y:∀i,R.family.label (d i),∀{c f:Side}{S:StepData c f}{T:Tube G S}{F:Forest S.ratio}{P:Teller G},
  ∀o:I→Site f, P.Funds S T→∀X:Coat T F,X.V=1→Assembly.Clear S X.x X.seeds F →
  ∀β:ℝ,0<β→∀z:momentSpace X,∀g:ℝ,0<g →
    |marked R d φ θ y o X β z g-∑j∈range (p+1),g^j*PowerSeries.coeff j (books R d F o φ θ y z.2)|≤
      WilsonCoherentReportingPivot.mass R d θ y*(C*(g*‖restrict R d F o z.2‖)^(p+1))

theorem purchased (p:ℕ):∃C:ℝ,0≤C ∧ ∀φ:I→Reading,(∀i z,|φ i z|≤‖z‖) → Coupon R d φ p C:=by
  obtain ⟨C,nonneg,price⟩:=WilsonRetainedSignedStencilMass.purchased R d p
  refine ⟨C,nonneg,?_⟩
  intro φ cap θ y c f S T F P o fund X V clear β pos z g hg
  let A:=restrict R d F o z.2
  let B:=books R d F o φ θ y z.2
  let l:=fun i=>(R.family.labels.level (d i)).scaled θ⁻¹ (y i)
  have bill:=price φ cap θ y A g hg
  change ‖material R d φ l (g•A)-∑j∈range (p+1),g^j • ordinary j (fun u:ℝ=>material R d φ l (u•A))‖≤_ at bill
  have value:material R d φ l (g•A)=(marked R d φ θ y o X β z g:ℂ):=by
    rw [path R d φ θ y o fund X V clear pos z]
    exact real_product R d φ l _
  have each(j:ℕ):ordinary j (fun u:ℝ=>material R d φ l (u•A))=((PowerSeries.coeff j B:ℝ):ℂ):=
    graded R d F o φ θ y z.2 j
  have sum:(∑j∈range (p+1),g^j • ((PowerSeries.coeff j B:ℝ):ℂ))=
      ((∑j∈range (p+1),g^j*PowerSeries.coeff j B:ℝ):ℂ):=by
    rw [Complex.ofReal_sum]
    exact sum_congr rfl fun j _=>by rw [Complex.ofReal_mul,Complex.real_smul]
  simp_rw [each] at bill
  rw [value,sum,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at bill
  exact bill

theorem selected (p:ℕ):∃C:ℝ,0≤C ∧ ∀s:I→Bool,Coupon R d (part ∘ s) p C:=by
  obtain ⟨C,nonneg,bought⟩:=purchased R d p
  exact ⟨C,nonneg,fun s=>bought (part ∘ s) (fun i=>contracted (s i))⟩

def phase (c:ℂ):Reading:=Complex.reCLM.comp (c • ContinuousLinearMap.id ℝ ℂ)

theorem rotated (p:ℕ):∃C:ℝ,0≤C ∧ ∀a:I→ℂ,(∀i,‖a i‖≤1) → Coupon R d (fun i=>phase (a i)) p C:=by
  obtain ⟨C,nonneg,bought⟩:=purchased R d p
  refine ⟨C,nonneg,fun a cap=>bought _ ?_⟩
  intro i z
  apply (Complex.abs_re_le_norm (a i*z)).trans
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (cap i)

end YM.Integration.WilsonRetainedSignedStencilPhysical
