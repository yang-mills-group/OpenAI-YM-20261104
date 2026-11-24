import YM.Frontier.Tuning.MovingBudget
import YM.Frontier.Tuning.ComplexSweep
import YM.Frontier.Tuning.PaletteB
import YM.Frontier.Tuning.HeldGate
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Paisley
import YM.Frontier.Tuning.Held
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Flotsam
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Plateau

/-! Locality on the inherited palette, before selecting score determinants. No admissibility of the COMPLEX combined argument should be assumed or needed to switch chart entries. -/
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2500000
noncomputable section
namespace YM.Frontier.Tuning.RecoilIdentity
open Held HeldGate
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Blaze Silica Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Clutch Matter PhysicalNext.Repeat.Alabaster
open Art Eider Flux Shield Poll Footage HeldBurst DensityTilt AngularReceipt TwoMotion TiltTogether
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {k k':Finset ℕ} {R A : Rep G f} {X : Coat T F} {e f':Payload G f} {l : ℕ}
variable {a W : ℝ}{τ:ℂ}{u u':Directions G f}{I I':Config G f}
variable {O:ChartRatio G}
variable {x y : Air f G}{Y : Support c}
variable {r s p q : ℂ} (ho : ∀ i y,e i y =r*R.activities.E i y+s*A.activities.E i y)
      (ht : ∀ i y, f' i y=p*R.activities.K i y+q*A.activities.K i y) (hf : Facing R A)
variable (hr : Intake P T X.x R) (ha : Intake P T X.x A) (hk : Room P S T X.x)
variable (J:Finset (Bond f))(K:ℝ)(V: Config G c)(j:Molecule S)
def rotor (e f':Payload G f)(R:Rep G f)(X:Coat T F)(O:ChartRatio G)(a W:ℝ)(l:ℕ)(τ:ℂ)(z:Air f G):= scTilt X τ R J K V z * floatC (vary X V) R (course X K R.beta z V) O a W (own j) τ l e f' j

def barC (R:Rep G f)(e f':Payload G f)(X:Coat T F)(O:ChartRatio G)(a W:ℝ)(l:ℕ)(j:Molecule S)(τ:ℂ):=let B:=lensS J G
  ∫ y, (∫ w, ComplexSweep.tiltQ (Pond.circuit B X.relating) R.beta τ w * floatC (X.wrapY y) R (Pond.spill B w) O a W (own j) τ l e f' j) ∂F.order G

variable {K':ℝ}(hc: Canary G K K') (hzL: Drivable X K K' V){γ:ℝ}
include hc hzL hr hf ho ht
lemma sameRotor (Q: ConnectedActivityE6.Target G P) (Z: Config G c)(hz:Z=V)(h:a>0)(hg:0<X.t)
   (ha : Intake P T X.x A) (hR: Room P S T X.x) (hh:8*a*X.t≤K/2)(y:Air f G) :
   skewIntegral X K W R (E:=ℝ) (fun _=>V) (fun i=> steer X K (worldZ X R.beta y) V) (fun i=>course X K R.beta y V) 0 y J Q a j τ e f'= rotor J K V j e f' R X Q.table a W Q.halo τ y := by
  unfold skewIntegral rotor floatC; dsimp only
  apply congrArg (scTilt X τ R J K V y * ·); apply prod_congr rfl; intro i hi
  let Y:= vary X V; let z:= course X K R.beta y V; let v:=worldZ X R.beta y; let u:= steer X K v V
  have hU:worldZ Y R.beta z=u:=proceeds X K hr.positive y V
  change emberC Y R (X.input v) u z Q.table a W (own j) τ Q.halo e f' i= emberC Y R (Y.input (worldZ Y R.beta z)) _ _ _ _ _ _ _ _ _ _ _ 
  generalize hi' : worldZ Y R.beta z=w
  have hs:u=w:=hU.symm.trans hi'
  have hx:= conquered X hc V v hzL (mul_pos h hg) hh
  have hy:= plastic (X:=Y) hx (mul_pos h hg)
  have hZ:=HeldGate.reel (O:=Q.table) (W:=W) (l:=Q.halo) (k:=own j) (τ:=τ) (x:=z) ho ht hf (X:=Y) hr ha hR hy i
  exact hZ.symm.trans (congr_arg (fun w=> emberC Y R (Y.input w) w z _ _ _ _ _ _ e f' i) hs)
section Borel
variable {N:Type*}[MeasurableSpace N] (ho':ShellAccess S G X.x W X.width γ) (N0 : N)
include ho ht hf ho'
lemma borel (ha : Intake P T X.x A)(hÑ:LocalRatio O) (Y:N→ F.Slice G)(z:N→ Air f G)(hY:Measurable Y)(hz:Measurable z):
  Measurable fun t=>rotor J K V j e f' R (X.wrapY (Y t)) O a W l τ (z t):= by
   obtain ⟨hj,hn⟩ := Flux.steering J X hc V hzL hY hz hr.ready ho' R.beta
   let Z t:= X.wrapY (Y t)
   let z' t:=course (Z t) K R.beta (z t) V
   change Measurable z' at hn
   have hF : Measurable fun t=>scTilt (Z t) τ R J K V (z t) := by
     let B:=lensS J G
     have hR:Measurable fun t=> lens₀ (Pond.circuit B X.relating) (Pond.swim B (z t)) := bulbB (fun i k=> measurable_const : Borel fun _ : N=> Pond.circuit B X.relating) ((Pond.swim_m B).comp hz)
     have hR':Measurable fun t=> lens₀ (Pond.circuit B (vary X V).relating) (Pond.swim B (z' t)) := bulbB (fun i k=> measurable_const : Borel fun _ : N=> Pond.circuit B (vary X V).relating) ((Pond.swim_m B).comp hn)
     have hs:Measurable fun t=> scalp J (Z t) V R.beta K (z t) := hj.mul (hR'.div hR)
     let f (w:Poll.Body (↥B)) := dotProduct w.ofLp ((Pond.circuit B (vary X V).relating)⁻¹ *ᵥ w.ofLp)
     have he : Continuous f:= by unfold f Matrix.mulVec dotProduct; fun_prop
     have hP : Measurable fun t=>phasePoly τ R (Z t) J K V (z t):=by
       refine Complex.continuous_exp.measurable.comp (measurable_const.add (measurable_const.mul (Complex.continuous_ofReal.measurable.comp ?_)))
       exact (he.measurable.comp ((Pond.swim_m B).comp hn)).div_const (2:ℝ)
     exact hP.mul (Complex.continuous_ofReal.measurable.comp hs)
   exact hF.mul (show Measurable (fun t=>floatC (drive X V (Y t)) R (z' t) O a W (own j) τ l e f' j) from PaletteB.float ho ht hf hr ha ho' hÑ measurable_const hY hn j)
end Borel

include ho ht
lemma transition (hp:X.relating.PosDef) (hh: J=edgesM S (ground R T l X.B j) X.B)(hl:500≤l)(ha : Intake P T X.x A)(hΛ:ShellAccess S G X.x W X.width γ)(hM:LocalRatio O)(hG:Room P S T X.x):
    barC J R e f' (vary X V) O a W l j τ=∫ y, (∫ z,rotor J K V j e f' R (X.wrapY y) O a W l τ z ∂X.dice) ∂ F.order G:=by
  apply integral_congr_ae (ae_of_all _ fun y=>?_)
  let Z:=X.wrapY y
  have hp': Z.relating.PosDef:=hp
  have hz':Drivable Z K K' V:=⟨hzL.good⟩
  let g w:= floatC (vary Z V) R w O a W (own j) τ l e f' j
  refine ComplexSweep.rotates J Z V hc hz' hr.positive τ g ?_ hp' ?_
  · subst J; intro z z' he
    rw [chargedU] at he
    change floatC _ _ z _ _ _ _ _ _ _ _ _ =floatC _ _ z' _ _ _ _ _ _ _ _ _
    refine HeldGate.coast ho ht hf (X:=vary Z V) hr ha hG (⟨Village.refl ..,?_,fun i hi=> Iff.rfl⟩: Borough (vary Z V) (vary Z V) _ _ _ _ _ _) hl _ (Subset.refl _)
    exact (Pond.observe _).1 he
  exact borel ho ht hf hr J K V j hc hzL hΛ ha hM (fun z:Air f G=> y) id measurable_const measurable_id
end YM.Frontier.Tuning.RecoilIdentity
