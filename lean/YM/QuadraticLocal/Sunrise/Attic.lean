import YM.QuadraticLocal.Sunrise.Harvest
import YM.Comparison.RG02.Assembly.Core
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Sunrise
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function AllOrder AllOrder.Fire AllOrder.Laplace AllOrder.Laplace.SigmaP AllOrder.Ker
open Progress.ClassicalKin Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response AllOrder.Ink AllOrder.Ink.Method GaussianScore Module
open Marker Multi Comparison.RG02 Comparison.RG02.Order
open scoped BigOperators Topology Classical ContDiff
variable {V I:Type}[Fintype V][DecidableEq V][Fintype I] (J:Census V)
variable (p:I→ Poly J)
variable {X Y:Type} [NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y][FiniteDimensional ℝ Y]
local notation "φ"=> I→ℝ
local notation "M"=> MvPolynomial I ℝ
local notation "χω"=> (I→ℝ)×Y
local notation "ξ"=> Poly J
local notation "ν"=> Poly.bead J
open MeasureTheory
namespace Attic
open PowerSeries Bead Launch Reveal Assembly Next.SectorChange
local notation "τ"=> Scatter.transmit J p
local notation "Xs"=> series J
-- all v:E support.SE.Fixed real chart.All gauges.
variable [MeasurableSpace Y][BorelSpace Y](P:Law Y) (μ:Measure Y)[μ.IsAddHaarMeasure]
variable {K:Type}[DecidableEq K][Fintype K]
variable (Ω:Matrix K K ℝ)(hΩ:Ω.IsSymm)(hP:Ω.PosDef)(Z:Y→ (K→ ℝ)) (hZ:∀ f:(K→ℝ)→ℝ,P.average μ (f ∘ Z)=∫ i,f i ∂Gaussian.cloud Ω)
variable (U:X)(W:(K→ℝ)→ₗ[ℝ] X)(w:V→ℕ)(l:Hot J→ℕ)(F:Hot J→ X→ℂ)(g:X→ℝ)
variable (u : Book ((I→ℝ)×Y)) (hu:Clear u) (hx:u 0=0)
local notation "ρ"=> hom J w
local notation "Γ"=> climate P μ u
local notation "η"=> tag J p
local notation "δ"=> Gaussian.cloud Ω
local notation "χ"=> Assembly.prescription U W l F g Ω hΩ
local notation "Φ"=> fun i=> Assembly.expansions l F g (Assembly.translate U W i)
-- Unmasked Mark (real rank tags), Orientation.E.State ALL.S.Q.Report.P.S.Bind
abbrev reel (y:Y) := (fun i (x:I→ℝ)=> u i (x,y))
variable (hr:∀ y,Reveal.tag J p (fun i (x:I→ℝ)=>u i (x,y))= Launch.hom J w (Assembly.affine l F g (Assembly.translate U W (Z y))))
def rent : PTable J:= PowerSeries.mk fun i=> Poly.inject (fun t=>∫ z, insideMoment U W l F g t i z ∂Gaussian.cloud Ω)
local notation "Γ₀"=> rent J Ω U W l F g
local notation "Tt" => Reveal.tag J p Γ
local notation "Πt" r:max=> (χ r)
local notation "ι"=>Launch.index J w
include hr hu hx hP hΩ
omit hr hu hx in
lemma axle (r:ℕ) : Xs r Γ₀ = Πt r := by
 apply Join.both_parts; intro t a; rw [polarization,← (prescription_sym U W l F g Ω hΩ hP).observe_part t a]; congr 1; rw [rent,coeff_mk, order_read _ _ _ _ _ _ _ hP _ (Order.order_limit r a)]; rfl
omit hP hΩ in
lemma see_light (y:Y) : η (reel (EXP u) y)=ρ ((Φ) (Z y)):= Function.const _ (Function.const _ (Function.const _ (Function.const _ (Function.const _ (by
 have ht:Clear (reel u y):=by
    intro i; have h':= Response.nearStep («B»:=LinearMap.inl ℝ (I→ℝ) Y) ((0:I→ℝ),y) (hu i); simpa [reel] using h'
 have he: reel u y 0=0:= by funext x; rw [reel,hx]; rfl
 ext1 i; rw [← observation J i (η _) le_rfl, ← observation J i (ρ _) le_rfl, show reel (EXP u) y= EXP (reel u y) from rfl, ← pennant J p (reel u y) ht i he,show η (reel u y)=_ from hr y]; exact congr_arg (observe J i · i) (Reveal.lifted J _ _ w (Assembly.exponent_identity _ _ _ _)).symm
  ) (inferInstance : FiniteDimensional ℝ Y)
  ) (inferInstance : MeasurableSpace Y)
  ) (inferInstance : BorelSpace Y)
  ) (inferInstance : DecidableEq K)
  ) (inferInstance : Fintype K)
include hZ
set_option maxHeartbeats 200000 in
lemma shows : Tt = ρ Γ₀ := by
 ext1 i; ext1 t
 let χ₀:=i - Launch.index J w t; let Ω₀:=insideMoment U W l F g t χ₀; let c:= (ρ Γ₀); let T'(i:ℕ):=coeff i (η Γ)
 let a:= (T' i).part t; let b:= (coeff i c).part t; suffices ht: ∀ d:ℂ→L[ℝ]ℝ,d a=d b from Complex.ext (ht Complex.reCLM) (ht Complex.imCLM)
 intro d
 let x(y:Y):= (Φ) (Z y); let y(z:Y):= τ (reel (EXP u) z i); let f:=d.toLinearMap ∘ₗ ((Poly.get t).restrictScalars ℝ).toLinearMap
 have he(i:Y)(j:ℕ):τ (reel (EXP u) i j)= coeff j (ρ ((Φ) (Z i))):=(pointer J p (reel (EXP u) i) j).symm.trans (congr_arg (coeff j) (see_light J p Z U W w l F g u hu hx hr i))
 have hh : d a= P.average μ (fun z:Y=> d ((y z).part t)):= by
   dsimp only [a,T']; rw [pointer]; exact Bead.ledger J p P μ (PureK.orient (Response.exp_p (fun i=> hu i) hx i)) f
 have hz:b= if Launch.index J w t≤ i then ∫ z, Ω₀ z ∂δ else 0 := by
   unfold b c; change Launch.see J (Launch.slow J w Γ₀) t i=_; rw [timing]; unfold Launch.see rent; rw [coeff_mk]; rfl
 rw [hh,hz]; unfold y; simp_rw [he,show ∀ y:Y, (coeff i (ρ ((Φ) (Z y)))).part t= if Launch.index J w t ≤ i then Ω₀ (Z y) else 0 from fun y=>Launch.timing J w _ _ _]
 split
 next ht=> rw [show (fun z=>d (Ω₀ (Z z)))=(d ∘ Ω₀) ∘ Z from rfl, hZ]; apply d.integral_comp_comm; have hΩ':= (Assembly.gather U W l F g Ω hΩ hP t (Order.pick χ₀ χ₀)).1; rw [picked _ le_rfl] at hΩ'; exact hΩ'
 next ht=> simp_rw [_root_.map_zero]; exact average_const ..
/-- Uniform WITH the physical Fk normalization at *any* regulator. hρ only about affine input,
    in particular no evidence about desired output estimate or approximations in this proof.
 -/
lemma mark (r n:ℕ)(h:n ≤ r)(t:J.Mode)(ht:t≠J.quiet): (τ (Response.connected P μ u (n+Launch.index J w t))).part t= (observe J r (Order.logMarked (χ r)) n).part t:= by
 have he(i:ℕ):= axle J Ω hΩ hP U W l F g i; have hb: Clear Γ:=climbable μ (fun i=> hu i) hx
 rw [← he]; exact reports_hot J p Γ hb Γ₀ w (toward μ hx) (fun i=> he i|>.symm ▸ (Assembly.prescription_unit U W l F g Ω hΩ)) (shows J p P μ Ω hΩ hP Z hZ U W w l F g u hu hx hr) t ht h
end Attic
end YM.QuadraticLocal.Sunrise
