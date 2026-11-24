import YM.QuadraticLocal.Fk.Banner
/-! # Mark power bank; Header U attached to arrangement, not arbitrary smooth extension

Project true issued fields at their full g powers (the same λ_i exponent used on rescaling
 the origin links). Price theorem may require fixed horizons for spectral radii and proof of
 Leg.Acc; no assertion that the projected kernel budget alone implies the estimate.Instances.
 This binds the native prescription to invariant packet presentations of the whole slot-census
 input, **uniform in θ assignments** over any authorized phase. Can use in establishing more
 projection data for primary k.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Earn
open Function Filter Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis Bid Planned.JetPort
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open AllOrder AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Haiku.Coat AllOrder.Fire PertExtension.Series Radial
open AllOrder.Laplace AllOrder.Laplace.SigmaP Response AllOrder.Ink AllOrder.Ink.Method AllOrder.Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration AllOrder.Catch AllOrder.Catch.Clock AllOrder.Floe AllOrder.Plateau
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {V:Type}{G:Gauge} {n c:Side} {k j d r:ℕ} {a b σ :ℝ}
open Aperture Poetry Echo Work.G05 Toggle Aux Aux.Name Marker Multi
open QuadraticLocal.Sunrise
variable {ι α : Type} [DecidableEq V] {P:Passport n V} {R:Census V}
variable (M:ι→ Row P R G α)
namespace Air
variable (q:ι→ℂ)(w:V→ℕ)(U:Staff M q w a k)
variable (L:Layout G)(T:Finset Age)
set_option quotPrecheck false
open Comparison.RG02 Comparison.RG02.Bulk
local notation "Yₐ"=> Launch.index R w
local notation "Ptv" i:max=> ScatterR.actor M i
local notation "R₀"=> Air.craft M q w L T
local notation "μ" t:max=> (fun i:ι=> (ScatterR.actor M i).val=Subtype.val t)
variable (y:Stationary.Link G n)
def discharge (u:Bulk.Colors R G n) (j:ℕ) (x:Exterior.fieldDir G n 1) : Poly R:= Multi.lit R (fun i=> Assembly.jet (Bulk.projected (u.mark i)) (u.power i+j) (1,x))
local notation "D"=> discharge
local notation "x"=> (Stationary.arm G n 1 y)
local notation "Lm"=> (tint G (Exterior.Body 1 n) (Kinetic.Port.exteriorL G n y))
local notation "χ"=> Stationary.Link G n
local notation "E₀"=> ℝ × ( Stationary.Link G n )
-- Coastal operation; reference `Φ` pose uses arm; don't compute different field because of the name. this is a defeq
lemma posture_align : Stationary.arm G n 1 y= tint G ( Exterior.Body 1 n ) ( Kinetic.Port.exteriorL G n y ):= rfl
include U
-- receipts per-component across ALL names.Weight.Lit.Board.Regime.
variable (F' : Multi.Hot R) (j:ℕ)
local notation "Yq"=> (fun z: ℝ × Stationary.Link G n=> Stationary.input G n z.2)
local notation "P₃"=> ( Air.discharge ( R₀ ) j (Stationary.arm G n 1 y) )
local notation "t₀"=> ((R₀).power F'+j)
local notation "ν"=> (1:ℝ)
local notation "ζ"=> (((1:ℝ),y): ℝ×χ)
local notation "W"=> (Prod.fst : E₀→ℝ)
local notation "Q₀"=> (fun z:ℝ × Stationary.Link G n=> (R₀).mark F' z.1 (Stationary.input G n z.2))
lemma basis : HasSum (fun i:ι=> (Poly.send (M i).mode ( q i * Complex.ofReal ((M i).markReceipt j y))).part F'.val) ((Air.discharge ( R₀ ) j (Stationary.arm G n 1 y)).part F'.val):= by
 let p:= μ F'; let f i (z:E₀) := if p i then ScatterR.familyAt M q i z.1 (Stationary.input G n z.2) else 0; let k' := t₀
 let q₀:= (fun z: E₀=> (R₀).mark F' z.1 (Stationary.input G n z.2))
 let B:= (ContinuousLinearMap.id ℝ ℝ).prodMap (Stationary.arm G n 1|>.toContinuousLinearMap)
 let x₀:= ζ
 have ht: (P₃).part F'.val=Assembly.jet q₀ k' ζ:= Eq.trans (part_lit _ F') ( (Assembly.jet_continuous_right B ((Air.grade M q w U L T F').smooth.of_le le_top) x₀).symm) -- type ambient.J.Power.Gr.
 have hv(i): ContDiffAt ℝ ω (fun z:ℝ×Stationary.Link G n => G.mat (Stationary.input G n z.2 i)) 0:= by let Hp:= ContinuousLinearMap.snd ℝ ℝ (Stationary.Link G n); let H:=(Stationary.arm G n 1).toContinuousLinearMap; apply (Work.F03.represent_smooth i).contDiffAt.comp (f:= H ∘L Hp) 0 (H ∘L Hp).contDiff.contDiffAt
 have hg := (Air.rings M q w U p W (Yq) 0 contDiffAt_fst hv k' (fun _=> x₀)).2
 have H: HasSum (fun i=>Assembly.jet (f i) k' ζ) (Assembly.jet q₀ k' ζ) := by
    let ht: HasSum (fun i=> iteratedFDeriv ℝ k' (f i) (0:E₀) (fun _=>x₀)) (iteratedFDeriv ℝ k' q₀ (0:E₀) (fun _=> x₀)):= hg.congr_fun (fun i=> by by_cases h:p i; simp_rw [f,if_pos h]; simp_rw [f,if_neg h]) -- replace
    exact ht.const_smul _
 rw [ht]; apply H.congr_fun; intro i; unfold f; by_cases hh :p i;
 · simp_rw [if_pos hh]; let Q:= M i; let F₀:= (Row.replaceTest Q (q i)); rw [Poly.part_send, if_pos (show F'.val=(M i).mode from hh.symm),show k'=F₀.lamp.power+j from congr_arg (·+j) (congr_arg (·+1) (((congr_arg (Launch.index R w) hh.symm)).trans (U.written i).symm))]; exact (Row.powerAudit F₀ () j y).symm
 simp_rw [if_neg hh, Poly.part_send, if_neg (fun h : F'.val= (M i).mode=> hh h.symm),Assembly.jet]; simp
variable [Fintype V]
lemma compared : HasSum (fun i:ι=> Poly.send (M i).mode ( q i * Complex.ofReal ((M i).markReceipt j y))) (Air.discharge ( R₀ ) j (Stationary.arm G n 1 y)):= by
 apply Pi.hasSum.mpr; intro i; by_cases h:i=R.quiet;
 · change HasSum _ ((P₃).part i); rw [h,Air.discharge,part_lit_quiet]; exact hasSum_zero.congr_fun (fun i=> part_quiet_hot (ScatterR.actor M i) _) -- i binder RW RHS maybe lhs abstr degree.
 exact basis M q w U L T y (⟨i,(Comparison.RG02.Cumulants.hot_iff_ne _).2 h⟩:Multi.Hot R) j
end Air
end YM.QuadraticLocal.Earn
