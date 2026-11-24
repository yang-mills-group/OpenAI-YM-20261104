import YM.OPE.Compatible.Cant.Pion
import YM.OPE.Compatible.Cant.Knit
import YM.OPE.Compatible.Cant.Ki
import YM.OPE.Compatible.Cant.Void
import YM.OPE.Compatible.Tips.Thel
import YM.OPE.Compatible.Cant.Hoe
/-!
# The phase shift in each argument of the pairing

`YM.OPE.Stroke.tokEq` identifies each phase of `TokZ` with the corresponding coefficient of the token pairing on the lifted vectors.
With the site condition `Pins` and the bounds in `Attest`, shifting either argument by `τΓ` multiplies the token by `Ū`. The resulting coefficient identities give `applauded`.
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
variable {Y:M→ℝ}{V:(i':M)→ Alps K T i (Y i')}{A':(i:ℕ)→ Submodule ℝ (Bead G l i)}{hq:1 ≤ Y}{U:Z.Ω M Y}
local notation "J!"=> Fin (l+1)
local notation "F!"=> Tracts G d τ
local notation "μ"=> lapPrice (Patch.L P)
-- Read each phase of the lifted bilinear form from the token coefficients.
variable (e': Fin (l+1))(S:Submodule ℝ (Bead G l e'.val)) (V₀:Even n.val)(x y:Site n) (hx:Pins K P x y)(hp:Attest G P d k e'.val l m τ n)
open JetS
section
noncomputable abbrev TokZ (r:ℕ): ΦB (↥S):=fun i=> Lais Hp Z a e' r V₀ i x y S
lemma tokEq (v w:Jewel S)(i:Phase)(r:ℕ):TokZ Hp Z a e' S V₀ x y r i v w=(WingP Hp Z a V₀ x y (Plato Z _ S e'.isLt v) (Plato Z _ S e'.isLt w) r).seq i.val:= (WingS Hp Z a ..).symm
lemma rocksV (Ψ:F→F)(Γ:E→E)(f:F→E)(g:E→ E→ Token)(e:F→F→Token)(ht:∀ x y,e x y=g (f x) (f y))(hv:∀ x, f (Ψ x)=Γ (f x))(hh:∀ x y,g (Γ x) y=Ū*g x y∧ g x (Γ y)=Ū*g x y)(x y:F): e (Ψ x) y=Ū*e x y∧ e x (Ψ y)=Ū*e x y:=by simp only [ht,hv,(hh ..).1,(hh ..).2,true_and]
include hx hp
set_option maxHeartbeats 200000 in

lemma higher (u v:Jewel S):
   let f:=fun u v:Jewel S=> WingP Hp Z a V₀ x y (Plato Z e'.val S e'.isLt u) (Plato Z e'.val S e'.isLt v) 0
   f (τΓ (S:Type) u) v=Ū*f u v ∧ f u (τΓ (S:Type) v)= Ū*f u v:=by
      intro f; exact rocksV (fun x=> τΓ (S:Type) x) (fun x=> WaneZ Z e'.val e'.isLt x) (fun x=> Plato Z e'.val S e'.isLt x) (fun x' y'=>WingP Hp Z a V₀ x y x' y' 0) f (fun _ _=>rfl) (sprain Z e'.isLt S) (Polygon0 Hp Z a V₀ x y hx hp 0 e'.isLt) u v
omit hx hp
lemma workU [NormedAddCommGroup E][NormedSpace ℝ E] {V:ΦB E}(f:Jewel E→ Jewel E→Token)(h:∀ x y,f (τΓ E x) y=Ū*f x y∧ f x (τΓ E y)=Ū*f x y)(he:∀ x y (i:Phase),V i x y=(f x y).seq i.val):Job V:=by
      constructor <;> intros x y <;> (simp_rw [he,(h ..).1,(h ..).2]; first| exact ⟨boneS _,boneS _⟩| exact ⟨boneL _,boneL _⟩ | exact ⟨boneH _,boneH _⟩)
include hx hp
lemma applauded : Job (TokZ Hp Z a e' S V₀ x y 0):= workU _ (higher Hp Z a e' S V₀ x y hx hp) (fun u v i=>tokEq Hp Z a e' S V₀ x y u v i 0)
end
end YM.OPE.Stroke
