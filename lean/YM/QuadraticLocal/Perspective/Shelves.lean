import YM.QuadraticLocal.Perspective.Sunday
import YM.QuadraticLocal.Germ.Stock
import YM.QuadraticLocal.Tint.Patrol
/-!
# Embed the full Mark polynomial toll when packing general U

Choose the cast once; ALL tests.Tent.Extension and all relevant roots in same representation.
No new K hist prices (even with old eligibility converted into values). Keep the old
constraint on its actual carrier. See `maskbackK`. This permits publications with arbitrary
inherited pre-analytic-budget and actual Path data. Uses `Hard.readdress{Price,Gas}`.
 The tests are still constrained to the Avatar.Real.Plan: see ScaleFit etc; here over any type.
-/
set_option autoImplicit false
noncomputable section
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
namespace YM.QuadraticLocal.Sunday.Filing
open Function Filter Set MeasureTheory
open Marker Lattice Wilson RG Progress.DirectedRecipe
open QuadraticLocal QuadraticLocal.Earn
open PhysicalNext PhysicalNext.Repeat
variable {θ:Type} [DecidableEq θ] {G:Gauge} {n: Side} {α β χ : Type} {R: Census θ} {P:Passport n θ}
variable {a b:ℝ} (U:RG.Rep G n) (hc:U.activities.Valid U.p a b)
variable (X:β→Earn.Row P R G α)(H: Tint.Incoming P U α χ R)
local notation "Ψ" => decoration U
local notation "γ"=> (filesK U.activities)
include hc
def paint : Tint.Incoming P (decoration U) α χ R:= ⟨H.old,H.hard.readdress (Filing.transport U hc)⟩
local notation "Φ"=> paint U hc H
lemma maskbackK (t:α)(j:ℕ)(W:Config G n)(he: (Φ).hard.hard t (filesK U.activities j) W≠0): (U.activities.forced j).eligible U.p.threshold W:=by apply H.hard.charged; change stuff (filesK U.activities) (H.hard.hard t) (filesK U.activities j) W≠0 at he; rwa [stuffed] at he
variable (w:θ→ℝ)(hw:∀ i,0 < w i)
variable {d d' :ℝ}
include hw
local notation "LC"=> (Tint.Patrol.picture X H)
local notation "Π"=> (Tint.Patrol.picture X (paint U hc H))
local notation "tᴷ"=> (transport U hc)
lemma pulse [Fintype θ] (hh: H.hard.Paid w U.p.B U.p.supportExponent d) (t:α): (Π).density t=(LC).density t := by
 let hS:= (transport U hc); funext W; have he: (decoration U).exponent W= U.exponent W:= by change U.v*_ - U.path.inChannels U.clip U.p U.beta W - (decoration U).activities.additive U.p W=_; rw [hS.same_sum]; rfl
 rw [Gallery.density, Gallery.density, he]; apply congr_arg; congr 1
 -- maybe one goal
 unfold Gallery.gas
 exact (Hard.readdressGas H.hard hS t W ( Hard.packet_summing H.hard hh U.p.exponent_pos.le hw t W ).hasSum).tsum_eq
lemma painted (he: H.old.Paid w U.p.B U.p.supportExponent d)(hh: H.hard.Paid w U.p.B U.p.supportExponent d'):
    (Φ).old.Paid w U.p.B U.p.supportExponent d ∧ (Φ).hard.Paid w U.p.B U.p.supportExponent d' := ⟨he, Hard.readdressPrice H.hard tᴷ hh⟩
-- Mark.Pol.Subject.Value can choose beta after Code.Tick` for each U, re-expression includes moved stencil proofs for any K.Location.Key.Year.Measure`. Need keep this trace in application.W.Pl paths.
omit hw
open QuadraticLocal.Affinity
variable {Y:θ→Type} [∀ i,AddCommGroup (Y i)][∀ i,Module ℝ (Y i)]
variable (A:∀ i,Set (Y i))(D:∀ i,Submodule ℝ (Y i))
variable (H: Tint.Incoming P U (Affinity.Wallet A) χ R)
set_option quotPrecheck false
local notation "Φℓ"=> paint U hc H
lemma lit (h:Taut P.support A D H.old)(hK:Crown P.support A D H.hard): Taut P.support A D (Φℓ).old ∧ Crown P.support A D (Φℓ).hard:= ⟨h,Crown.rename H.hard tᴷ hK⟩ -- implicit.Aspections.RG namespace priority
end YM.QuadraticLocal.Sunday.Filing
