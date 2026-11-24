import YM.FVA2.Change.Mark
import YM.FVA2.Laplace.Landau
/-!
# Evaluate full Wilson pose with marked Laurent valuations and converted fees

Canonical independent prescription here: `Dictionary.raw` full `Orb.diag` at even regulator with
external x^-total grade and `Dictionary.finite` applies source sums in the new coupling after
substitution. No Endμ construction given as hypothesis.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Change
open Function Set Filter Finset Lattice MeasureTheory Wilson
open MS MS.Koszul MS.Plane MS.Orbit MS.Swirl MS.Book Convolve Program MS.Menus MS.Cylinder Lab Taylor
open MS.Native Chart MS.Bare MS.Local.Physical MS.Rake MS.Land MS.Local.Physical MS.Fleet MS.Tide
open Slice FormalOPE.RG10 FormalOPE.RG10.MultiGauge Splice
open PertExtension PertExtension.Series Series.Radial Series.Tested
open PowerSeries (coeff)
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}{n:Side}{F:Dot G Cover} {k:ℕ} {A J W: Type}
local notation "E" => Transverse G n
local notation "V" => Chart.City G (Site n)
local notation "T" => Config G n
local notation "D" => PertExtension.Orb.Dir G n
local notation "T₀" => MultiGauge.Stack.rise
local notation "Φ" => nation (G:=G) (P:=Site n)
local notation "Q" => incCL G n
local notation "χ" => (Q: Transverse G n→Chart.City G (Site n))
local notation "Ξ" => PowerSeries.X

def joints {I:Type*}(f:I→Config G n→ℝ)(l:List I) : Config G n→ℝ:= (l.map f).prod
-- tree-Laurent can take any gauges; attaching rank via From uses all position legs
lemma pre_pair {O P:Config G n→ℝ}(h:Orb.PreTest O)(k:Orb.PreTest P): Orb.PreTest (O*P) where
 gauge u v f:= congr_arg₂ (· * ·) (h.gauge u v f) (k.gauge u v f)
 curved := ⟨h.curved.boundedness.mul k.curved.boundedness,h.curved.germ.mul k.curved.germ⟩
 continuous := h.continuous.mul k.continuous
variable (ev:Even n.val)
include ev
namespace Stencil
variable (X:Stencil F) (p:Cover)
lemma vote : Orb.PreTest (X.placed n p) := by
    have he := X.crease (n:=n) p; let β:D→L[ℝ] V:= Orb.variation.toContinuousLinearMap -- test
    have hb (x:D) : (Orb.restrictedO (X.placed n p) ∘ PertExtension.Chart.expLinks G _) x=(X.placed n p ∘ nation) (β x) := by
       change X.placed n p (Orb.representative x) = X.placed n p (Φ (β x)); apply congr_arg (X.placed n p)
       let z:= FVA2.Orbit.fan ev (FVA2.Orbit.Grove.rise PertExtension.Orb.Branch x); let A:=FVA2.Orbit.lit z; have hz:= FVA2.Orbit.Grove.tree_lift (G:=G) ev x; change z.val=β x at hz; have hq: FVA2.Orbit.touches G n z= _:= FVA2.Orbit.read_fan ev _; have he:= congr_arg nation hz
       rw [←FVA2.Orbit.Grove.tree_ignite, ← hq]; exact A.trans he
    refine ⟨fun u _ U=> X.invariant p u _, ⟨ (X.continuous_placed p).comp Orb.continuous_links,by rw [funext hb]; exact ((β.map_zero.symm ▸ he : ContDiffAt ℝ ω (X.placed n p ∘ Φ) (β 0)).comp (f:=β) 0 β.contDiff.contDiffAt).of_le le_top⟩, X.continuous_placed p⟩
end Stencil
omit ev
namespace Dictionary
variable {B:Deck G}{P:LitBook B}
variable (X:Dictionary P)(u: W→Label B)
local notation "R" => vertices u
variable (L:Cover)(d: W→Cover)
def stage (n:Side)(r: vertices u): Wilson.Config G n → ℝ:= (X.node r.2).placed n (L+d r.1)
local notation "W₀" => X.stage u L d n
def currency (l:List R) := (l.map fun r=> Glyph.grade r.2).sum
/-- The configured (pre-transform) raw real Wilson coefficients. External powers subject to the
rank supplied by P's actual stencils; $real^{-currency}$. -/
def raw (n:Side)(l:List (vertices u)) := MultiGauge.Stack.drop (currency u l) (PowerSeries.mk (Orb.diag (Orb.restrictedO (joints (X.stage u L d n) l))))
local notation "p" => X.raw u L d n
lemma approved (r:R) : From (r.2.lit P).val (Glyph.grade r.2):= (P.levels ..).low
lemma honored (l:List R) : Ξ ^ currency u l * positions (X.edge u L d n) l=T₀ ((joints W₀ l ∘ nation) ∘ incCL G n):= by
    have h (l:List R): germ ((joints W₀ l ∘ nation) ∘ incCL G n):= by
       induction l with
       | nil=>exact contDiffAt_const
       | cons a l ih=> exact (Axes.calm ((X.node a.2).crease (L+d a.1))).mul ih
    induction l with
    | nil=> change Ξ^0 * 1=T₀ (1:E→ℝ); rw [MultiGauge.Stack.rise_one,pow_zero,one_mul]
    | cons r l ih=>
      let y:= X.node r.2; let A:= (joints W₀ l ∘ nation) ∘ incCL G n; let C:= (W₀ r ∘ nation) ∘ incCL G n; let f:= X.edge u L d n r; let t:= positions (X.edge u L d n) l
      change Ξ ^ (Glyph.grade r.2+currency u l) * (f*t)=T₀ (C*A); rw [MultiGauge.Stack.rise_mul ( (show germ C from Axes.calm (y.crease (L+d r.1))).of_le le_top ) ((h l).of_le le_top),pow_add, show Ξ ^ Glyph.grade r.2 * Ξ ^ currency u l * (f*t)=(Ξ^Glyph.grade r.2*f)*(Ξ^currency u l*t) from by ring, show Ξ^Glyph.grade r.2 * f=T₀ C from y.giveback (L+d r.1) (approved (P:=P) u r), show Ξ ^ currency u l*t=T₀ A from ih]
include ev
lemma examination (l:List R) : Orb.PreTest (joints W₀ l):= by
    induction l with| nil=>exact FVA2.Orbit.Screen.pre_one | cons r l h=> exact pre_pair ((X.node r.2).vote ev (L+d r.1)) h
variable [Fintype J][DecidableEq J]
variable (a: Axes G n A J)(μ:Measure (Transverse G n))[Measure.IsAddHaarMeasure μ]
local notation "Y" => a.sumBody μ
local notation "Z" => X.edge u L d n
lemma exact_tree (l:List R) : Ξ ^ currency u l * Y (positions Z l)= PowerSeries.mk (Orb.diag (Orb.restrictedO (joints W₀ l))):= by
    rw [ ← fall a ev μ (X.examination ev u L d l), show MultiGauge.Stack.rise ((joints W₀ l ∘ nation) ∘ includeA G n)=_ from (X.honored u L d l).symm ]; unfold Axes.sumBody enjoy; rw [mul_left_comm a.relative, MultiGauge.Stack.taking, mul_assoc]
theorem evaluates (l:List R) : p l= Y (positions Z l):= by rw [raw, ← X.exact_tree ev u L d a μ l]; exact MultiGauge.Stack.drop_mul ..
include a μ -- remove arbitrary geometry deps w theorem via pick basis+a.AddHaar
lemma pre_neg (l:List R)(j:ℕ)(h:j<currency u l): Orb.diag (Orb.restrictedO (joints W₀ l)) j=0:= by rw [← PowerSeries.coeff_mk j (Orb.diag (Orb.restrictedO (joints W₀ l))), ← X.exact_tree ev u L d a μ,PowerSeries.coeff_X_pow_mul',if_neg (by omega)]
lemma maturity (l:List R): Tested.Aspiration (fun t:ℝ=> (t⁻¹)^(currency u l) * Orb.preExpectation (joints W₀ l) t) (Tested.term (p l)):= by
    have hv : Tested.Aspiration (fun t:ℝ=> (t⁻¹)^(currency u l) * Orb.preExpectation (joints W₀ l) t) (fun i=> Orb.diag (Orb.restrictedO (joints W₀ l)) (currency u l+i)):= ( Orb.before_tree_formula ev (Orb.traySpec G) (X.examination ev u L d l) ).shift (X.pre_neg ev u L d a μ l)
    convert! hv using 1; funext i; unfold Tested.term raw MultiGauge.Stack.drop; simp
variable [LinearOrder W]
variable (S: Finset W)
variable (M:Land.Prescription B)(x:ℝ)
def finite (S:Finset W)(M:Land.Prescription B)(n:Side)(x:ℝ) := convertSources (paid u M x) S.toList (fun l => Program.substitute (Program.shift M.team x) (Slice.record (X.raw u L d n l)))
include a μ
lemma call [Fintype A] [DecidableEq A] : PhysicalSum G M.team x n true S d L ( ApplyM P (Swirl.Near.Stripped M.team) M u ) (X.finite u L d S M n x):= by
    unfold finite; simp_rw [X.evaluates ev u L d a μ]; exact X.at_parameters u M L d x a μ S
end Dictionary
end YM.FVA2.Change
