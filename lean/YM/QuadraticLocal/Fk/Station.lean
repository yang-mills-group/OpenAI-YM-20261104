import YM.QuadraticLocal.Fk.Receipt
/-!
# Publication cover-approximation state for any ticket simultaneously with the pre-Run bank

May use for summing all the chosen stencil kernels in combination with the native
model's momentum probes, demonstrating FinPeriod ↔ Cover identity up to exponential
winding payments. No equality-at-fixed-torus assumed – that would be inappropriate for
these doubly-anchored paint kernels.

Target for repeated publication uses phase orders and arity.Paper tags chosen by Epoch
prior to passing through the Book. Invariant stencils after projection use a fixed marker
grid for the entire query. Thus `Kul(t)` here references nothing about the choice of
analytic winding cuts on the actual step. This certificate is needed even for kernels with
markers on far ends of the torus, many of which don't admit those same cuts.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Mentor
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll AllOrder
open Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration PriceCompiler
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G:Gauge}{V:Type}[Fintype V][DecidableEq V]
open AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV Pane ThroughLaunch
open Aero Kinetic.Port Laurent Bloch Further.PhysicalPeriodLimitF933 Shingle Macrame PhysicalNext
variable {X:Metals G} (D:RG.Supply.Rolls X.p)(R:Roots (G:=G) X.p.profile X.K X.p.kernel)(x y:ℕ) (Q:R.Tab D) (ψ:ℕ→ℕ) (K₀: Offices.Books R D Q ψ)
set_option quotPrecheck false
local notation "B" => X.K
local notation "A" => X.p.profile
local notation "p" => X.p.profile x
local notation "q" => X.p.profile y
local notation "K" => X.p.kernel
local notation "O"=> X.O
variable {k r i:ℕ}
open QuadraticLocal.Sunrise Aperture.Bunch
open Comparison.RG02
namespace Wharf
variable (V_ : Port.Cashpoint R D x y)
local notation "h₁" => V_.2.1
local notation "θ"=> V_.2.1.wants
local notation "κ"=> Burn.horizon V_.2.1.vac
local notation "I"=> Card D R x y θ κ
local notation "J₀"=> V_.2.2.1
local notation "J'"=> (J₀).val.loans
local notation "e₀"=> (J₀).val.angle
local notation "φ₀"=> (J₀).val.order
local notation "i'"=> V_.2.2.2.val
local notation "F"=> Epoch.data R D Q V_.1 V_.2.1
local notation "U"=> K₀.lore x y V_.1 V_.2.1 J₀
local notation "M"=> (Params R D ψ x y θ (J') (h₁).vac)
local notation "Δ"=> (Poetry.Agenda.poll R κ x)
-- as NE projection uses V_ param arguments, Prop quantifiers keep explicit `[local]` might get orphan variables rewrite
local notation "Ψ" a:max n:max=> (@Publication.reads G (Fin ((J₀).val.fst.val)) _ _ X D R x y θ (h₁).vac ψ J' F a i' n) -- check #print
local notation "𝓥"=> (V_.fst)
local notation "A0"=> (Fin ((J₀).val.fst.val))
local notation "δ"=> (Mural.sheet X.p D θ)
local notation "ν" n:max=> Ad G (δ) K n
-- price class at fixed stages. `wound`: uniform [CreditF]. Not state property includes positive δ for all heap.
def rate (d:ℕ)(B₀ paid:ℝ)(n:Side):ℝ:= (B₀*(1+|paid|)^d) * (n.val:ℝ)^d
def Wound (C₁:ℝ)(j:ℕ): Prop:= 0< Poetry.Agenda.poll R κ x ∧ ∀ a:M,∀ n:Side, Ad G (Mural.sheet X.p D θ) K n →
    Prices (Poetry.Agenda.guard (J') univ i') ((Wharf.rate j C₁ a.1.self.paid n)*dearth Δ n) ( (Ψ a n)-(Publication.report D R x y θ ψ J' e₀ F U a i' n) )
-- keep LeaseEarn observation.READ.
local notation "Kul" => ( U )
local notation "Υ"=> Wharf.Wound D R x y Q ψ K₀ V_
lemma obtains : ∃ b:ℝ, ∃ j:ℕ, 0≤ b ∧ Wound D R x y Q ψ K₀ V_ b j:= by
 haveI:= V_.2.1.head; let F' := Kul; let j:= F'.ticket
 obtain ⟨f,⟨g,hg,hΓ⟩,hσ,H⟩:= Publication.lease D R x y θ ψ J' e₀ F F' (Nat.le_of_lt_succ V_.2.2.2.prop);
 obtain ⟨b,hb,hY⟩:= hg
 refine ⟨b,j,hb,hσ,fun i n hn=>?_⟩; have hδ : 0≤dearth Δ n:=(Real.exp_pos _).le; have hCp : f i n*dearth Δ n ≤ Wharf.rate j b i.1.self.paid n * dearth Δ n:= mul_le_mul_of_nonneg_right ((hΓ i n).2.trans (mul_le_mul_of_nonneg_right (hY i|>.2) (by positivity))) hδ; exact ⟨(H i n hn).1.trans hCp, (H i n hn).2.1, fun x=> ((H i n hn).2.2 x).trans (mul_le_mul_of_nonneg_right hCp (by positivity))⟩
lemma lend {C C₁:ℝ}{j t:ℕ}(hp:Wound D R x y Q ψ K₀ V_ C j)(hC:0≤C)(h:C≤C₁)(hu:j≤t): Wound D R x y Q ψ K₀ V_ C₁ t := by
 refine ⟨hp.1,fun a n he=>?_⟩; let d:=dearth Δ n; let r:=rate j C a.1.self.paid n; have hr:a.1.self.paid ≤ |a.1.self.paid|:=le_abs_self _; have hb: r*d ≤ rate t C₁ a.1.self.paid n*d:= by
    have hz: (1:ℝ) ≤ n.val:= by exact_mod_cast n.property
    have hd:0 ≤ d:= (Real.exp_pos _).le; unfold r rate; exact mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul h (pow_le_pow_right₀ (le_add_of_nonneg_right (abs_nonneg _)) hu) (by positivity) (le_trans hC h)) (pow_le_pow_right₀ hz hu) (by positivity) (mul_nonneg (hC.trans h) (by positivity))) hd
 exact ⟨(hp.2 _ _ he).1.trans hb,(hp.2 _ _ he).2.1,fun x=> ((hp.2 a n he).2.2 x).trans (mul_le_mul_of_nonneg_right hb (by positivity))⟩
local notation "ω"=> Port.Cashpoint R D x y
lemma ready : ∃ (b:ℝ)(j:ℕ), 0<b ∧ ∀ V':Port.Cashpoint R D x y, Wound D R x y Q ψ K₀ V' b j:=by
 letI : Finite ω:=by unfold Port.Cashpoint; infer_instance
 letI:= Fintype.ofFinite (Port.Cashpoint R D x y)
 choose f g hf h using fun V_'=> Wharf.obtains D R x y Q ψ K₀ V_'
 refine ⟨1+∑ v:ω,f v, Finset.univ.sup g,add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun i _=> hf i)), fun i=>Wharf.lend D R x y Q ψ K₀ i (h i) (hf i) (?_) (Finset.le_sup (f:=g) (Finset.mem_univ _))⟩; exact (Finset.single_le_sum (f:=f) (fun i _=>hf i) (Finset.mem_univ i)).trans (le_add_of_nonneg_left zero_le_one)
abbrev upper := (ready D R x y Q ψ K₀).choose
def title := (ready D R x y Q ψ K₀).choose_spec.choose
lemma warranty : 0< Wharf.upper D R x y Q ψ K₀ ∧ Wound D R x y Q ψ K₀ V_ (Wharf.upper D R x y Q ψ K₀) (Wharf.title D R x y Q ψ K₀):= ⟨(ready D R x y Q ψ K₀).choose_spec.choose_spec.1,(ready D R x y Q ψ K₀).choose_spec.choose_spec.2 V_⟩
end Wharf
end YM.QuadraticLocal.Mentor
