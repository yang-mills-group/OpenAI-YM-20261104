import YM.QuadraticLocal.Echo.Legible
/-!
# tail insurance
 Keep the real and PIT cuts on the exact same schedule. omitted = outside chosen globally
 Fin list (paid at full distance and flourish; long cut not assumed finitely supported), ALSO
 drop any of length > threshold by foregoing half the exponential. In application also omit
 all whose terms do not agree with the TRUE regulator location, exact zero on auxiliary if
 stamp fit and permits; conservative here. Quantified through supplying successor render.No
 finite-order compatibility/remainder on true torus inferred from dropping (keep semantic model
 leg lists and carry errors of the omitted terms).
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Echo
open Function Filter Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis Bid Planned.JetPort
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open AllOrder AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Haiku.Coat AllOrder.Fire PertExtension.Series Radial
open AllOrder.Laplace AllOrder.Laplace.SigmaP Response AllOrder.Ink AllOrder.Ink.Method AllOrder.Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration AllOrder.Catch AllOrder.Catch.Clock AllOrder.Floe AllOrder.Plateau
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {ι:Type*} {V:Type}[Fintype V][DecidableEq V]{G:Gauge} {k j e d Nℓ:ℕ} {a f σ b Z τ A:ℝ} {n:Side}
open Aperture Poetry Work.G05 Toggle Aux Aux.Name
open Spot Trace
namespace Minty
-- from funding spacecraft.B.Line
variable (p:V)(T:V→Site n)(R:Poetry.Roll G V)
local notation "Φ" => (R.leg)
local notation "Φ'"=> univ
local notation "μ" i:max=> Poetry.Lantern.money (Φ i) a
local notation "U"=> R.Ty
variable (h:R.Faith (univ:Finset V) p k a A)
variable (c:Finset R.Ty)(H:ℕ)(hp:b ≤ a) (hw:0< a)
local notation "β" i:max=> R.price b i
local notation "ν" i:max=> R.price a i
def crystal (R:Poetry.Roll G V)(c: Finset R.Ty)(b:ℝ)(i:R.Ty):= if i∉c then R.price b i else 0
local notation "ζ"=> (crystal R c)
local notation "ℓ"=> ((a-b):ℝ)
set_option quotPrecheck false
local notation "q!"=> Real.exp (-(a-b)*H)
def peck := c.filter (fun i=> (Φ i).length≤H ∧ Spot.Entails (Φ i) p T)
local notation "b₀"=> peck p T R c H
-- currency by length.Lost.There_C card support.Arbitrariness.c
include hp
lemma lengthRate (i:R.Ty)(he:H ≤ (Φ i).length): β i ≤ q!*ν i:=by
 let p:= (Φ i).length; let x:=(Φ i).atom.magnitude; unfold Roll.price Poetry.Lantern.money; rw [mul_left_comm]; refine mul_le_mul_of_nonneg_left ?_ (Texture.mag_nonneg _); rw [←Real.exp_add]; apply Real.exp_monotone; have he': (H:ℝ) ≤ ((Φ i).length:ℝ):= (by exact_mod_cast he); nlinarith [mul_le_mul_of_nonneg_left he' (sub_nonneg.mpr hp)]
lemma day (i:R.Ty): β i≤ν i:= by simpa using lengthRate (a:=a) R 0 hp i (Nat.zero_le _)
-- mint with ANY finset.c.
include h
lemma accord (hC: SumBudget (ζ a) f): SumBudget (Trace.rent p T R (peck p T R c H) b) (f+q!*A) := by
 let w:= q!; let s:= peck p T R c H; let z:= Trace.rent p T R s; let q:= R.price a; let g i:= w * q i; apply Local.sumBudget_mono (Local.sumBudget_add hC (Local.sumBudget_mul_left h.price (Real.exp_pos _).le)) _ _ le_rfl
 · intro i; unfold Trace.rent; split; · exact Lantern.fee_nn ..
   exact le_rfl
 · intro i; unfold Trace.rent; split; next hx=>
      obtain ⟨hu,hx'⟩:=hx; by_cases hT:i∈c; · exact (lengthRate R H hp i (by by_contra! hx; apply hu; exact Finset.mem_filter.mpr ⟨hT,hx.le,hx'⟩)).trans (le_add_of_nonneg_left (hC.1 _))
      exact ( (day R hp i).trans_eq (if_pos hT|>.symm : q i=crystal R c a i)).trans (le_add_of_nonneg_right (mul_nonneg (Real.exp_pos _).le (h.price.1 i))) -- if
   exact add_nonneg (hC.1 i) (mul_nonneg (Real.exp_pos _).le (h.price.1 i))
omit hp -- generic existence
lemma gets (hf:0 < f): ∀ᶠ c: Finset R.Ty in atTop, SumBudget (crystal R c a) f:=by
 let g:= R.price a; let A':=∑' i,g i; have h': Tendsto (fun w:Finset R.Ty=>∑ i∈w,g i) atTop (𝓝 A'):= h.price.2.1.hasSum
 filter_upwards [h'.eventually (lt_mem_nhds (show A'-f<A' from sub_lt_self A' hf))] with i hi; let g' := crystal R i a; have hz:g'= (i:Set R.Ty)ᶜ.indicator g:= by unfold g' crystal; ext1 x; by_cases h:x∈i; rw [if_neg (not_not.mpr h),(Set.indicator_of_notMem (show x∉(i:Set R.Ty)ᶜ from not_not.mpr h) g)]; rw [if_pos h,(Set.indicator_of_mem (show x∈(i:Set R.Ty)ᶜ from h) g)]
 rw [show crystal R i a=g' from rfl,hz]; refine ⟨Set.indicator_nonneg (fun i _=> h.price.1 i), h.price.2.1.indicator _,?_⟩; rw [← _root_.tsum_subtype]; apply le_of_lt;
 have he: (∑ x∈i,g x)+(∑' x:↑( (i:Set R.Ty)ᶜ),g ↑x)=A':= by
    rw [← Finset.sum_coe_sort,← tsum_fintype (L:=.unconditional _)]; exact h.price.2.1.tsum_subtype_add_tsum_subtype_compl (i:Set R.Ty)
 change A'-f< ∑ x∈i,g x at hi; change (∑' x:↑((i:Set R.Ty)ᶜ),g ↑x)<f; linarith only [he,hi]
omit h
end Minty
end YM.QuadraticLocal.Echo
