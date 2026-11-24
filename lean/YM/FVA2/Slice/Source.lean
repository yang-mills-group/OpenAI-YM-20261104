import YM.FVA2.Slice.Reduction
/-!
# Evaluate the supplied MS finite Wick predicate for these precise body tickets.

Still here in bare variable. Additional supplied literal identifications with dockets (marks)
and clock sense are necessary to apply `LPT_to_MS`. This is an exact finite-regulator supplier,
on the stipulated inserted data, not an application with those hypotheses omitted. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Slice
open Function Set Filter Finset MeasureTheory Lattice
open MS MS.Plane MS.Cylinder Lab MS.Cylinder.Taylor MS.Book Convolve Program MS.Tone MS.City MS.Orbit
open MS.Koszul MS.Landau MS.Native MS.Native.Chart MS.Native.Wilsonian MS.Orbit.Cog MS.Swirl MS.Swirl.Near
open MS.Puff MS.Puff.Engine MS.Puff.Mom
open PertExtension.GaussianScore
open FormalOPE.RG10 FormalOPE.RG10.MultiGauge MultiGauge.Splice
open Wick Gem Fermion Boson
open Formal (overlay)
open PowerSeries (coeff)
open scoped BigOperators Matrix Topology ContDiff InnerProductSpace
variable {G : Gauge} {n : Side} {A J : Type}

/-- Complexify the regulator Taylor variables; same coefficients. -/
def record (s:PowerSeries ℝ)(n:ℕ) : ℂ := (coeff n s:ℝ)
local infixl:70 " ● " => Actors.core Trunk
lemma stack_mul (s t:PowerSeries ℝ) : record (s*t)=record s ● record t := by
  funext x; rw [record,PowerSeries.coeff_mul,Complex.ofReal_sum]; exact Finset.sum_congr rfl (fun _ _=> Complex.ofReal_mul ..)

namespace Axes
variable [Fintype A] [DA:DecidableEq A] [Fintype J] [DecidableEq J]
variable (a : Axes G n A J)
local notation "L" => Transverse G n
local notation "P" => Permit (Transverse G n)
local notation "b" => sector (A:=A) (J:=J)
local notation "q" => σbranch (G:=G) (n:=n)
local notation "I" => Wick.Index A J
local notation "Q" => bosonMatrix (gaussian G n) a.X
local notation "T" => FixedMode G n
local notation "K" => Master G n true
local notation "F" => before G n
local notation "B" => ( (1/2:ℂ) • totalCov Q J : Matrix I I ℂ )
local notation "S" => exp0 σbranch F
local notation "μₜ" => ℶV K
local notation "Z" => a.relative
local notation "Y" => Boson.bills (J:=J) a.X
local notation "δ" => Wick.pull a.R
local notation "ϱ" => promote δ
local infixl:70 " ⋆ " => product b
local infixl:70 " ★ " => overlay b
local infixl:70 " ⋆₀ " => overlay q

variable (μ : Measure (Transverse G n))[Measure.IsAddHaarMeasure μ]
local notation "Ψ" => input (gaussian G n) μ
variable (x:Formal.Table (FixedMode G n)) (t:Ticket (Transverse G n))
variable (hx:x∈Formal.OK σbranch) (ht: promote (Wick.pull a.R) x= Boson.bills a.X t) -- instance J infer?
include hx ht
theorem reading : μₜ (S ⋆₀ x)= record (Ψ (Z*t)):= by
  let WW:= S ⋆₀ x; have hp:WW∈Formal.OK q:= Formal.overlay_ok (Formal.exponent_ok before_ok) hx;
  have hv: promote δ WW=(promote δ S) ★ Y t := by
    rw [← ht]; funext i; simp only [WW,Formal.coeff_prod,promised,map_sum]; refine Finset.sum_congr rfl fun k _=> Wick.pull_product a.tieR _ _
  funext i; obtain ⟨hf,hm⟩:= fee_spec (hp i (Set.mem_univ _)); change View K (WW i)= _; rw [a.wick_ms (WW i) hm];
  have hV : δ (WW i)∈Mini I:= by obtain ⟨p,hp⟩:= hm; exact minH (Wick.pull_limit a.R hp)
  rw [total_w Q (Matrix.IsSymm.ext (fun i j=> Wick.wick_sym _ _ j i)) (Wick.pull_symm a.tieR hf) hV,
    show Wg A J (δ (WW i))=Y (Z*t) i from congr_fun (Eq.trans (congr_arg (promote (Wg A J)) hv) (a.wash t)) i]
  exact read_body ..

omit hx ht
lemma reads_unit : μₜ S=record (Ψ Z) := by
  let A₀ := actor q; have Hu : Formal.tab (coin (1:ℂ))∈Formal.OK q := Formal.tab_good («S»:=FeeP q) (Swirl.feeUnit («p»:=q)); obtain he:= a.reading μ _ 1 Hu (by rw [Formal.promote_tab, Wick.pull_coin, tab_one]; rfl); rw [show S ⋆₀ (Formal.tab (coin 1))= S from (PermV q).identityR _, mul_one] at he; exact he

/-- The real linear-gauge coefficients on all these joint open tickets are on a common
vacuum denominator ($Ψ Z$). -/
def sumBody (a:Axes G n A J)(μ : Measure (Transverse G n))[Measure.IsAddHaarMeasure μ] (x: Ticket (Transverse G n)) := enjoy (gaussian G n) μ x a.relative
omit [Fintype A] DA in
lemma sum_cost : Ψ (Z*t)= Ψ Z * a.sumBody μ t:= by unfold sumBody enjoy; rw [mul_left_comm, PowerSeries.mul_inv_cancel _ (by rw [underBudget (gaussian G n) μ a.priced_zero]; exact one_ne_zero), mul_one]
include hx ht
lemma End_sumBody : Endμ K σbranch F x (record (a.sumBody μ t)) := by unfold Endμ; rw [a.reading μ _ _ hx ht,a.reads_unit μ, sum_cost a μ t]; exact stack_mul ..
end Axes
end YM.FVA2.Slice
