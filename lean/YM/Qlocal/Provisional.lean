import YM.Qlocal.Parse

/-!
Entering rough primitives with differential gauges. This one separates actual
radii (in Proto) from arbitrary slotted λ. Funding uses `ρ` relative to the
bill of the ENTIRE marker mode. Inherited captions supplied separately. Can
 undo λ by any gains on pertinent finite products; doesn't ask positivity of
 final packet coefficients. Adapt this to the actual `.rap` costs of another
branch only after checking all hypotheses.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Provisional
open Marker Lattice Wilson RG MeasureTheory Extra.Trajectories Push Push.AbsoluteSums
open Overlay RG3.Press RG3.Held RG3.Script.Picnic RG3.Forms Progress.DirectedRecipe
open Function Set Filter Finset Integration Integration.LocalComparison Integration.RiderTastePresentation
open Next.Foundations PhysicalNext PhysicalNext.Repeat Mallow Blush
open scoped Topology InnerProductSpace Classical ContDiff Matrix.Norms.Frobenius BigOperators YM.Qlocal.Payload
open Merge Switch UniformPays Publishing Emissions Payload MergeProof Menu Accent Lotus
open RGComparison01.Pledge Footprint
variable {Ω ι J V M : Type} [DecidableEq V] {R:Census V} {G:Gauge}{n:Side}{P: RG.Rep G n}
    {X:Support n}{o:V→Site n}{s:V→Support n}
    {u w:V→ℝ}{c:R.Mode→ℝ}{k k' : ℕ}{a b d δ C A B θ ρ ξ:ℝ}

variable (r: V→ℝ) [Fintype ι] {Q:ι→Hat R P}
    {f:Side} (S:StepData f n)

lemma common (M:ι→Leaf P)(u v:ι→ℝ)(Z Z':ι→Poly R)(he:∀ i,(↑(u i):ℂ) • Z i=(↑(v i):ℂ) • Z' i)(U:Config G n):
    Photo.given (S:=S) M u R Z U= Photo.given (S:=S) M v R Z' U:=by
 unfold Photo.given; refine sum_congr rfl fun j _=> ?_; rw [Complex.ofReal_mul,Complex.ofReal_mul,mul_smul,mul_smul]; congr 1; rw [Complex.ofReal_prod,Complex.ofReal_prod];
 let A(q:ι→ℝ)(Z:ι→Poly R): (∏ i∈j.val,(↑(q i):ℂ)) • (∏ i∈j.val,Z i)=∏ i∈j.val,(↑(q i):ℂ) • Z i:= by simp_rw [← Poly.product_bead, Finset.prod_mul_distrib, map_prod]
 rw [A,A]; exact prod_congr rfl fun i _=> he i

variable {dcl:Set (ℕ ×ℕ)} {Y:Taste Ω o P R} {HE:RetainsDeclared dcl Y s}
    {H:Peak P o Y c a A B} {hΩ:Ω} (V': Fabric HE H hΩ) (h0:a=P.p.supportExponent) (hc:∀ i,0<c i) (hr:0<ρ)
    (hp: HasSlots P.p P.activities)
local notation "DK"=>deck R s

def radius (c:R.Mode→ℝ) (ρ:ℝ)(s:V→Support n)(i:deck R s):ℝ:=ρ*c (kind i)
def actual_t (c:R.Mode→ℝ)(ρ:ℝ)(s:V→Support n)(i: deck R s): ℂ:= valueH i / ↑(radius c ρ s i)
def marks (c:R.Mode→ℝ)(ρ:ℝ)(s:V→Support n)(i:deck R s):= Poly.send (kind i) (actual_t c ρ s i)
set_option quotPrecheck false
local notation "W'"=> ProfileH
local notation "H0"=> profileH hp V'
local notation "Z"=> marks c ρ s
local notation "R'"=> radius c ρ s
include hc hr
lemma price (i:deck R s):0<radius c ρ s i:= mul_pos hr (hc _)
include hp h0
lemma bench (x:Ω) : RGComparison01.Pledge.Bench (fun i=>(H0 x i).M) R' (ρ*(2*(A+B))):= by
 subst a; let e i:=(profileH hp V' x i|>.M); have he:∀ i:deck R s,(e i).crest.Nonempty := by
    intro i; apply (Finset.nonempty_iff_ne_empty.mpr);
    intro he; let A:= P.activities; cases ho:(e i).turn with
    | logKey z => have h': (A.reg z).site ∈ (e i).crest:=by unfold Leaf.crest; rw [ho]; exact (A.reg z).anchor
                  rw [he] at h'; exact Finset.notMem_empty _ h'
    | gasKey z=> have hh : (e i).crest = _:= (show (e i).crest= (P.activities.forced z).support from congr_arg (fun k:Wing=>k.support P) ho); exact ((hh.symm ▸ ((P.activities.forced z).inventory_ne.mono (P.activities.forced z).inventory_sup)) : (e i).crest.Nonempty).ne_empty he
 let o' i:=(he i).choose; refine ⟨o',fun i=>(he i).choose_spec,fun i=>(price hc hr i).le,fun i=> budget_mono (budget_scale hr.le (income hp V' x i)) (fun j=>?_) (fun j=>?_)⟩
 · split; exact mul_nonneg (mul_nonneg (price hc hr _|>.le) (Leaf.profit _)) (Real.exp_nonneg _); rfl
 split
 next hi=>
   rw [if_pos (show i∈_ from hi ▸ (show o' j∈ _ from (he j).choose_spec)), Palette.wages,radius]; dsimp only; rw [modesH]; apply le_of_eq; ring
 next=> exact (budget_scale hr.le (income hp V' x i)).1 _

variable [Fintype V] (hP:P.Lawful θ ξ b d δ)
include hP
lemma prologue (x:Ω) : Photo.given (S:=S) (fun i:deck R s=>(H0 x i).M) R' R Z=(Y.leaf x).contents.density:=by
 funext U; rw [← borrows h0 hc hp V' x U hP S (fun _=>1) (fun _=>zero_lt_one)]; unfold Expense; apply common; intro i; rw [purchase _ (fun _=>zero_lt_one)] -- implicit layout? `Fintype DK`
 unfold Menu.stamp marks; rw [sent,modesH, chargesH]; apply congr_arg; unfold actual_t; have hκ:= price hc hr i; field_simp [(Complex.ofReal_ne_zero.mpr hκ.ne')]
omit hP h0 hc hr [Fintype V] in
lemma authentic : Syntax (Z) s (fun i:deck R s=>(profileH hp V' hΩ i).M.crest) := Syntax.for_radii _ (signs hp V')
omit hP h0 hp [Fintype V] in
lemma specifics (i:deck R s): ‖actual_t c ρ s i‖ = (radius c ρ s i)⁻¹:=by
 unfold actual_t; rw [norm_div,Complex.norm_real,Real.norm_of_nonneg (price hc hr i|>.le), show ‖valueH i‖=1 from (by cases i<;> exact colour_norm _),one_div]

omit hP h0 hp [Fintype V] in
lemma renewed {D:R.Mode→ℝ}(he:0 ≤ C) (h :∀ U:Finset (deck R s),∀ v:Fits kind U,D (unionTag kind U v) ≤ C*∏ i∈U,radius c ρ s i):
    Brand (marks c ρ s) D C := by
 apply postage (q:=kind) _ he; intro U hv; simp_rw [specifics (c:=c) hc hr]; rw [prod_inv_distrib,← div_eq_mul_inv]; exact (div_le_iff₀ (prod_pos fun i _=>price hc hr _)).2 (h U hv)
end YM.Qlocal.Provisional
