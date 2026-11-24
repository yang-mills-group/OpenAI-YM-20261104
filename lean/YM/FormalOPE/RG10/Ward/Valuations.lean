import YM.FormalOPE.RG10.Ward.KeepCorrection

/-! Pole clearing precondition. This is only a supply for the basic `qneq` geometry (finite
bare stencil vectors). It doesn't prove the lift from chosen **all** nonlinear field quotient
null coordinates, nor joint rank. Provides a local constructor: `Counts` a sufficient way
of clearing, e.g. for vectors made by unscaled products of curvature factors before correcting
with sums of lower-order rows. Minimal-EOM-class examples. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.InversionWard
open Gauge Lattice RG Wilson MeasureTheory Metric Finset
open PertExtension PertExtension.Orb Function Filter InversionTop PowerSeries
open YM.PertExtension.Series YM.PertExtension.Series.Radial YM.PertExtension.Series.Tested
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {n : Side} (hn : Even n.val) {b : Edge (Site n)}
    {f g : Config G n → ℝ} {d e i j : ℕ}

-- simpler with pointwise `Bill` eval on representative
private abbrev smoothR (f : Config G n → ℝ) := f ∘ representative

/-- One order cost only; no target/shape conditions here. Cost on the full unpaired or paired
field as actually read on the same representative. -/
def weightFloor (i : ℕ) (f : Config G n → ℝ) := RadialOrder i (smoothR f)
namespace weightFloor
lemma baseline (h : Proxy f) : weightFloor 0 f := fun u => (directions (f:=smoothR f) (h.germ.contDiffAt) u).bounded
lemma initial (h : Proxy f) (he : f 1 = 0) : weightFloor 1 f :=
  zero_first h.germ.contDiffAt (by unfold smoothR; simp [he])
lemma lowered (h : weightFloor d f) (hv : e ≤ d) : weightFloor e f := fun x => bill_ge (h x) hv
lemma pair (h : weightFloor d f) (k : weightFloor e g) : weightFloor (d+e) (f*g) :=
  fun u => bill_mul (h u) (k u)
lemma append (h : weightFloor d f) (k : weightFloor d g) : weightFloor d (f+g) :=
  fun u => bill_add (h u) (k u)
lemma neg (h : weightFloor d f) : weightFloor d (-f) := fun u => bill_neg (h u)
lemma unpaid {I : Type*} (s : Finset I) (f : I → Config G n → ℝ) (h : ∀ i∈s, weightFloor d (f i)) :
    weightFloor d (∑ i∈s, f i) := by
  intro x
  have he := bill_sum s (fun i t => smoothR (f i) (t • x)) (fun i hi => h i hi x)
  convert! he using 1; funext u; simp only [smoothR, Function.comp_apply, Finset.sum_apply]
lemma wipes (h : weightFloor d f) (hp : Proxy f) (hv : i < d) : row i (pencil f) = 0 := by
  funext x
  change PowerSeries.coeff i (InversionTop.lift (smoothR f) x)=0
  change row i (InversionTop.lift _) _ = _
  rw [row_lift, jets_vanish (hp.germ.contDiffAt) h hv]; rfl
end weightFloor

local notation "D" => WardBin.dirs

/-- Include derivative valuation so divergence after projection is meaningful. Used componentwise
on X. No Ward or EOM assumed. -/
structure Counts (b : Edge (Site n)) (d : ℕ) (f : Config G n → ℝ) : Prop where
  proxy : Proxy f
  floor : weightFloor d f
  leaf c : weightFloor (d-1) (fun U => vary b f U c)
namespace Counts
lemma atom (h : Proxy f) : Counts b 0 f := ⟨h, weightFloor.baseline h, fun c => weightFloor.baseline (h.reply b c)⟩
lemma pays_one (h : Proxy f) (he : f 1 = 0) : Counts b 1 f :=
  ⟨h,weightFloor.initial h he, fun c => weightFloor.baseline (h.reply b c)⟩

lemma product (h : Counts b d f) (hf : Counts b e g) : Counts b (d+e) (f*g) := by
  refine ⟨h.proxy.mul hf.proxy,h.floor.pair hf.floor,fun c=>?_⟩
  rw [show (fun U => vary b (f*g) U c)=_ from funext (fun U => leibniz b h.proxy hf.proxy U (fun _=>c))];
  exact ((weightFloor.lowered (h.leaf c |>.pair hf.floor) (by omega)).append
    (weightFloor.lowered (h.floor.pair (hf.leaf c)) (by omega)))
end Counts

namespace Direction

variable {Z : Config G n → G.Color}

include hn in
/-- Sufficient order valuation. For any cleared pole convention, the *same* equationMark
and contact formulas apply. -/
theorem pays (h : Direction b Z)
    (hp : ∀ j : G.ColorIndex, Counts b d (fun U => Inner.inner ℝ (D G j) (Z U))) : Approved b Z d := by
  let J := fun i (U:Config G n) => Inner.inner ℝ (D G i) (Z U)
  let E1 := fun i (U : Config G n) => J i U * vary b invoice U (D G i)
  let E2 := fun i (U : Config G n) => vary b (J i) U (D G i)
  let f := InversionWard.effort b Z
  let g := InversionWard.fallout b Z
  have hm : retained (1:Config G n) := by funext i; rw [all_reversed]; simp
  have h1 (i:G.ColorIndex) : weightFloor 1 fun U=>vary b invoice (G:=G) U (D G i) := weightFloor.initial
    (invoice_proxy (G:=G) (n:=n) |>.reply b (D G i)) (by rw [twiceAt hn b 1 hm, force_unit, inner_zero_right])
  have h₁ : f= ∑ i, E1 i := by
    funext; rw [Finset.sum_apply]; exact coupled_components ..
  have h₂ : g= ∑ i, E2 i := by
    funext; rw [Finset.sum_apply]; exact fallout_deriv b h.acts _
  have hf : weightFloor (d+1) f := by rw [h₁]; apply weightFloor.unpaid; intro i _; exact (hp i).floor.pair (h1 i)
  have hg : weightFloor (d-1) g := by rw [h₂]; apply weightFloor.unpaid; intro i _; exact (hp i).leaf (D G i)
  intro k hk
  unfold unweighted; rw [show row k (pencil f - delay 2 (pencil g)) = _ from
    funext (fun x => (show row k _ x = row k (pencil f) x-row k (delay 2 (pencil g)) x from map_sub _ _ _)),
    hf.wipes (h.acts.effort b) (by omega), row_delay]
  by_cases h' : 2≤k
  · rw [if_pos h', hg.wipes (h.acts.fallout b) (by omega)]; exact sub_self _
  rw [if_neg h']; exact sub_self _
end Direction

variable (G n b)

include hn in
/-- Nontrivial scope test: use WardBin Euler itself AS the local vector in `qneq`, all color
indices, pull it with factor `1/g`. -/
theorem supplied_force : Direction b (fun U : Config G n => WardBin.euler U b) ∧
    Approved b (fun U : Config G n => WardBin.euler U b) 1 := by
  have H : Direction b (fun U : Config G n => WardBin.euler U b) := ⟨proxy_force _, carrying_force _⟩
  refine ⟨H,H.pays hn (fun i => Counts.pays_one ?_ ?_)⟩
  · exact H.acts.after _ (innerSL ℝ (D G i)).contDiff
  rw [force_unit, inner_zero_right]
end YM.FormalOPE.RG10.InversionWard
