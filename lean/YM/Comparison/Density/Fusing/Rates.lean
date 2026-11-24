import YM.Comparison.Density.Payload.Evaluating
import YM.Push.LOCAL_SPLITTING.Funding
/-!
# Flag-only log entries

Prelude to actual re-expression. Neither term in a difference may
be evaluated unaware of its mask; these are the permitted LOG
changes and their exact corrections. Real vacuum exponent through
same scalar, nonempty marker components. Quantitative hit on
COMPLETE supports with polynomial/test weight included outside
sup. If the argument used additional addresses or derivative
stencils, they must be registered in the support before charging
and merging, including the flags actually tested.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Density.Fusing
open Testing Markers Registers Marker RG Lattice Function Finset MeasureTheory Filter Wilson
open Pert.Attach Push.AbsoluteSums
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical

variable {V : Type} [DecidableEq V] {R : Census V} {n : Side} {G : Gauge}
variable {X : V → Type} [∀ v, NormedAddCommGroup (X v)] [∀ v, NormedSpace ℂ (X v)]
variable {O : Readers V X n}

structure Leftovers (R : Census V) (X : V→Type) (G : Gauge) (n : Side) where
  real : Pert.Attach.Corrections G n
  marked : Cross X → Supply R G n

variable {B : BudgetPoint} {L : Leftovers R X G n} {w : V→ ℝ}

structure Placed (B : BudgetPoint) (O : Readers V X n) (L : Leftovers R X G n) : Prop where
  nonempty i : (L.real.region i).Nonempty
  real : Prepared B.threshold L.real
  marked x : BoundTo (L.marked x) L.real.region B O.source
  empty x i U : (L.marked x i U).part R.quiet=0
  masked x i U : Healthy B.threshold (L.real.region i) U → L.marked x i U=0
  tickets i U : Catalogue O.locus (L.real.region i) (fun x=> L.marked x i U)

def Compensated (B : BudgetPoint) (O : Readers V X n) (L : Leftovers R X G n) (w : V→ℝ) (e b : ℝ):=
    ∃ d : ℕ→ℝ, ∃ D : ℕ→Poly R, (∀ i U, |L.real.value i U| ≤ d i) ∧ (∀ i, Carries O.source.uses (L.real.region i) (D i)) ∧
      (∀ i, (D i).part R.quiet=0) ∧
      (∀ x, UnitPage x → ∀ i U, Over (L.marked x i U) (D i)) ∧
      Ac.Hit L.real.region B.B (fun i=> d i+Poly.price w (D i)) (B.supportExponent+e) b

def scenery (L : Leftovers R X G n) : Pert.Attach.Corrections G n := ⟨L.real.region,fun j U=> Real.exp (L.real.value j U)-1⟩
variable (hw : ∀ i,0<w i) (h : Placed B O L)
include h

lemma permitted : Prepared B.threshold (scenery L):= by
  have he := h.real
  refine ⟨fun i U hi=> by simp [scenery,he.flag i U hi], fun i k U=> by unfold scenery; simp only [he.sym i k U],
    fun i=> ((Real.continuous_exp.measurable.comp (he.meas i)).sub measurable_const), fun i U X ht hX=> by dsimp only [scenery]; rw [he.deps i U X ht hX],fun s b=>?_⟩
  obtain ⟨f⟩:=he.move s b
  exact ⟨f.perm,f.region,fun i U=> by dsimp only [scenery]; rw [f.value]⟩

include hw
variable {e b : ℝ} (hg : 0≤ e) (hc : Compensated B O L w e b)
include hg hc

omit hw hc in
private lemma priced_L {f : ℕ→ℝ} (hp : ∀ i,0≤ f i)
    (H : Ac.Hit L.real.region B.B f (B.supportExponent+e) b) : Summable f := by
  apply Activities.summable_charge h.nonempty hp (p:=B) (w:=b); intro x
  apply budget_mono (H x)
  · intro i; split; exact mul_nonneg (Real.exp_pos _).le (hp _); exact le_rfl
  intro i; split_ifs
  · unfold BudgetPoint.mass; rw [mul_comm (f i)]
    have hz:=hp i; gcongr; linarith
  exact le_rfl

lemma real_sums (U) : Summable fun i=> L.real.value i U:= by
  obtain ⟨f,k,hf,-,-,-,H⟩:=hc
  have he := priced_L h hg (fun i=> add_nonneg ((abs_nonneg _).trans (hf i U)) (Poly.nonnegative hw _)) H
  refine Summable.of_norm (he.of_nonneg_of_le (fun i=>norm_nonneg _) fun i=> ?_)
  exact (hf i U).trans (le_add_of_nonneg_right (Poly.nonnegative hw _))
variable [Fintype V]

lemma poly_sums (x : Cross X) (U) : Summable fun i=> L.marked x i U:= by
  obtain ⟨d,c,hF,H,hq,hO,Ht⟩:=hc
  have he : Deposits B w O.source L.real.region L.marked e b:= by
    refine ⟨c,hO,H,fun i=>budget_mono (Ht i) (fun j=> ?_) (fun j=> ?_)⟩
    · split; exact mul_nonneg (Poly.nonnegative hw _) (Real.exp_pos _).le; exact le_rfl
    split_ifs
    · exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left ((abs_nonneg _).trans (hF _ 1))) (Real.exp_pos _).le
    exact le_rfl
  obtain ⟨f,hf,ha,hZ⟩:= he.pay hw hg h.nonempty h.tickets x
  exact (Poly.budgeted hw ha fun i=> hZ i U).1

omit hw h hg hc

def spins (L : Leftovers R X G n) (x : Cross X) (i) (U) := companion (L.real.value i U) (L.marked x i U)
include h
lemma escort (x : Cross X) : Escort (spins L x) (scenery L) B O.source := by
  have he:= h.real; have ht := h.marked x
  refine ⟨⟨fun i=>by intro k U; rw [spins, ht.sym i k U, he.sym i k U]; rfl,fun i=>?_,
    fun i U V hh hX=> by rw [spins, ht.reads i U V hh hX, he.deps i U V hh hX]; rfl,
    fun i U=> Carries.companion _ (ht.bears i U)⟩, fun i U=> quiet_companion _ (h.empty x i U),fun i U hp=>?_⟩
  · exact (((embedded_cont.measurable.comp (Real.continuous_exp.measurable.comp (he.meas i))).mul (Poly.pass_cont.measurable.comp (ht.borel i))).sub measurable_const)
  rw [spins,he.flag _ U hp,h.masked x i U hp]
  unfold companion; rw [one_magnify,sub_self]

lemma spins_tickets (i U) : Catalogue O.locus ((scenery L).region i) (fun x=> spins L x i U) := Catalogue.friend _ (h.tickets i U)

include hw hc hg

lemma prices : Deposits B w O.source (scenery L).region (spins L) e (b*Real.exp b) := by
  obtain ⟨f,m,hf,hM,hv,hW,H⟩:=hc
  have hf' i:= show 0≤ f i from (abs_nonneg _).trans (hf i 1)
  let d i:= f i+Poly.price w (m i)
  have hd i : 0≤d i:= add_nonneg (hf' _) (Poly.nonnegative hw _)
  have hz i : d i ≤ b := by
    obtain ⟨x,hx⟩:= h.nonempty i; apply le_trans _ (budget_single (H x) i); rw [if_pos hx]
    exact le_mul_of_one_le_right (hd i) (Real.one_le_exp (mul_nonneg (add_nonneg B.exponent_pos.le hg) (by positivity)))
  let F i := companion (f i) (m i)
  refine ⟨F, fun x hx i U=> Over.companion (hf _ U) (hW x hx i U) (h.empty ..) (hv _), fun i=> Carries.companion _ (hM i), fun i=>?_⟩
  rw [mul_comm b]; apply budget_mono (budget_scale (Real.exp_pos _).le (H i))
  · intro j; split; exact mul_nonneg (Poly.nonnegative hw _) (Real.exp_pos _).le; exact le_rfl
  intro j; change (if i∈ L.real.region j then Poly.price w (F j)*_ else 0) ≤ _; split_ifs
  · rw [←mul_assoc]; refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    calc _ ≤ Real.exp (d j)-1 := companion_bound hw (hv _) (hf' _)
         _ ≤ d j*Real.exp (d j):= Push.Local.exp_gain ..
         _ ≤ Real.exp b*d j:= by rw [mul_comm]; exact mul_le_mul_of_nonneg_right (Real.exp_monotone (hz j)) (hd j)
  rw [mul_zero]
end YM.Comparison.Density.Fusing
