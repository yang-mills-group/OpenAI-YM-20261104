import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
/-!
# Uniform big-O envelope helper for HorizonFork logarithmic power budgeting

For G4--G8: topology of the budget is just the `radius` heading; exponent independent
of positions through its clearance, phases, and other length parameters. Keep a common predicate
for several such price derivations; export the application without this terminology.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Fork
open Function Filter
open scoped BigOperators Classical
variable {α Z F : Type*} {φ : Filter α} {B:α→Z→Prop} {L W W' : α → Z → ℝ}

section
variable [Norm F]
/-- poly-in-L budget with positive weight-factor W; in the exercises, log budget (on both radii).
No positive powers of (1/r) hidden. -/
def Sold (φ : Filter α) (B:α→Z→Prop) (L W : α → Z → ℝ) (f : α → Z → F) : Prop :=
    ∃ k:ℕ, ∃ b:ℝ, 0 ≤ b ∧ ∀ᶠ a in φ, ∀ z:Z, B a z → ‖f a z‖ ≤ b*L a z^k*W a z
end

def Safe (φ : Filter α) (B:α→Z→Prop) (L W : α → Z → ℝ) : Prop :=
    ∀ᶠ a in φ, ∀ z, B a z → 1 ≤ L a z ∧ 0 ≤ W a z

lemma Safe.joint {w:α→Z→ℝ} (hw:Safe φ B L W) (hw':∀ᶠ a in φ,∀ z,B a z→ 0 ≤ w a z) : Safe φ B L w :=
  (hw.and hw').mono (fun _ h z he => ⟨(h.1 z he).1,h.2 z he⟩)

namespace Sold
variable [NormedAddCommGroup F] {f g : α → Z → F} (hw:Safe φ B L W)

lemma zero : Sold φ B L W (fun _ _=>(0:F)) :=
  ⟨0,0,le_rfl, Eventually.of_forall (fun _ _ _ => by simp)⟩
lemma transfer {F' :Type*} [Norm F'] {g : α → Z → F'} (H:Sold φ B L W f) {c:ℝ} (hn:0≤c)
    (hh:∀ᶠ a in φ, ∀ z:Z, B a z → ‖g a z‖ ≤ c*‖f a z‖) : Sold φ B L W g := by
  obtain ⟨k,b,hb,h⟩:= H; refine ⟨k,c*b,mul_nonneg hn hb, (hh.and h).mono ?_⟩
  intro a h z he; exact (h.1 z he).trans ((mul_le_mul_of_nonneg_left (h.2 z he) hn).trans_eq (by ring))
lemma price {F' :Type*} [Norm F'] {g : α → Z → F'} (H:Sold φ B L W f)
    (hh:∀ᶠ a in φ, ∀ z:Z, B a z → ‖g a z‖ ≤ ‖f a z‖) : Sold φ B L W g :=
  H.transfer zero_le_one (by simpa only [one_mul] using hh)
lemma congr (H:Sold φ B L W f) (hfg : ∀ a z, f a z=g a z) : Sold φ B L W g :=
  H.price (Eventually.of_forall fun _ _ _=> by rw [hfg])
lemma bounded {c:ℝ}(hc:0 ≤ c)(h:∀ᶠ a in φ, ∀ z:Z, B a z → ‖f a z‖ ≤ c*W a z) : Sold φ B L W f :=
  ⟨0,c,hc,by simpa using h⟩
lemma closed (u:F) : Sold φ B L (fun _ _=>1) (fun _ _=>u) := bounded (norm_nonneg u)
  (Eventually.of_forall fun a z _=> by rw [mul_one])
lemma more {w : α→Z→ℝ} (H:Sold φ B L W f)(hL:∀ᶠ a in φ,∀ z,B a z→0≤L a z)
    (hw:∀ᶠ a in φ,∀ z,B a z→ W a z ≤ w a z) : Sold φ B L w f := by
  obtain ⟨k,b,hb,h⟩:=H; refine ⟨k,b,hb,?_⟩
  filter_upwards [h,hL,hw] with a h hL hw z hz; exact (h z hz).trans (mul_le_mul_of_nonneg_left (hw z hz)
    (mul_nonneg hb (pow_nonneg (hL z hz) _)))
include hw in
lemma buy (H:Sold φ B L W f) : ∀ᶠ k:ℕ in atTop, ∀ᶠ b:ℝ in atTop, ∀ᶠ a in φ,
    ∀ z:Z, B a z → ‖f a z‖ ≤ b*L a z^k*W a z := by
  obtain ⟨k,b,hb,H⟩:= H
  filter_upwards [eventually_ge_atTop k] with j hj; filter_upwards [eventually_ge_atTop b] with c hc
  filter_upwards [hw,H] with a ha h z he; obtain ⟨hl,hw⟩:=ha z he; refine (h z he).trans ?_; exact mul_le_mul_of_nonneg_right
    (mul_le_mul hc (pow_le_pow_right₀ hl hj) (by positivity) (hb.trans hc)) hw
include hw in
lemma add (H:Sold φ B L W f)(H':Sold φ B L W g) : Sold φ B L W (fun a z=> f a z+g a z):= by
  obtain ⟨k,h,h'⟩:= ((H.buy hw).and (H'.buy hw)).exists
  obtain ⟨b,⟨hQ,hP⟩,hb⟩:= ((h.and h').and (eventually_ge_atTop 0)).exists
  refine ⟨k,b+b, add_nonneg hb hb,(hQ.and hP).mono ?_⟩
  intro a h z he; exact (norm_add_le ..).trans ((add_le_add (h.1 z he) (h.2 z he)).trans_eq (by ring))
lemma neg (H:Sold φ B L W f): Sold φ B L W (fun a z=> -(f a z)):=
  H.price (Eventually.of_forall fun _ _ _=> (norm_neg _).le)
include hw in
lemma sub (H:Sold φ B L W f)(H':Sold φ B L W g) : Sold φ B L W (fun a z=> f a z-g a z):=
  (H.add hw H'.neg).congr (fun _ _=> (sub_eq_add_neg ..).symm)
include hw in
lemma sum {i:Type*} {x:Finset i} {F':i→α→Z→F} (h:∀ i∈x, Sold φ B L W (F' i)):
    Sold φ B L W (fun a z=> ∑ i∈x, F' i a z):= by
  induction x using Finset.induction_on with
  | empty=>simpa using (zero (B:=B) (L:=L) (W:=W) (φ:=φ) (F:=F))
  | @insert i s hi ih=>
    exact ((h i (Finset.mem_insert_self ..)).add hw (ih fun j hj=> h j (Finset.mem_insert_of_mem hj))).congr
      (fun _ _=> by rw [Finset.sum_insert hi])
lemma smul [NormedSpace ℂ F]{A:α→ Z→ℂ} (hw:Safe φ B L W)
    (H:Sold φ B L W f)(H':Sold φ B L W' A): Sold φ B L (fun a z=>W' a z*W a z) (fun a z=> A a z • f a z):=by
  obtain ⟨k,b,hb,h⟩:=H; obtain ⟨j,c,hc,h'⟩:=H'; refine ⟨k+j,b*c,mul_nonneg hb hc,?_⟩
  filter_upwards [hw,h,h'] with a hQ h h' z hz
  obtain ⟨hl,hw⟩:= hQ z hz; rw [norm_smul]; exact (mul_le_mul
    (h' z hz) (h z hz) (norm_nonneg _) ((norm_nonneg _).trans (h' z hz))).trans_eq (by rw [pow_add]; ring)
lemma mul {f g:α→Z→ℂ}(hw:Safe φ B L W) (H : Sold φ B L W f)(H':Sold φ B L W' g):
    Sold φ B L (fun a z=> W' a z*W a z) (fun a z=> g a z*f a z):= H.smul hw H'
lemma rename {α' Z' : Type*}{φ' : Filter α'} {A:α'→Z'→Prop}
    (H:Sold φ B L W f){p:α'→α}(h:Tendsto p φ' φ){y:α'→ Z'→Z} (h':∀ᶠ a in φ',∀ z,A a z→ B (p a) (y a z)) :
    Sold φ' A (fun a z=> L (p a) (y a z)) (fun a z=> W (p a) (y a z)) (fun a z=> f (p a) (y a z)) := by
  obtain ⟨k,b,hb,q⟩:=H; exact ⟨k,b,hb,((h.eventually q).and h').mono (fun a hx z he=> hx.1 (y a z) (hx.2 z he))⟩
end Sold

section stencil
variable {I : Type*}[Fintype I]{V:I→Type*}[∀ i, NormedAddCommGroup (V i)]
    [∀ i, NormedSpace ℂ (V i)] [∀ i, FiniteDimensional ℂ (V i)]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
abbrev directions (V:I→Type*) [∀ i, NormedAddCommGroup (V i)]
    [∀ i, NormedSpace ℂ (V i)] := (i:I) → Fin (Module.finrank ℂ (V i))
def pose (v:directions V) (i:I) := Module.finBasis ℂ (V i) (v i)
lemma extend_box (L: ℝ) (hL : 0 ≤ L) : ∃ C:ℝ, 0 ≤ C ∧
    ∀ (M : MultilinearMap ℂ V F) (b:ℝ), 0 ≤ b → (∀ i:directions V, ‖M (pose i)‖ ≤ b) →
      ∀ v : (i:I)→V i, (∀ i, ‖v i‖ ≤ L) → ‖M v‖ ≤ C*b := by
  let J i := Fin (Module.finrank ℂ (V i)); let F' i := Module.finBasis ℂ (V i)
  let c i (j:J i) := ((F' i).coord j).toContinuousLinearMap
  refine ⟨∑h:directions V, ∏ i, (‖c i (h i)‖*L), Finset.sum_nonneg
    (fun i _=> Finset.prod_nonneg (fun j _=> by positivity)), fun M b hb h u hu=> ?_⟩
  have he : u = fun i=>∑ j:J i, c i j (u i) • F' i j :=funext fun i=> ((F' i).sum_repr _).symm
  let f (h:directions V):=(∏ i,c i (h i) (u i)) • M (pose h)
  have hf : M u = ∑ i,f i := by
    rw [he,M.map_sum]; exact Finset.sum_congr rfl (fun j _=> M.map_smul_univ ..)
  rw [hf,Finset.sum_mul]; apply le_trans (norm_sum_le ..) (Finset.sum_le_sum fun i _=>?_)
  unfold f; rw [norm_smul,norm_prod]; gcongr
  exact ((c _ _).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hu _) (norm_nonneg _))
  exact h i

-- all directions simultaneous (no changing B when evaluating a moved/programmed label)
lemma Sold.wallet {A:α→Z→ MultilinearMap ℂ V F} (H:∀ u, Sold φ B L W (fun a z=> A a z u))
    (hw:Safe φ B L W) (D:ℝ)(hD:0≤D):
    ∀ᶠ k:ℕ in atTop, ∀ᶠ b:ℝ in atTop,∀ᶠ a in φ, ∀ z, B a z → ∀ u:(i:I)→V i,
      (∀ i,‖u i‖≤D) → ‖A a z u‖ ≤ b*L a z^k*W a z := by
  obtain ⟨C,hC,H'⟩:= extend_box (F:=F) (V:=V) D hD
  filter_upwards [eventually_all.mpr (fun i:directions V=> (H (pose i)).buy hw)] with k hk
  obtain ⟨c,hc,Hc⟩:= ((eventually_ge_atTop 0).and (eventually_all.mpr hk)).exists
  filter_upwards [eventually_ge_atTop (C*c)] with b hb
  filter_upwards [hw,eventually_all.mpr Hc] with a ha h z hz u hu
  obtain ⟨hl,hw⟩:= ha z hz; refine (H' (A a z) (c*L a z^k*W a z) (by positivity) (fun i=>h i z hz) u hu).trans ?_
  rw [← mul_assoc C, ← mul_assoc C]; gcongr
lemma Sold.present {A:α→Z→ MultilinearMap ℂ V F} (H:∀ u, Sold φ B L W (fun a z=> A a z u))
    (hw:Safe φ B L W){g:α→Z→(i:I)→V i}{C:ℝ} (hC:0 ≤ C)(hg:∀ᶠ a in φ,∀ z, B a z → ∀ i,‖g a z i‖ ≤ C):
    Sold φ B L W (fun a z=> A a z (g a z)):=by
  obtain ⟨k,h⟩:= (Sold.wallet H hw C hC).exists
  obtain ⟨b,hb,Hb⟩:= ((eventually_ge_atTop 0).and h).exists
  exact ⟨k,b,hb,(Hb.and hg).mono (fun a h z he=> h.1 z he (g a z) (h.2 z he))⟩

variable {J:Type*}[Fintype J]{V':J→Type*}[∀ i, NormedAddCommGroup (V' i)]
    [∀ i, NormedSpace ℂ (V' i)] [∀ i, FiniteDimensional ℂ (V' i)]
lemma Sold.both {A:α→Z→ MultilinearMap ℂ V (MultilinearMap ℂ V' F)} (hw:Safe φ B L W)
   (hA : ∀ u v, Sold φ B L W (fun a z=> A a z u v)) (D:ℝ) (hD:0 ≤ D): ∃ k:ℕ, ∃ b:ℝ, 0 ≤ b ∧
    ∀ᶠ a in φ, ∀ z,B a z→ ∀ (u : (i:I)→V i) (v:(j:J)→V' j), (∀ i,‖u i‖≤ D) → (∀ i,‖v i‖ ≤ D) →
      ‖A a z u v‖ ≤ b*L a z^k*W a z := by
  obtain ⟨k,h⟩:=(eventually_all.mpr fun i:directions V=>Sold.wallet (A:=fun a z=> A a z (pose i)) (hA (pose i)) hw D hD).exists
  obtain ⟨b,hb,H⟩:=((eventually_ge_atTop 0).and (eventually_all.mpr h)).exists
  obtain ⟨C,hC,H'⟩:= extend_box (F:=F) (V:=V) D hD
  refine ⟨k,C*b, mul_nonneg hC hb,?_⟩
  filter_upwards [hw,eventually_all.mpr H] with a ha h z hz u v hu hv
  obtain ⟨hl,hw⟩:= ha z hz
  let X : MultilinearMap ℂ V' F →ₗ[ℂ] F := ⟨⟨fun q=>q v, fun _ _=>rfl⟩, fun _ _ => rfl⟩
  let M := X.compMultilinearMap (A a z)
  exact (H' M (b*L a z^k*W a z) (by positivity) (fun i=> h i z hz v hv) u hu).trans_eq (by ring)
end stencil
end YM.Integration.GradedFar.Fork
