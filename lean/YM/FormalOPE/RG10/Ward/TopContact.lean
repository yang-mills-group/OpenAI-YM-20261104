import YM.FormalOPE.RG10.Ward.Eom
import YM.FormalOPE.RG10.Ward.Forces
import YM.FormalOPE.RG10.FiniteTop

/-! # Lift contact and derivative payments to formal-Wilson coefficients

The derivative of another insertion is a *new* mark. No ghost composites/off-shell propagators
part of this regulator; Ward tests carried on the gauge-invariant physical subspace. These are
necessary **exact** tests on every Stamp/Simplex sector before looking for any normalized contact
composites or taking moving/multi-cluster limits. `replyCoeff` always computed independently by
`into/diag`, not by the Ward identity.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.InversionWard
open Gauge Lattice RG Wilson MeasureTheory Metric Finset
open PertExtension PertExtension.Orb Function Filter InversionTop PowerSeries
open YM.PertExtension.Series YM.PertExtension.Series.Radial YM.PertExtension.Series.Tested
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {n : Side} (hn : Even n.val) (b : Edge (Site n))
    {f : Config G n → ℝ} {Z : Config G n → G.Color}

/-- Vector field and needed analytic/gauge coherence for the genuine Haar equation. Additional
geometry (e.g. supports) and vanishing powers required on some uses, not needed for the
pre-division identities. -/
structure Direction (b : Edge (Site n)) (Z : Config G n → G.Color) : Prop where
  acts : Proxy Z
  real : carrying b Z
namespace Direction
variable {b}
protected lemma effort (h : Direction b Z) : PreTest (InversionWard.effort b Z) :=
    (Proxy.effort b h.acts).active (respects_coupled b h.real invoice_proxy invoice_even)
protected lemma fallout (h : Direction b Z) : PreTest (InversionWard.fallout b Z) :=
    (Proxy.fallout b h.acts).active (respects_fallout b h.acts h.real)
protected lemma contact (h : Direction b Z) {f : Config G n → ℝ} (hf : Proxy f) (hg : respects f) :
    PreTest (coupled b Z f) := (Proxy.couple b h.acts hf).active (respects_coupled b h.real hf hg)
end Direction

lemma unique_wilson {u v : ℝ→ℝ} {A B : ℕ→ℝ} (h : u =ᶠ[YM.PertExtension.Series.Tested.germ] v) (hA : Aspiration u A) (hB : Aspiration v B) : A=B := by
  refine Aspiration.unique hA fun i => ?_
  obtain ⟨c,hc,he⟩:= hB i
  refine ⟨c,hc,?_⟩; filter_upwards [he,h] with t ht hq; simp only [Pi.sub_apply] at ht ⊢; rw [← hq] at ht; exact ht -- simp

def replyCoeff (f : Config G n → ℝ) := into (PowerSeries.mk (diag (restrictedO f)))

lemma expectation_witness (h : PreTest f) :
    replyCoeff f = (feed hn).step (vertices G n) (raw (restrictedO f)) := (tree_agreement hn h.curved).symm

private lemma square_pow : Aspiration (fun x : ℝ => x^2) (fun i => if i=2 then 1 else 0) := by
  simpa using! Aspiration.single (1:ℝ) 2

include hn in
theorem reply_relation (h : Direction b Z) (hf : Proxy f) (hp : respects f) :
    replyCoeff (effort b Z * f) = X^2 * (replyCoeff (fallout b Z * f) + replyCoeff (coupled b Z f)) := by
  let a := effort b Z * f; let v := fallout b Z * f; let w := coupled b Z f
  let R := tray G
  have hx p (h : PreTest (G:=G) (n:=n) p) : Aspiration (preExpectation p) (diag (restrictedO p)) :=
    before_tree_formula hn (traySpec G) h
  have hv := (hx v (Uses.pre_mul h.fallout (hf.active hp))).add (hx w (h.contact hf hp))
  let y : ℕ→ℝ := fun i => if i=2 then 1 else 0
  have he : diag (restrictedO a) = conv y (diag (restrictedO v)+diag (restrictedO w)) :=
    unique_wilson (hA := hx a (Uses.pre_mul h.effort (hf.active hp)))
      (eventually_pos.mono (fun x hx => orbit_IBP hn b h.acts hx.ne' hf)) (square_pow.prod hv)
  have hs : PowerSeries.mk y=(PowerSeries.X (R:=ℝ))^2 := by apply PowerSeries.ext fun n=> ?_;rw [coeff_mk,coeff_X_pow]
  have hz (k j : ℕ→ℝ) : PowerSeries.mk (k+j)=PowerSeries.mk k+PowerSeries.mk j := by apply PowerSeries.ext fun n => ?_; simp
  have hw : PowerSeries.mk (diag (restrictedO a)) = X^2 * (PowerSeries.mk (diag (restrictedO v))+PowerSeries.mk (diag (restrictedO w))) := by
    apply PowerSeries.ext; intro i; rw [← hz,← hs, coeff_mk]; exact congr_fun he i
  unfold replyCoeff; rw [show effort b Z * f = a from rfl, hw, map_mul,map_add,map_pow, show into X=X from map_X _]

include hn in
/-- Raw series additivity on gauge invariant inputs. -/
theorem reply_sum {I : Type*} (s : Finset I) (A : I→Config G n→ℝ) (h : ∀ i∈s, PreTest (A i))
    (hy : ∀ i∈s, Proxy (A i)) :
    replyCoeff (∑ i∈s,A i) = ∑ i∈s, replyCoeff (A i) := by
  have hr : respects (∑ i∈s,A i) := by
    intro t ht U; simp only [Finset.sum_apply]; exact Finset.sum_congr rfl (fun i hi => (h i hi).gauge t ht U)
  let D := fun (f : Config G n→ℝ) => diag (restrictedO f)
  have hx f (h : PreTest f) : Aspiration (preExpectation (G:=G) (n:=n) f) (D f) := before_tree_formula hn (traySpec G) h
  have he : D (∑ i∈s, A i)=∑ i∈s, D (A i) := unique_wilson (.of_eq (expectation_sum s A hy))
    (hx _ ((Proxy.sum s hy).active hr)) (Aspiration.sum s _ _ (fun i hi => hx _ (h i hi)))
  apply PowerSeries.ext; intro i
  simp only [replyCoeff, map_sum,into_coeff, coeff_mk]; change (((D (∑ i∈s,A i) i:ℝ):ℂ))=_
  rw [he, Finset.sum_apply, Complex.ofReal_sum]
include hn in
lemma reply_nil : replyCoeff (0 : Config G n → ℝ) = 0 := by
  rw [expectation_witness hn (f:=0) ⟨fun _ _ _ => rfl, ⟨continuous_const, contDiffAt_const⟩, continuous_const⟩]
  rw [show raw (restrictedO (0 : Config G n → ℝ))=0 from ?_];
  · simp only [FlatFeed.step, mul_zero]; rw [show (feed hn (G:=G)).average 0=0 from ?_, zero_mul]
    apply PowerSeries.ext; intro k
    rw [FlatFeed.average_coeff, show row k 0 = (0: Unit × Dir G n → ℂ) from ?_, FlatFeed.mean_zero,map_zero]; funext x; simp [row]
  funext x; apply PowerSeries.ext; intro k
  have hx : raw (restrictedO (0 : Config G n → ℝ)) = InversionTop.lift 0:=rfl
  simp only [hx, Pi.zero_apply, InversionTop.lift, into_coeff, coeff_mk]
  simp [jet]

end YM.FormalOPE.RG10.InversionWard
