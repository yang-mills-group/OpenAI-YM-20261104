import YM.Next.WARD_BIN.Haar
import YM.PertExtension.BareChart
import YM.PertExtension.OrbHaar

/-! # Paired-edge variation on the inversion regulator

An arbitrary positive edge, not only a free gauge-fixed chart variable -- this lets RG14 keep
actual force support. Every variation at `e` moves also `Orb.reflect e`; only even side, no
fixed edges. Gauge covariance under even gauge transformations. No omission of a measure
Jacobian in PT, we do this from stationary orbit Wilson integrals before gauge fixing.
-/
set_option autoImplicit false
noncomputable section

namespace YM.FormalOPE.RG10.InversionWard
open Gauge Lattice RG Wilson MeasureTheory Metric
open PertExtension PertExtension.Orb Function
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace

variable {G : Gauge} {n : Side} (hn : Even n.val) (b : Edge (Site n))

/-- Move in the physical orientation of `b`. Pure inversion partner at the other end is
multiplied FROM THE RIGHT by the inverse element. -/
def push (g : G.El) (U : Config G n) (k : Edge (Site n)) := if k=b then g*U k
  else if k=Orb.reflect b then U k * g⁻¹ else U k

@[simp] lemma push_same (g : G.El) (U : Config G n) : push b g U b = g*U b := by simp [push]

@[simp] lemma push_unit (U : Config G n) : push b 1 U = U := by funext x; simp [push]

include hn in
lemma push_mirror (U : Config G n) (g : G.El) : push b g U (Orb.reflect b) = U (Orb.reflect b) * g⁻¹ := by
  simp [push, no_fixed_edge hn b]

/-- Color derivative along this one parameter path. -/
def tilt (U : Config G n) (a : G.Color) := push b (G.lieExp a) U
@[simp] lemma home (U : Config G n) : tilt b U 0 = U := by simp [tilt]

lemma action (g h : G.El) (U : Config G n) : push b g (push b h U) = push b (g*h) U := by
  funext k; unfold push; split_ifs <;> group

@[fun_prop] lemma step_cont (g : G.El) : Continuous (push (G:=G) b g) := by
  apply continuous_pi; intro i; unfold push; split_ifs <;> fun_prop

lemma point_combine (U : Config G n) (a : G.Color) (s t : ℝ) :
    tilt b (tilt b U (s • a)) (t • a) = tilt b U ((t+s) • a) := by
  have h := WardBin.left_add a (1 : G.El) t s
  simp only [WardBin.left, mul_one] at h
  unfold tilt; rw [action, h]

/-- With even gauge transformations, the end of the mirror sees the *same* adjoint color acting
as the head of `b`. -/
def evenAt (t : Site n → G.El) := ∀ x, t (-x)=t x
lemma tilt_gauge (t : Site n → G.El) (h : evenAt t) (U : Config G n) (a : G.Color) :
    tilt b (gauge t U) (G.adjoint (t b.1) a) = gauge t (tilt b U a) := by
  have he : t ((Orb.reflect b).1 + step (Orb.reflect b).2)=t b.1 := by unfold Orb.reflect; simp only [sub_add_cancel]; exact h _
  funext k
  by_cases h₁:k=b
  · subst k; simp only [tilt, Lattice.gauge, push, if_true]; rw [← WardBin.expAdjoint]; group
  by_cases h₂:k=Orb.reflect b
  · subst k; unfold tilt push Lattice.gauge
    simp only [if_neg h₁, ↓reduceIte, he]
    rw [← WardBin.expAdjoint]; group
  simp [tilt, push, h₁, h₂, Lattice.gauge]

abbrev Antes (G : Gauge) (n : Side) := OEdge n → G.El

/-- On the integration variables prior to tree fixing. No measure comparison with `Wilson.prior`
is implicit here. -/
def matchEdge (g : G.El) (A : Antes G n) : Antes G n := fun i => if i = index b then
    if eR b = b then g * A i else A i * g⁻¹ else A i
lemma preserves (g : G.El) : MeasurePreserving (matchEdge b g)
    (Chart.physical G (OEdge n)) (Chart.physical G (OEdge n)) := by
  apply measurePreserving_pi (fun _ => G.probHaar) (fun _ => G.probHaar) (f:=fun i e => if i=index b
    then if eR b=b then g*e else e*g⁻¹ else e); intro i; split
  · split
    · exact measurePreserving_mul_left G.probHaar g
    exact measurePreserving_mul_right G.probHaar g⁻¹
  exact MeasurePreserving.id _

private lemma at_index (g : G.El) (A : Antes G n) : liftLinks (matchEdge b g A) b = g * liftLinks A b := by
  by_cases he:eR b = b <;> simp [liftLinks, matchEdge, he]

include hn in
theorem lift_pair (g : G.El) (A : Antes G n) : push b g (liftLinks A) = liftLinks (matchEdge b g A) := by
  funext i; by_cases hz:i=b
  · subst i; rw [push_same, at_index]
  by_cases hi:i=Orb.reflect b
  · subst i; rw [push_mirror hn, lift_flip hn, lift_flip hn, at_index, mul_inv_rev]
  unfold push; rw [if_neg hi, if_neg hz]
  have h : index i ≠ index b := by
    intro ht
    have hs : eR i = eR b := congr_arg (fun k : OEdge n => k.val) ht
    rcases eR_spec i with h|h <;> rcases eR_spec b with k|k <;> rw [h,k] at hs
    · exact hz hs
    · exact hi hs
    · exact hi (by rw [← hs, reflect_reflect])
    exact hz (by simpa using congr_arg Orb.reflect hs)
  simp [liftLinks,matchEdge,h]

@[fun_prop] lemma liftlinks_cont : Continuous (liftLinks (K:=G.El) (n:=n)) := Orb.lift_cont G
end YM.FormalOPE.RG10.InversionWard
