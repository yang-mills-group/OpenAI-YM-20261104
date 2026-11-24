import YM.Integration.WilsonFullFaceSignedInterpolation
import YM.Integration.WilsonCapturedPrimarySoftMount

/-! Separate the old regular error in the ordinary exponential at load three.
The nominal occurrences, the true masks, and the quiet gas are identical at
the four interpolation nodes. An old bill is recovered once, outside every
node's finite capture cost. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonFullFaceSignedRegular
open Finset Lattice RG Wilson Marker QuadraticLocal Source Labels Extra.Histories Push.Local Planned.GuardedAtom
open WilsonCenteredFiledAtoms WilsonFullFaceSignedInterpolation
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {V X ι ν : Type} [DecidableEq V] [Fintype V] {R : Census V}
    {o : V→Site n} {P : Rep G n} {d : ℕ} {F : Frame G d}

def factor (e : ℝ) : ℝ := ∑ j : Fin 4, ‖coins (e:ℂ) j‖

def fee (p : BudgetPoint) (Z : Support n) (w : V→ℝ) (C e : ℝ) (rad : ℕ)
    (S : SectionData F) (Y : Hol G) (μ v κ : ℝ) (s : R.Mode) :=
  e * (factor e * WilsonCapturedPrimarySoftMount.fare p Z w (C+3) rad S Y μ v κ s)

theorem original [Countable ι] [Countable ν] (L : Lamps X ι G P.p o R) (B : Lamps X ν G P.p o R)
    (x : X) (s : R.Mode) (load : s.val.card≤3)
    (y : Site n) (Z : Support n) (hold : y∈Z) (landing : ∀j∈s.val,o j∈Z)
    (rad : ℕ) (near : ∀j∈s.val,separation (o j) y≤rad) (w : V→ℝ) (hw : ∀v,0<w v)
    {C e : ℝ} (pos : 0<e) (model : L.Paid w P.p.B (P.p.supportExponent+2) C)
    (debt : B.Paid w P.p.B (P.p.supportExponent+2) e)
    {σ E Λ δ κ v μ : ℝ} (K : Guard.Keeper P.p P.activities) (law : P.Lawful σ E Λ δ v)
    (div : 0<κ) (hv : 0≤v) (room : hitWidth P.p*v≤1)
    (S : SectionData F) (Y : Hol G) (reader : Readable Y S P.p n μ) :
    Store P S Y y κ (fee P.p Z w C e rad S Y μ v κ s)
      (fun U=>(P.eval U:ℂ)*((Poly.pass ((L.join B).log x U)).part s-(Poly.pass (L.log x U)).part s)) :=by
  let z := (e:ℂ)
  let node (j:Fin 4) := L.join (scale B ((j.val:ℂ)/z))
  let bill := WilsonCapturedPrimarySoftMount.fare P.p Z w (C+3) rad S Y μ v κ s
  let val (j:Fin 4) (U:Config G n) := (P.eval U:ℂ)*(Poly.pass ((node j).log x U)).part s
  have width : 0≤P.p.supportExponent+2 := by linarith only [P.p.exponent_pos]
  have nz : z≠0 := by dsimp only [z];exact_mod_cast pos.ne'
  have normZ : ‖z‖=e := by simp [z,Real.norm_eq_abs,abs_of_pos pos]
  have bounded (j:Fin 4) : (node j).Paid w P.p.B (P.p.supportExponent+2) (C+3) :=by
    have scaled:=WilsonFullFaceSignedInterpolation.paid B ((j.val:ℂ)/z) w debt
    have price : ‖(j.val:ℂ)/z‖*e=(j.val:ℝ) :=by rw [norm_div,Complex.norm_natCast,normZ];field_simp
    rw [price] at scaled
    have hj : (j.val:ℝ)≤3:=by exact_mod_cast (show j.val≤3 by omega)
    exact (node j).loan_monotone (Lamps.joinPaid model scaled) (add_le_add_right hj C)
  have pay (j:Fin 4) := WilsonCapturedPrimarySoftMount.original (node j) x s y Z hold landing rad near w hw (bounded j)
    K law div hv room S Y reader
  have arm (j:Fin 4) : Store P S Y y κ (‖coins z j‖*bill) (fun U=>coins z j*val j U) :=
    painted S Y y _ (pay j)
  obtain ⟨r,fit,charge,pub⟩:=WilsonFullFaceSignedHard.collect univ S Y y div law _ _
    (fun j (_:j∈(univ:Finset (Fin 4)))=>arm j)
  let scaled:=stretch z r
  refine ⟨scaled,stretch_format z fit,?_,fun U=>?_⟩
  · have b:=stretch_rem z charge
    rw [normZ,←Finset.sum_mul] at b
    exact b
  · change (stretch z r).density y S P U=_
    rw [stretch_density,pub]
    have l:=model.sums width hw x U
    have b:=debt.sums width hw x U
    let tail:=z⁻¹ • B.log x U
    have off:tail.part R.quiet=0:=by rw [show tail=z⁻¹ • B.log x U from rfl,Marker.Poly.part_smul,B.quiet_of_hasSum x U b,mul_zero]
    have actual:(L.join B).log x U=L.log x U+z • tail:=by
      rw [Lamps.joinLog x U l b]
      simp [tail,smul_smul,nz]
    have nodes (j:Fin 4):(node j).log x U=L.log x U+(j.val:ℂ) • tail:=by
      unfold node
      rw [Lamps.joinLog x U l ((WilsonFullFaceSignedInterpolation.paid B ((j.val:ℂ)/z) w debt).sums width hw x U),
        reading]
      simp [tail,smul_smul,div_eq_mul_inv]
    let a:=L.log x U
    have eq:=table s load a tail z (L.quiet_of_hasSum x U l) off
    change z*(∑j,coins z j*((P.eval U:ℂ)*(Poly.pass ((node j).log x U)).part s))=_
    simp_rw [nodes]
    rw [actual,eq]
    have perm (j:Fin 4) : coins z j*((P.eval U:ℂ)*(Poly.pass (a+(j.val:ℂ) • tail)).part s)=
      (P.eval U:ℂ)*(coins z j*(Poly.pass (a+(j.val:ℂ) • tail)).part s):=by ring
    change z*(∑j,coins z j*((P.eval U:ℂ)*(Poly.pass (a+(j.val:ℂ) • tail)).part s))=_
    simp_rw [perm]
    rw [←Finset.mul_sum];ring

end YM.Integration.WilsonFullFaceSignedRegular
