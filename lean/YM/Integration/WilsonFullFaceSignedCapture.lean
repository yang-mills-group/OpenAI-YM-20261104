import YM.Integration.WilsonFullFaceSignedRegular
import YM.Integration.WilsonFullFaceSignedMasks
import YM.Integration.WilsonThermometerWeightedCapture
import YM.Integration.WilsonCenteredDetectorUnit

/-! Subtract the full ordinary nominal on the real, closed Wilson
representation. The three contributions are the occupied forced gas, the
old regular variation and the failed union masks. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonFullFaceSignedCapture
open Finset Lattice RG Wilson Marker Multi QuadraticLocal Source Labels Extra.Histories Push.Local Planned.GuardedAtom
open WilsonCenteredFiledAtoms WilsonRootedKioskOccupiedSlip WilsonCenteredCompleteGallery
open WilsonThermometerCenteredAlgebra
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {X ι ν : Type} [Countable ι] [Countable ν]
    {o : Fin 3→Site n} {P : Rep G n} {d : ℕ} {F : Frame G d}
local notation "J" => Stock.census (Fin 3)

def fare (p : BudgetPoint) (S : SectionData F) (Y : Hol G) (Z : Support n) (w ws : Fin 3→ℝ)
    (s : (J).Mode) (rad : ℕ) (C e D wage E v κ μ : ℝ) :=
  WilsonFullFaceSignedHard.fee p Z ws s E wage v κ +
      WilsonFullFaceSignedRegular.fee p Z w C e rad S Y μ v κ s +
      ∑q∈shards (J) s,WilsonFullFaceSignedMasks.charge p Z w C D v κ q

theorem face (L : Lamps X ι G P.p o J) (B : Lamps X ν G P.p o J)
    (H : Hard X P.p P.activities.forced P.activities.K o J) (x : X) (s : (J).Mode)
    (w ws : Fin 3→ℝ) (hw : ∀j,0<w j) (hs : ∀j,0<ws j) {C e D wage E v σ c Λ δ κ μ : ℝ}
    (pos : 0<e) (model : L.Paid w P.p.B (P.p.supportExponent+2) C)
    (debt : B.Paid w P.p.B (P.p.supportExponent+2) e) (gross : Gross L w P.p.B (P.p.supportExponent+2) D)
    (soft : (L.join B).Paid ws P.p.B (P.p.supportExponent+2) E) (hard : H.Paid ws P.p.B P.p.supportExponent wage)
    (K : Guard.Keeper P.p P.activities) (law : P.Lawful σ c Λ δ v)
    (div : 0<κ) (hv : 0≤v) (room : hitWidth P.p*v≤1)
    (S : SectionData F) (Y : Hol G) (reader : Readable Y S P.p n μ)
    (y : Site n) (Z : Support n) (center : y∈Z) (resident : ∀j∈s.val,o j∈Z)
    (rad : ℕ) (near : ∀j∈s.val,separation (o j) y≤rad) :
    let A : Gallery X (ι⊕ν) o P J := ⟨L.join B,H⟩
    Store P S Y y κ (fare P.p S Y Z w ws s rad C e D wage E v κ μ)
      (fun U=>(A.density x U).part s-(P.eval U:ℂ)*(Poly.pass (bare L x U)).part s) :=by
  intro A
  have force:=WilsonFullFaceSignedHard.original A x s S Y Z y center resident K ws hs law hv room div soft hard
  have regular:=WilsonFullFaceSignedRegular.original L B x s (by simpa using card_le_univ s.val)
    y Z center resident rad near w hw pos model debt K law div hv room S Y reader
  have masks:=WilsonFullFaceSignedMasks.original L x s y Z center resident rad near w hw model gross
    K law div hv room S Y
  obtain ⟨r,fit,bill,field⟩:=WilsonCenteredFiledAtoms.add law div (WilsonCenteredFiledAtoms.add law div force regular) masks
  refine ⟨r,fit,bill,fun U=>?_⟩
  rw [field];simp only [Pi.add_apply]
  change ((A.density x U).part s-(P.eval U:ℂ)*(Poly.pass ((L.join B).log x U)).part s+
    (P.eval U:ℂ)*((Poly.pass ((L.join B).log x U)).part s-(Poly.pass (L.log x U)).part s))+
    (P.eval U:ℂ)*((Poly.pass (L.log x U)).part s-(Poly.pass (bare L x U)).part s)=_
  ring

theorem pooled (S : SectionData F) (Y : Hol G) (y : Site n) {κ σ C Λ δ v μ : ℝ}
    (div : 0<κ) (law : P.Lawful σ C Λ δ v) (reader : Readable Y S P.p n μ) (Q : Poly J)
    (M L : Config G n→Poly J) (fee : (J).Mode→ℝ)
    (faces : ∀s:(J).Mode, Store P S Y y κ (fee s) (fun U=>(M U).part s-(P.eval U:ℂ)*(L U).part s)) :
    ∃ h : Coefficient F n,h.Format y Y P ∧ h.remBound y P κ (∑s,‖weight Q s‖*fee s) ∧
      (∀U,h.density y S P U=(total (M U) Q).part full -(P.eval U:ℂ)*(total (L U) Q).part full) ∧
      ∀ a : Probe G d, a.2.val=0 → runProbe F a h.x =
        (P.eval (1:Config G n):ℂ)⁻¹*((total (M 1) Q).part full-(P.eval (1:Config G n):ℂ)*(total (L 1) Q).part full) :=by
  obtain ⟨h,fmt,bill,pub⟩:=WilsonFullFaceSignedHard.collect (univ:Finset (J).Mode) S Y y div law _ _
    (fun s _=>WilsonFullFaceSignedInterpolation.painted S Y y (weight Q s) (faces s))
  have field (U:Config G n) : h.density y S P U=(total (M U) Q).part full-(P.eval U:ℂ)*(total (L U) Q).part full :=by
    rw [pub,affine,affine,mul_sum,←sum_sub_distrib]
    apply sum_congr rfl
    intro s _
    ring
  exact ⟨h,fmt,bill,field,fun a flat=>(WilsonCenteredDetectorUnit.flatProbe h fmt reader.sound a flat).trans
    (congrArg (fun z=>(P.eval (1:Config G n):ℂ)⁻¹*z) (field 1))⟩

end YM.Integration.WilsonFullFaceSignedCapture
