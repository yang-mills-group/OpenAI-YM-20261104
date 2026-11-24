import YM.Integration.WilsonFiniteGalleryWidth

/-! Qualitative full three-source income on the original finite Haar law. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonFiniteGalleryHaar
open MeasureTheory Filter Finset Lattice RG Wilson Marker Multi QuadraticLocal Ac Source Labels Extra.Histories
open Push.Local Planned.GuardedAtom WilsonCenteredFiledAtoms WilsonRootedKioskOccupiedSlip
open WilsonGeometricSignedCapture
open scoped Classical BigOperators
variable {G:Gauge} {n:Side} {P:Rep G n} {F:Frame G 0} {o:Fin 3→Site n}
local notation "J" => Stock.census (Fin 3)
variable {X I:Type} [Countable I]

theorem original (A : Gallery X I o P (J)) (x : X) (w : Fin 3 → ℝ) (hp : ∀ j, 0 < w j)
    (keeper : Guard.Keeper P.p P.activities) {σ C Λ δ v κ μ b e α : ℝ}
    (law : P.Lawful σ C Λ δ v) (div : 0 < κ) (hv : 0 ≤ v) (room : hitWidth P.p*v ≤ 1)
    (S : SectionData F) (Y : Hol G) (reader : Readable Y S P.p n μ)
    (regular : A.E.Paid w P.p.B α b) (hard : A.K.Paid w P.p.B P.p.supportExponent e) :
    Integrable (A.density x) (prior G n) := by
  obtain ⟨cap,capPos,soft⟩ := WilsonFiniteGalleryWidth.paid (b:=P.p.supportExponent+2) A.E hp regular
  let y : Site n := 0
  let Z : Support n := univ
  have atCenter : y∈Z := mem_univ _
  have resident (j:Fin 3) : o j∈Z := mem_univ _
  let rad := (univ : Finset (Fin 3)).sup (fun j => separation (o j) y)
  have near (j:Fin 3) : separation (o j) y ≤ rad := Finset.le_sup (f:=fun t=>separation (o t) y) (mem_univ j)
  let E:=WilsonOriginalScalarGallery.empty P o (J) X
  have paid:E.Paid w P.p.B (P.p.supportExponent+2) 0:=by
    refine ⟨fun i=>i.elim,fun i=>i.elim,fun i=>i.elim,fun t=>?_⟩
    exact ⟨fun i=>i.elim,(hasSum_fintype _).summable,by rw [tsum_empty]⟩
  have allFields:Gross E w P.p.B (P.p.supportExponent+2) 0:=by
    refine ⟨fun i=>i.elim,fun i=>i.elim,fun i=>i.elim,fun t=>?_⟩
    exact ⟨fun i=>i.elim,(hasSum_fintype _).summable,by rw [tsum_empty]⟩
  have joined:(E.join A.E).Paid w P.p.B (P.p.supportExponent+2) cap:=by
    simpa only [zero_add] using Lamps.joinPaid paid soft
  let AG:Gallery X (Empty⊕I) o P (J):=⟨E.join A.E,A.K⟩
  have bare0 (U:Config G n):bare E x U=0:=by simp only [WilsonRootedKioskOccupiedSlip.bare,tsum_empty]
  have actual (U:Config G n):AG.density x U=A.density x U:=by
    have h0:0 ≤ P.p.supportExponent+2:=by linarith only [P.p.exponent_pos]
    have logs:(E.join A.E).log x U=A.E.log x U:=by
      rw [Lamps.joinLog x U (paid.sums h0 hp x U) (soft.sums h0 hp x U)]
      simp only [Lamps.log,tsum_empty,zero_add]
    change _ • (Poly.pass ((E.join A.E).log x U)*A.gas x U)=_ • (Poly.pass (A.E.log x U)*A.gas x U)
    rw [logs]
  let fee (s:(J).Mode):=WilsonFullFaceSignedCapture.fare P.p S Y Z w w s rad 0 cap 0 e cap v κ μ
  have faces (s:(J).Mode):Store P S Y y κ (fee s)
      (fun U=>(A.density x U).part s-(P.eval U:ℂ)*(Poly.pass (0:Poly (J))).part s):=by
    have sold:=WilsonFullFaceSignedCapture.face E A.E A.K x s w w hp hp capPos paid soft allFields joined hard keeper
      law div hv room S Y reader y Z atCenter (fun j _=>resident j) rad (fun j _=>near j)
    change Store P S Y y κ (fee s) (fun U=>(AG.density x U).part s-(P.eval U:ℂ)*(Poly.pass (bare E x U)).part s) at sold
    simpa only [actual,bare0] using sold

  apply integrable_pi_iff.mpr
  intro s
  obtain ⟨q,fmt,charge,out⟩ := faces s
  have vacuum : Integrable (fun U : Config G n => (P.eval U:ℂ)) (prior G n) :=
    Complex.ofRealCLM.integrable_comp ((P.envelope law).integrable _)
  have eqn : (fun U=>(A.density x U).part s) =
      (fun U=>q.density y S P U+(P.eval U:ℂ)*(Poly.pass (0:Poly (J))).part s) := by
    funext U
    rw [out,sub_add_cancel]
  rw [show (fun U=>(A.density x U) s)=(fun U=>(A.density x U).part s) from rfl,eqn]
  exact ((q.envelope S law charge fmt).integrableC _).add (vacuum.mul_const _)
end YM.Integration.WilsonFiniteGalleryHaar
end
