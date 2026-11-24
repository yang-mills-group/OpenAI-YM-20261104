import YM.Integration.WilsonMeasuredCompanionFace

/-! A hard summand from either Wilson host changes one occupied physical
entry. The two resulting galleries share all ordinary peers and quiet keys. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceOwner
open Function Finset Lattice Wilson RG Labels Source Marker QuadraticLocal QuadraticLocal.Earn Ac
open WilsonMeasuredCoefficientTransport WilsonPhysicalMarkedDefect.RegularProjection WilsonOriginalDepositedHard
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {V T I : Type} [Fintype V] [DecidableEq V]
    {J : Census V} {o : V → Site n} {W : Rep G n} {d : ℕ} {F : Frame G d}
    {κ M k C : ℝ} {Y : Hol G}

theorem original (v : V) (h : Coefficient F n) (fit : h.Format (o v) Y W) (pay : h.remBound (o v) W κ M)
    (rent : Hard.Rent W.activities.forced W.activities.K W.p W.p.supportExponent k)
    (E : Lamps T I G W.p o J) (w : V → ℝ) (positive : ∀ j, 0 < w j)
    (salaries : E.Paid w W.p.B W.p.supportExponent C) (x : T) (s : J.Mode) (S : SectionData F) :
    let old : Hard T W.p W.activities.forced W.activities.K o J := Hard.rent rent
    let added := joined old v h fit (fun _ => (1:ℂ))
    let L₀ : Gallery T I o W J := ⟨E,old⟩
    let L₁ : Gallery T I o W J := ⟨E,added⟩
    L₀.Pays w W.p.supportExponent C k ∧ L₁.Pays w W.p.supportExponent C (k+w v*(κ*M)) ∧
    (∀ U, account h W U*WilsonMeasuredCompanionFace.peers E v s x U =
      (L₁.density x U).part s-(L₀.density x U).part s) ∧
    ∀ U, account h W U ≠ 0 → ∃i, h.forced i U≠0 ∧ o v∈(W.activities.forced i).support ∧
      ∃z,z∈(W.activities.forced i).inventory ∧ z∈flags W.p.threshold U := by
  have booked := WilsonMeasuredCompanionFace.fund rent v h fit (fun _ => (1:ℂ)) E w positive
    (fun _ => by simp) pay salaries
  have recorded := WilsonMeasuredOnlyHard.original h W W rfl rfl rfl S Y (o v) κ M fit pay
  refine ⟨booked.1,booked.2,?_,recorded.2.2.2⟩
  intro U
  have eq := WilsonMeasuredCompanionFace.on_field rent v h fit (fun _ => (1:ℂ)) E S w positive
    (fun _ => by simp) pay x s U
  rw [recorded.2.2.1 U] at eq
  simp only [one_mul,add_mul] at eq
  linear_combination eq
end YM.Integration.WilsonMeasuredPublicEntranceOwner
end
