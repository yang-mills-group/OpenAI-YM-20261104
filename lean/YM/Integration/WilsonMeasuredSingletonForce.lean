import YM.Integration.WilsonCenteredSingletonMass
import YM.Integration.WilsonCenteredFiledAtoms

/-! A fired hard singleton on the original operands is a native forced coefficient.
The rooted receipt is taken at its actual mark site. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredSingletonForce
open Function Finset Lattice Wilson RG Source Labels Marker QuadraticLocal Ac MeasureTheory
open Extra.Histories Push.Local Overlay
open scoped Classical BigOperators
variable {G:Gauge} {n:Side} {V X:Type} [DecidableEq V] {J:Census V}
    {P:Rep G n} {o:V → Site n} (H:Hard X P.p P.activities.forced P.activities.K o J)
    (x:X) (v:V) {d:ℕ} {F:Frame G d}

def row : Coefficient F n :=
  {Extra.Histories.primary (o v) 0 with forced:=fun i U=>(H.hard x i U).part (J.fire v)}

theorem format (Y:Hol G) : (row (F:=F) H x v).Format (o v) Y P := by
  have base:=(primary_format (o:=o v) (R:=P) (H:=Y) (0 : F.Coeff))
  refine ⟨base.smooth,base.origin,base.identity_null,base.projects,?_,?_,?_,?_,?_⟩
  · intro i U live
    exact H.charged x i U (fun z=>live (by change (H.hard x i U).part (J.fire v)=0;rw [z];rfl))
  · intro i live
    by_contra miss
    apply live
    funext U
    by_contra nonzero
    exact miss ((H.locality x i).carry U (J.fire v) nonzero v (mem_singleton_self v))
  · intro i g U
    exact congrArg (fun p : Poly J=>p.part (J.fire v)) ((H.locality x i).gauge g U)
  · intro i U W ha hf
    exact congrArg (fun p : Poly J=>p.part (J.fire v)) ((H.locality x i).reads U W ha hf)
  · intro i
    exact (Poly.part_cont _).measurable.comp (H.locality x i).borel

/-- The supplier may bill all owners. Only the original owners carrying this site
can contribute to the native global mass of the one-source row. -/
theorem paid {M κ:ℝ} (positive:0<κ) (mass:0≤M) (fee:ℕ→ℝ)
    (cap:∀ i U,‖(H.hard x i U).part (J.fire v)‖≤fee i)
    (hit:Hit (fun i=>(P.activities.forced i).support) P.p.B fee P.p.supportExponent (κ*M)) :
    (row (F:=F) H x v).remBound (o v) P κ M := by
  let e:=fun i=>if o v∈(P.activities.forced i).support then fee i else 0
  have due : SumBudget (fun i=>P.p.mass (P.activities.forced i).support (e i)) (κ*M) :=by
    convert hit (o v) using 1
    funext i
    by_cases atSite:o v∈(P.activities.forced i).support <;>
      simp [BudgetPoint.mass,e,atSite,mul_comm]
  refine ⟨0,M,le_rfl,mass,(zero_add M).le,positive,⟨fun _=>0,budget0 _ _,fun _=>(regular0 P.p _ (o v)).2⟩,e,due,?_⟩
  intro i
  by_cases atSite:o v∈(P.activities.forced i).support
  · have nonneg : 0≤fee i := (norm_nonneg _).trans (cap i 1)
    simpa [e,atSite,row] using And.intro nonneg (cap i)
  · have z:∀U,(H.hard x i U).part (J.fire v)=0 :=by
      intro U
      by_contra live
      exact atSite ((H.locality x i).carry U (J.fire v) live v (mem_singleton_self v))
    simp [e,atSite,row,z]

/-- Starting from the whole original hard wallet, restore one marker radius
and the original hard divisor once. The regular and primary coordinates vanish. -/
theorem restored (w:V→ℝ) (hw:∀j,0<w j) {κ M:ℝ} (positive:0<κ) (mass:0≤M)
    (wallet:H.Paid w P.p.B P.p.supportExponent (κ*M)) :
    (row (F:=F) H x v).remBound (o v) P κ ((w v)⁻¹*M) :=by
  obtain ⟨e,nn,_,caps,paid⟩:=WilsonCenteredHardWallet.original H w hw (J.fire v) v (mem_singleton_self _) wallet
  have pos:0≤(w v)⁻¹*M :=mul_nonneg (inv_nonneg.mpr (hw v).le) mass
  refine ⟨0,_,le_rfl,pos,(zero_add _).le,positive,⟨fun _=>0,budget0 _ _,fun _=>(regular0 P.p _ (o v)).2⟩,
    e,?_,fun i=>⟨nn i,caps i x⟩⟩
  simpa only [BudgetPoint.mass,Poly.toll,Census.fire,prod_singleton,mul_left_comm] using paid

theorem density (S:SectionData F) (U:Config G n)
    (summable:Summable (Fusion.Attached.packet P.activities P.p (H.hard x) U)) :
    (row (F:=F) H x v).density (o v) S P U =
      (Real.exp (P.exponent U):ℂ)*(WilsonCenteredAbsoluteHard.gas H x U).part (J.fire v) := by
  have paid:HasSum (fun B=>(row (F:=F) H x v).marked P B U)
      ((WilsonCenteredAbsoluteHard.gas H x U).part (J.fire v)) :=by
    have sum:HasSum (fun B=>(Fusion.Attached.packet P.activities P.p (H.hard x) U B).part (J.fire v))
        ((WilsonCenteredAbsoluteHard.gas H x U).part (J.fire v)):=(Poly.get (J.fire v)).hasSum summable.hasSum
    apply sum.congr_fun
    intro B
    by_cases ok:P.activities.admissible P.p U B <;>
      simp [Fusion.Attached.packet,Coefficient.marked,ok,Multi.first_of_prod,H.quiet,row]
  have head : (row (F:=F) H x v).exponentialEntry (o v) S P U=0 :=by
    simp [row,Extra.Histories.primary,Coefficient.exponentialEntry,Coefficient.maskedTerm,masked,SectionData.places,SectionData.evaluate]
  simp only [Coefficient.density,head,mul_zero,zero_add,paid.tsum_eq]

end YM.Integration.WilsonMeasuredSingletonForce
