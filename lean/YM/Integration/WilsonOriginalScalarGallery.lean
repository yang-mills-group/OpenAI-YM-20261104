import YM.QuadraticLocal.Startup.Arbor
import YM.MergeProof.Pitch

/-! The original finite vacuum at the date of a new registered source.
The complete scalar forced gas keeps its full physical support exponent. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalScalarGallery
open Function Finset Lattice RG Wilson Marker QuadraticLocal Ac
open Push.AbsoluteSums Fusion Fusion.Attached ConnectedActivityE6
open scoped Classical BigOperators
variable {G:Gauge} {n:Side} {V X :Type} [DecidableEq V] {Γ:Census V}
  {o:V→Site n} {P:Rep G n} {w:V→ℝ} {k:ℝ}

def empty (P:Rep G n) (o:V→Site n) (Γ:Census V) (X:Type) : Lamps X Empty G P.p o Γ :=
   ⟨fun i=>i.elim,fun i=>i.elim,fun i=>i.elim,fun i=>i.elim,fun _ i=>i.elim,
    fun _ i=>i.elim,fun i=>i.elim,fun _ i=>i.elim⟩

def before (h:Hard.Rent P.activities.forced P.activities.K P.p P.p.supportExponent k) :
    Gallery X Empty o P Γ := ⟨empty P o Γ X, Hard.rent h⟩

theorem paid (h:Hard.Rent P.activities.forced P.activities.K P.p P.p.supportExponent k) :
    (before (X:=X) (o:=o) (Γ:=Γ) h).Pays w P.p.supportExponent 0 k := by
  refine ⟨⟨fun i=>i.elim,fun i=>i.elim,fun i=>i.elim,?_⟩,Hard.leasing h⟩
  intro u
  exact ⟨fun i=>i.elim,(hasSum_fintype _).summable,by rw [tsum_empty]⟩

theorem gas (h:Hard.Rent P.activities.forced P.activities.K P.p P.p.supportExponent k)
    (hw : ∀v,0<w v) (x:X) (U:Config G n) :
    (before (X:=X) (o:=o) (Γ:=Γ) h).gas x U = Poly.bead Γ ((P.activities.gas P.p U : ℝ) : ℂ) := by
  let H : Hard X P.p P.activities.forced P.activities.K o Γ := Hard.rent h
  have summed := Hard.packet_summing H (Hard.leasing (w:=w) h) P.p.exponent_pos.le hw x U
  have one j : packet P.activities P.p (H.hard x) U j =
      Poly.bead Γ ((P.activities.gasOccurrence P.p j U : ℝ) : ℂ) := by
    unfold packet Activities.gasOccurrence
    split
    · rw [Complex.ofReal_prod, map_prod]; rfl
    · simp
  change (∑' j, packet P.activities P.p (H.hard x) U j) = Poly.bead Γ ((P.activities.gas P.p U:ℝ):ℂ)
  ext s
  by_cases hs : s = Γ.quiet
  · subst s
    exact (Hard.packet_of_quiet H x U summed).trans ((Poly.part_send ..).trans (if_pos rfl)).symm
  · rw [Poly.share summed]
    change (∑' j, (packet P.activities P.p (H.hard x) U j).part s) = _
    simp_rw [one]
    change (∑' j, (Poly.send Γ.quiet _).part s) = (Poly.send Γ.quiet _).part s
    simp_rw [Poly.part_send,if_neg hs,tsum_zero]

variable [Fintype V]
theorem density (h:Hard.Rent P.activities.forced P.activities.K P.p P.p.supportExponent k)
    (hw : ∀v,0<w v) (x:X) (U:Config G n) :
    (before (X:=X) (o:=o) (Γ:=Γ) h).density x U = (P.eval U:ℂ) • (1:Poly Γ) := by
  rw [Gallery.density, gas h hw x U]
  have zero : (before (X:=X) (o:=o) (Γ:=Γ) h).E.log x U=0 := tsum_empty
  have bead (c:ℂ) : Poly.bead Γ c=c • (1:Poly Γ) := by
    rw [← Poly.product_bead,mul_one]
  rw [zero,Next.Rank.Exponential.pass_zero,one_mul,bead,smul_smul,Rep.eval,Complex.ofReal_mul]

end YM.Integration.WilsonOriginalScalarGallery
