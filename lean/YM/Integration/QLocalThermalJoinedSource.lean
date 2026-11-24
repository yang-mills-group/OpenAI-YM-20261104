import YM.Integration.QLocalMarkedJoinedCatalogue
import YM.Integration.QLocalThermalPacketDivision

/-! The actual submitted token field supplies each original dirty sector of
the joined compulsory register, including the negative correction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalThermalJoinedSource
open Function Finset Lattice RG Wilson Marker Overlay Extra.Histories Planned.GuardedAtom
open RG3.Script.Picnic LocalComparison Comparison.Density.RenderM LocalComparison.MarkedPackets
open QLocalMarkedJoinedCatalogue QLocalThermalPacketDivision WilsonLimitConstruction.FundedMarkedFieldSplit
open scoped Classical BigOperators
variable {G:Gauge} {n:Side} {Q:Rep G n} {V:Type} [DecidableEq V] [Fintype V]
    {D:V→ ComparisonDensity.Address.Orbit} {Γ:Census V} {o:V→Site n}
    (P:MarkedPackets D G n Γ) {p:BudgetPoint} {a:V→Support n}
    {region:Comparison.Density.Testing.Region (fun v=>(D v).Mood) n}
    {w:V→ℝ} {g width budget:ℝ} {off cov:ℕ}

def row (phys:BudgetPoint) (g:ℝ) (c:ℂ) (s:Γ.Mode) (x:TestSpace D) (r:ℕ) (U:Config G n) : ℂ :=
  if pick P phys U r≠none ∧ s=P.mode r then c*P.term x g U r else 0

def source (H:P.Paid p a region w g width budget off cov) (hg:g≠0) (c:ℂ) :
    Source (W:=Q) (plot P) (fun x U=>c • dirty P Q.p x g U) where
  field:=row P Q.p g c
  dirty s x r U nz good:=by
    have cold:pick P Q.p U r=none:=(healthy P Q.p U r).2 good
    exact nz (by simp [row,cold])
  purchase s x U:=by
    let keep (i:ℕ):Prop:=pick P Q.p U i≠none
    let B:=WilsonPrescribedPacketTail.slice P keep
    have root:=NativePaidPacketColors.read_summable (clip P H keep) hg x g U
    have color:HasSum (fun i=>(Poly.send (B.mode i) (B.term x g U i)).part s) ((B.read x g U).part s):=
      root.hasSum.mapL (Poly.get s)
    change HasSum (fun r=>row P Q.p g c s x r U) (c*((B.read x g U).part s))
    apply (color.mul_left c).congr_fun
    intro i
    by_cases h:keep i
    · have hot:pick P Q.p U i≠none:=h
      cases packet_eq : P.packet i <;> by_cases mode:s=P.mode i <;>
        simp [row,B,WilsonPrescribedPacketTail.slice,MarkedPackets.term,h,hot,mode,packet_eq]
    · have cold:¬pick P Q.p U i≠none:=h
      simp [row,B,WilsonPrescribedPacketTail.slice,MarkedPackets.term,h,cold]

theorem issued (K:Guard.Keeper Q.p Q.activities) (T:Taste (TestSpace D) o Q Γ)
    (H:P.Paid p a region w g width budget off cov) (hg:g≠0) (c:ℂ)
    (funds:∀x,Financed (T.menu.terms x)) :
    ∃A:Compulsory (TestSpace D) Γ G n,∀x,Financed ((replace T A).menu.terms x) ∧
       ∀U,((replace T A).leaf x).contents.cluster U=
            Poly.pass (c • dirty P Q.p x g U)*(T.leaf x).contents.cluster U ∧
          ((replace T A).leaf x).density U=
            Poly.pass (c • dirty P Q.p x g U)*(T.leaf x).density U := by
  have quiet (x:TestSpace D) (U:Config G n):(c • dirty P Q.p x g U).part Γ.quiet=0:=by
    rw [Poly.part_smul,QLocalThermalPacketDivision.dirty,QLocalThermalPacketDivision.part,(WilsonPrescribedPacketTail.slice P _).quiet_read,mul_zero]
  obtain ⟨A,sold⟩:=QLocalMarkedJoinedCatalogue.issued K T (source P H hg c) quiet (fun _=>True)
    (fun x=>⟨trivial,funds x⟩) (fun _ _ _ _ _=>trivial)
  exact ⟨A,fun x=>⟨(sold x).2.1,(sold x).2.2⟩⟩

end YM.Integration.QLocalThermalJoinedSource
