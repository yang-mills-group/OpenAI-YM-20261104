import YM.Integration.QLocalThermalPacketDivision
import YM.Integration.QLocalCompulsoryInventoryLocal

/-! Source of a simultaneous opposite signed rebooking, with actual old
marked compulsory gases in both channels and the true thermal cut of
each submitted spatial token. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalThermalPacketRebooking
open Function Finset Lattice Wilson RG Marker Overlay RG3.Script.Picnic
open LocalComparison Comparison.Density.RenderM Comparison.Density.Markers
open QLocalCompulsoryInventoryProduct QLocalCompulsoryInventoryBank QLocalCompulsoryInventoryLocal
open QLocalThermalPacketDivision WilsonLimitConstruction.FundedMarkedFieldSplit WilsonLimitConstruction.FundedMarkedSoftRows
open scoped Classical BigOperators
variable {G:Gauge} {V:Type} [DecidableEq V] [Fintype V] {Γ:Census V} {D:V→ ComparisonDensity.Address.Orbit}
    {n:Side} {Q:Rep G n} {o:V→Site n} (P:MarkedPackets D G n Γ) {q:BudgetPoint} {a:V→Support n}
    {region:Comparison.Density.Testing.Region (fun i=>(D i).Mood) n}
    {w:V→ℝ} {g width budget:ℝ} {off cov:ℕ}

def regular (fill:Γ.Mode) (g:ℝ) : Rows (TestSpace D) Γ G n :=
  {mode:=fun i=>if (P.packet i).isSome then P.mode i else fill,
   site:=fun i=>(P.packet i).elim univ (fun T=>T.plot),value:=fun x i U=>P.term x g U i}

theorem soft (fill:Γ.Mode) (H:P.Paid q a region w g width budget off cov) (hg:g≠0)
    (x:TestSpace D) (U:Config G n) :
    HasSum (wave (regular P fill g) Q.p x U) (clear P Q.p x g U) := by
  let keep i:=pick P Q.p U i=none
  let L:=WilsonPrescribedPacketTail.slice P keep
  have ht:=NativePaidPacketColors.read_summable (clip P H keep) hg x g U
  apply ht.hasSum.congr_fun
  intro i
  symm
  change Poly.send (L.mode i) (L.term x g U i)=wave (regular P fill g) Q.p x U i
  cases e:P.packet i with
  | none=>
    simp [regular,L,wave,MarkedPackets.term,WilsonPrescribedPacketTail.slice,e,masked]
  | some T=>
    by_cases live:Healthy Q.p.threshold T.plot U
    · have kept:keep i:=(healthy P Q.p U i).2 (by simpa [plot,e] using live)
      simp [regular,L,wave,MarkedPackets.term,WilsonPrescribedPacketTail.slice,e,kept,masked_eq _ _ _ _ live]
    · have drop:¬keep i:=fun h=>live (by simpa [plot,e] using (healthy P Q.p U i).1 h)
      simp [regular,L,wave,MarkedPackets.term,WilsonPrescribedPacketTail.slice,e,drop,masked_ne _ _ _ _ live]

omit [Fintype V] in
private theorem opposite {H:Bands Γ Q} {c:Site n→ Config G n→Poly Γ} (S:Captured H c) :
    Captured H (fun ξ U=>-(c ξ U)) where
  roots i ξ hi U:=by simpa only [zero_sub] using (carry_zero.sub (S.roots i ξ hi U))
  reads i ξ hi U W fields flags:=congrArg Neg.neg (S.reads i ξ hi U W fields flags)
  measurable ξ:=(S.measurable ξ).neg
  invariant ξ s U:=congrArg Neg.neg (S.invariant ξ s U)

theorem invoice (F E:Taste (TestSpace D) o Q Γ) (H:P.Paid q a region w g width budget off cov)
    (hg:g≠0) {d κ:ℝ} (valid:Q.activities.Valid Q.p d κ)
    (fa:∀x,(F.leaf x).Active) (ea:∀x,(E.leaf x).Active)
    (ff:∀x,∃u c t b,(F.menu.terms x).Radial w u c t b) (ef:∀x,∃u c t b,(E.menu.terms x).Radial w u c t b)
    (fc:∀x,Captured (F.menu.terms x) (flag P Q.p x g)) (ec:∀x,Captured (E.menu.terms x) (flag P Q.p x g)) :
    Nonempty (Invoice F E (fun x U=>P.read x g U)) := by
  let h x:=flag P Q.p x g
  let neg x ξ U:=-(h x ξ U)
  have hz:∀x ξ U,(h x ξ U).part Γ.quiet=0:=fun x ξ U=>quiet P Q.p x g ξ U
  have nz:∀x ξ U,(neg x ξ U).part Γ.quiet=0:=fun x ξ U=>by simp [neg,hz]
  have fs x U:∀i,Summable (fun j=>(F.menu.terms x).tagged i j U):=by
    obtain ⟨u,c,t,b,fare⟩:=ff x
    exact ((F.menu.terms x).baseBound (fa x).articles fare valid U).1
  have es x U:∀i,Summable (fun j=>(E.menu.terms x).tagged i j U):=by
    obtain ⟨u,c,t,b,fare⟩:=ef x
    exact ((E.menu.terms x).baseBound (ea x).articles fare valid U).1
  refine ⟨{
    soft := regular P (F.menu.rays 0) g
    hard := fun x U => total Q (h x) U
    quiet := fun x U => total_quiet (h x) (hz x) U
    formalForced := tape F neg
    residualForced := tape E h
    formal_active := ?_
    residual_active := ?_
    formal_sum := ?_
    residual_sum := ?_
    masked := ?_
    formal_cluster := ?_
    residual_cluster := ?_ }⟩
  · intro x
    exact ⟨QLocalCompulsoryInventoryLocal.active _ (fa x).articles valid.forced _ (opposite (fc x))
      (fun i U=>fs x U i),(fa x).captions⟩
  · intro x
    exact ⟨QLocalCompulsoryInventoryLocal.active _ (ea x).articles valid.forced _ (ec x)
      (fun i U=>es x U i),(ea x).captions⟩
  · intro x U
    obtain ⟨u,c,t,b,fare⟩:=ff x
    exact ((F.menu.terms x).bulkBound (fa x).articles fare U).1
  · intro x U
    obtain ⟨u,c,t,b,fare⟩:=ef x
    exact ((E.menu.terms x).bulkBound (ea x).articles fare U).1
  · intro x U
    have sep:=partition P Q.p H hg x U
    have hclear : clear P Q.p x g U = P.read x g U - total Q (h x) U := by
      change clear P Q.p x g U=P.read x g U-∑ξ∈flags Q.p.threshold U,flag P Q.p x g ξ U
      rw [sep.1,←sep.2,add_sub_cancel_right]
    rw [←hclear]
    exact soft P (F.menu.rays 0) H hg x U
  · intro x U
    have rev:total Q (neg x) U= -total Q (h x) U:=by simp [neg,total]
    simpa only [rev] using
      (funded F neg nz (fun x i U=>fs x U i) x U).1
  · intro x U
    exact (funded E h hz (fun x i U=>es x U i) x U).1

end YM.Integration.QLocalThermalPacketRebooking
