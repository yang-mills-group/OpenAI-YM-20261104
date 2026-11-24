import YM.Integration.ManuscriptQLocalHardConditional
import YM.LocalLTE.Marked.Send
import YM.LocalLTE.Reels.Ovation
import YM.MergeProof.Magma
import YM.MergeProof.Hash

/-! Literal signed connected-ticket expansion on the same conditional law as
the hard disk. All local integrations and source mask equalities are retained. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ManuscriptQLocalIntegratedTicket
open Filter Function Finset Lattice Wilson Merge RG Tree Pressure Pressure.Stores ConnectedActivityE6
open ConnectedActivityE6.Blaze Blaze.March Captain Push Push.AbsoluteSums
open PhysicalNext PhysicalNext.Repeat Next.Scheduling AnalyticBridge VerifiedReset
open MergeProof Marker Extra.Multi LocalLTE PhysicalNext.Repeat.Daisy
open ManuscriptQLocalMarkedHeightTail
open scoped Classical Topology BigOperators
variable {G:Gauge} {c f L:Side} {S:StepData c f} {T:Tube G S} {R:Rep G f}
  {P:Teller G} {Q:ConnectedActivityE6.Target G P} {W x μ a:ℝ}
  {o:Target.Order G W} (H:Cash W x μ L Q o a T R) (χ:Push.SectorMeasure.Chi)
  {V ι:Type} [DecidableEq V] [Fintype ι] {Γ:Marker.Census V} (M:ι→Menu.Hat Γ R)

def activity (p:Ursell.Clusters H.ThinP) (D:Captain.Oscars (fun i : ι => (M i).M) p) (U:Config G c) : ℝ :=
  Ursell.coefficient H.seam p.2*(∏b,Merge.Palette.act (fun i : ι => (M i).M) H χ U (p.2 b).val (D b)) / ↑(p.fst+1).factorial

omit [Fintype ι] in
lemma pulse (w:V→ℝ) (p:Ursell.Clusters H.ThinP) (D:Captain.Oscars (fun i : ι => (M i).M) p) :
    Captain.pulseV p (fun i : ι => (M i).M) Γ (fun i=>Menu.sing (M i) w) D=phase H M w ⟨p,D⟩ := by
  have productAttach (t:Finset ι):(∏ i∈t.attach,Menu.sing (M i.1) w)=∏ i∈t,Menu.sing (M i) w:=
    Finset.prod_attach t (fun i=>Menu.sing (M i) w)
  simp [Captain.pulseV,phase,Occ,Fintype.prod_sigma,productAttach]

theorem signed (w:V→ℝ) (hw:∀v,0<w v) (p:Ursell.Clusters H.ThinP) (U:Config G c) :
    Switch.sound (fun i=>Menu.sing (M i) w) (Merge.Palette.song (fun i : ι => (M i).M) H χ (fun i=>Menu.sumFee (M i) w) p U)=
    ∑D:Captain.Oscars (fun i : ι => (M i).M) p,(activity H χ M p D U:ℂ) • matrix H M ⟨p,D⟩ := by
  have raw:=Captain.horns (H:=H) (χ:=χ) p (fun i : ι => (M i).M) (fun i=>Menu.sumFee (M i) w) Γ
    (fun i=>Menu.sing (M i) w) (fun i=>(Menu.virtue (M i) w).2) U
  refine raw.trans (Finset.sum_congr rfl fun D _=>?_)
  rw [pulse H M,ManuscriptQLocalMarkedHeightTail.physical H M w hw,smul_smul]
  change (↑(Captain.pearl p (fun i : ι => (M i).M) (fun i=>Menu.sumFee (M i) w) D*activity H χ M p D U):ℂ) • _ =
    ((activity H χ M p D U:ℂ)*(Captain.pearl p (fun i : ι => (M i).M) (fun i=>Menu.sumFee (M i) w) D:ℂ)) • _
  rw [Complex.ofReal_mul,mul_comm]

/-- Every fixed true source cluster has a finite native mark polynomial before
any root estimate is applied. Its coefficients may have either sign. -/
theorem finite_model (w:V→ℝ) (hw:∀v,0<w v) (p:Ursell.Clusters H.ThinP) (U:Config G c) :
    ∃a:ℝ,Switch.Paid (fun _:Unit=>Merge.Palette.song (fun i : ι => (M i).M) H χ (fun i=>Menu.sumFee (M i) w) p U) a := by
  let r:=fun i=>Menu.sumFee (M i) w
  let f (D:Captain.Oscars (fun i : ι => (M i).M) p) (_:Unit):=fun t S=>Fan.sponsor (fun i : ι => (M i).M) H r ⟨p,D⟩ t S*activity H χ M p D U
  let a (D:Captain.Oscars (fun i : ι => (M i).M) p):=Captain.pearl p (fun i : ι => (M i).M) r D*‖activity H χ M p D U‖
  have term (D:Captain.Oscars (fun i : ι => (M i).M) p):Switch.Paid (f D) (a D):=
    (Fan.amends (fun i : ι => (M i).M) H r (fun i=>Menu.timed (M i) hw) ⟨p,D⟩ Unit).mul
      (Switch.constant (ι:=ι) (fun _:Unit=>activity H χ M p D U) (norm_nonneg _) (fun _=>le_rfl))
  have full:=Switch.Paid.sum Finset.univ f a (fun i _=>term i)
  have ident:(fun _:Unit=>Merge.Palette.song (fun i : ι => (M i).M) H χ r p U)=∑D:Captain.Oscars (fun i : ι => (M i).M) p,f D:=by
    funext _ t S
    simpa only [f,activity,Fan.actorsV,Finset.sum_apply] using Fan.music (fun i : ι => (M i).M) H χ r p U t S
  exact ⟨_,ident.symm ▸ full⟩

/-- The original deposited log sheet carries the physical zero-source value
with its exact sign. Every nonempty mark mode reads the full signed sum. -/
theorem centered (w:V→ℝ) (hw:∀v,0<w v) (p:Ursell.Clusters H.ThinP) (U:Config G c) :
    Merge.Photo.headSheet (fun i : ι => (M i).M) H χ (fun i=>Menu.sumFee (M i) w) Γ (fun i=>Menu.sing (M i) w) p U =
      (∑D:Captain.Oscars (fun i : ι => (M i).M) p,(activity H χ M p D U:ℂ) • matrix H M ⟨p,D⟩) +
        Poly.bead Γ (↑(-Merge.Palette.song (fun i : ι => (M i).M) H χ (fun i=>Menu.sumFee (M i) w) p U 0 ∅):ℂ) := by
  let r:=fun i=>Menu.sumFee (M i) w
  let raw:=Merge.Palette.song (fun i : ι => (M i).M) H χ r p U
  let vac:ℝ:=raw 0 ∅
  obtain ⟨a,paid⟩:=finite_model H χ M w hw p U
  have bare:=Switch.constant (ι:=ι) (fun _:Unit=>-vac) (norm_nonneg _) (fun _=>le_rfl)
  have eqn:Merge.Photo.tones (fun i : ι => (M i).M) H χ r p U=raw+(fun _ _=>-vac):=by
    funext t S
    change raw t S-vac=raw t S+ -vac
    exact sub_eq_add_neg ..
  change Switch.sound (fun i=>Menu.sing (M i) w) (Merge.Photo.tones (fun i : ι => (M i).M) H χ r p U)=_
  rw [eqn,Switch.add_sounds _ ((paid.works ()).choose_spec) ((bare.works ()).choose_spec),Switch.const_sounds]
  rw [show Switch.sound (fun i=>Menu.sing (M i) w) raw=_ from signed H χ M w hw p U]

variable {C d rv s A v y B e:ℝ} {j k:ℕ}
  (N:Captain H j C d rv s A v y B e k χ) (host:HostQ H N.conduit A B k)

include N host in
theorem conditional (w:V→ℝ) (hw:∀v,0<w v) (p:Ursell.Clusters H.ThinP) (U:Config G c)
    (Z:BudgetPoint) (ht:Z.threshold=Pressure.temp x) (hord:Z.order≤j) (n:ℕ) (hn:Z.power≤n) :
    Switch.sound (fun i=>Menu.sing (M i) w) (Merge.Palette.song (fun i : ι => (M i).M) H χ (fun i=>Menu.sumFee (M i) w) p U)=
    ∑D:Captain.Oscars (fun i : ι => (M i).M) p, if ManuscriptQLocalForcedClusters.alive H χ (fun i : ι => (M i).M) ⟨p,D⟩ then
      ((RG.masked Z.threshold (Captain.reachability p) (Captain.wingTerm (H:=H) (χ:=χ) p (fun i : ι => (M i).M) D) U:ℝ):ℂ) •
        matrix H M ⟨p,D⟩ else 0 := by
  rw [signed H χ M w hw]
  apply Finset.sum_congr rfl
  intro D _
  have paid:=ManuscriptQLocalForcedClusters.differentiated H χ (fun i : ι => (M i).M) N host ⟨p,D⟩ Z ht hord n hn
  have measured:activity H χ M p D U=RG.masked Z.threshold (Captain.reachability p)
      (Captain.wingTerm (H:=H) (χ:=χ) p (fun i : ι => (M i).M) D) U:=congrFun paid.1 U
  rw [measured]
  by_cases live:ManuscriptQLocalForcedClusters.alive H χ (fun i : ι => (M i).M) ⟨p,D⟩
  · rw [if_pos live]
  · rw [if_neg live,ManuscriptQLocalForcedClusters.dead H χ (fun i : ι => (M i).M) ⟨p,D⟩ live]
    simp [RG.masked]

/-! The native deposition groups the linked sheet at its original support and
its unrestricted signed forced factors at their original inventory profiles. -/

def linked (w:V→ℝ) (p:H.fragrances) (U:Config G c) : Poly Γ :=
  (∑D:Captain.Oscars (fun i : ι => (M i).M) p,(activity H χ M p D U:ℂ) • matrix H M ⟨p,D⟩) +
    Poly.bead Γ (↑(-Merge.Palette.song (fun i : ι => (M i).M) H χ (fun i=>Menu.sumFee (M i) w) p U 0 ∅):ℂ)

lemma marked (w:V→ℝ) (hw:∀v,0<w v) (p:H.fragrances) (U:Config G c) (s:Γ.Mode) (hs:s≠Γ.quiet) :
    (Merge.Photo.headSheet (fun i : ι => (M i).M) H χ (fun i=>Menu.sumFee (M i) w) Γ (fun i=>Menu.sing (M i) w) p U).part s =
    ∑D:Captain.Oscars (fun i : ι => (M i).M) p,(activity H χ M p D U:ℂ)*(matrix H M ⟨p,D⟩).part s := by
  have bead (v:ℂ):(Poly.bead Γ v).part s=0:=by
    change (Poly.send Γ.quiet v).part s=0
    simp only [Poly.part_send,if_neg hs]
  simp only [centered H χ M w hw p U,Poly.part_plus,Poly.part_sum,Poly.part_smul,bead,add_zero]

/-- The full push of the original offered mixed density. The genuine native
coarse forced field includes its entire signed inventory, simultaneously with
the explicitly expanded connected exponent on the same coarse configuration. -/
theorem pushed [Fintype V] (w:V→ℝ) (hw:∀v,0<w v) (A:Rep G c) (K:ℝ→Finset ι→ℕ→ Config G c→ℝ)
    {dk ex kr:ℝ} (law:Merge.Photo.Usable (fun i : ι => (M i).M) H χ A (fun i=>Menu.sumFee (M i) w) K dk ex kr)
    (U:Config G c) : S.push R.beta (Menu.Expense M w S) U=(Real.exp (A.exponent U):ℂ) •
      (Poly.pass (∑X,Accent.tally (fun p:H.fragrances=>H.bookFoot (.inr p)) (linked H χ M w) X U)*
        Accent.field (fun P=>Merge.Photo.chain A K Γ (fun i=>Menu.sing (M i) w) P U) (RG.flags A.p.threshold U)) := by
  have quoted:=Merge.Photo.scored (fun i : ι => (M i).M) H χ A (fun i=>Menu.sumFee (M i) w) K Γ
    (fun i=>Menu.sing (M i) w) (fun i=>(Menu.virtue (M i) w).2) law w hw (fun i=>Menu.paid (M i) hw)
    (fun i=>(Menu.virtue (M i) w).1) U
  have same:Merge.Photo.headSheet (fun i : ι => (M i).M) H χ (fun i=>Menu.sumFee (M i) w) Γ (fun i=>Menu.sing (M i) w)=linked H χ M w:=
    funext fun p=>funext fun U=>centered H χ M w hw p U
  simpa only [Menu.Expense,Merge.Photo.spine,same] using quoted

/-- The physical mixed conditional identity, including the complete signed gas. -/
def Deposited [Fintype V] (w:V→ℝ) (A:Rep G c) (K:ℝ→Finset ι→ℕ→ Config G c→ℝ) : Prop :=
  ∀U,S.push R.beta (Menu.Expense M w S) U=(Real.exp (A.exponent U):ℂ) •
    (Poly.pass (∑X,Accent.tally (fun p:H.fragrances=>H.bookFoot (.inr p)) (linked H χ M w) X U)*
      Accent.field (fun P=>Merge.Photo.chain A K Γ (fun i=>Menu.sing (M i) w) P U) (RG.flags A.p.threshold U))

/-- The complete incoming marked density, including its original compulsory
partners, is the same at every positive radius vector. -/
theorem expense_eq (step:StepData c f) (w r:V→ℝ) (hw:∀v,0<w v) (hr:∀v,0<r v)
    {σ C t e d:ℝ} (real:R.Lawful σ C t e d) : Menu.Expense M w step=Menu.Expense M r step :=
  funext fun U=>(Menu.passIn M step real hw U).trans (Menu.passIn M step real hr U).symm

/-- The signed conditional linked field retains its full physical matrix
when the temporary source measurement radius is changed. -/
theorem linked_eq (w r:V→ℝ) : linked H χ M w=linked H χ M r := by
  funext p U
  have quiet:Merge.Palette.song (fun i : ι => (M i).M) H χ (fun i=>Menu.sumFee (M i) w) p U 0 ∅ =
      Merge.Palette.song (fun i : ι => (M i).M) H χ (fun i=>Menu.sumFee (M i) r) p U 0 ∅ := by
    have ws:Merge.Palette.ways (fun i=>Menu.sumFee (M i) w) 0 ∅=
        Merge.Palette.ways (fun i=>Menu.sumFee (M i) r) 0 ∅:=by
      funext i;simp [Merge.Palette.ways]
    unfold Merge.Palette.song
    rw [ws]
  simp only [linked,quiet]

/-- The original incoming source and linked field are evaluated at `w`. The
authentic complete outgoing gas is read at its purchased radius `r`. -/
def Recovered [Fintype V] (w r:V→ℝ) (A:Rep G c) (K:ℝ→Finset ι→ℕ→ Config G c→ℝ) : Prop :=
  ∀U,S.push R.beta (Menu.Expense M w S) U=(Real.exp (A.exponent U):ℂ) •
    (Poly.pass (∑X,Accent.tally (fun p:H.fragrances=>H.bookFoot (.inr p)) (linked H χ M w) X U)*
      Accent.field (fun P=>Merge.Photo.chain A K Γ (fun i=>Menu.sing (M i) r) P U) (RG.flags A.p.threshold U))

theorem recover [Fintype V] (w r:V→ℝ) (hw:∀v,0<w v) (hr:∀v,0<r v) {σ C t e d:ℝ} (real:R.Lawful σ C t e d)
    (A:Rep G c) (K:ℝ→Finset ι→ℕ→ Config G c→ℝ) (base:Deposited H χ M r A K) : Recovered H χ M w r A K := by
  intro U
  rw [expense_eq M S w r hw hr real,linked_eq H χ M w r]
  exact base U

end YM.Integration.ManuscriptQLocalIntegratedTicket
