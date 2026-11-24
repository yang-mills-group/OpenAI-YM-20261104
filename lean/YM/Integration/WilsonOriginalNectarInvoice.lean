import YM.Integration.WilsonThermometerOwnOffsetNectar

/-! On the actual displaced physical trajectory all three pieces of the
coloured source agree before any testing or integration, including the
exponential entry and the literal individual forced keys. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalNectarInvoice
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Copper
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetSource WilsonThermometerOwnOffsetField
open WilsonThermometerOwnOffsetTale WilsonThermometerOwnOffsetNectar
open ProjectorNext.Equivariance Push.Local WilsonThermometerOffsetResidue
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) {k j N p d:ℕ} {D:Rail R.family} {B:ℕ→ℕ→ℝ}

theorem original {V:Sight R.family d p} {r:Emblems R.family d}
    (z:Site (R.family.side N p))
    (H:Enrolled R.makes D B k N p d (digits R N p z) V r)
    (hj:k≤j) (hn:j≤N) (y:Palette R.family d) :
    let P:=R.family.path.rep N p j
    let o:=site R hn z
    let x:=finer r hj y
    let s:=factor R k j d
    ∃Q:Coefficient (R.family.labels.level d) (R.family.side j p),
      Q.Format o R.family.params P ∧
      Q.remBound o P (kappa R.family.path j) (‖s‖*(B d j*size x)) ∧
      invoice Q o (R.family.localSection d) P=state (k:=k) R V r y z j :=by
  intro P o x s
  let t:=primaryLetter d
  let C:=R.family.localSection d
  let π:=Classical.choice ((R.makes.wilson.represents N p j hn).good.labels.moves 1 o)
  obtain ⟨v,hp⟩:=(H.legal j hj hn).capacity0 x
  rcases hp with @⟨X,F,fee,b,tail,cert,wallet,assembled,hx,hy,financed⟩
  have bill:fee t≤B d j*size x:=((Finset.single_le_sum (fun l _=>rem_nonneg (wallet l))
    (Finset.mem_univ t)).trans (le_add_of_nonneg_right tail.nonneg)).trans financed
  have paid:=rem_mono (wallet t) bill
  have tab : strand R V r hj y=invoice (X t) 0 C P :=
    (congrArg (fun S:Tape G (R.family.side j p)=>S (line t)) assembled.symm).trans
      (together_line X F tail t)
  have center:affine (1:Signed) o 0=o:=by simp [affine]
  let Q:=shifted π (X t)
  have form:Q.Format o R.family.params P:=center ▸ shifted.format π 0 (always_room R.family j p) (cert t)
  have fare:Q.remBound (affine (1:Signed) o 0) P (kappa R.family.path j)
        (permission P.p 1 * (B d j*size x)):=shifted.cap π (cert t) paid
  have noFee:permission P.p 1=1:=by unfold permission;exact if_pos (fun _=>rfl)
  have price:Q.remBound o P (kappa R.family.path j) (B d j*size x):=
    Eq.mp (congrArg₂ (fun a b=>Q.remBound a P (kappa R.family.path j) b) center
      (show permission P.p 1*(B d j*size x)=B d j*size x by rw [noFee,one_mul])) fare
  have same : invoice Q o C P=shiftTape o π (invoice (X t) 0 C P):=by
    refine Prod.ext ?_ (Prod.ext ?_ rfl)
    · change Q.density o C P=(X t).density 0 C P ∘ Lattice.pull 1 o
      exact (congrArg (fun a=>Q.density a C P) center.symm).trans
        (shifted.density π C (R.makes.sections d) (X t) 0)
    · funext U
      change Q.exponentialEntry o C P U=(X t).exponentialEntry 0 C P (Lattice.pull 1 o U)
      exact (congrArg (fun a=>Q.exponentialEntry a C P U) center.symm).trans
        (shifted.expEntry π C (R.makes.sections d) (X t) U 0)
  refine ⟨stretch s Q,stretch_format s form,stretch_rem s price,?_⟩
  calc
    invoice (stretch s Q) o C P=s • invoice Q o C P:=invoice_stretch Q o C P s
    _=s • shiftTape o π (strand R V r hj y):=congrArg (s • ·) (same.trans (congrArg (shiftTape o π) tab.symm))
    _=state (k:=k) R V r y z j:=by unfold state; rw [dif_pos (And.intro hj hn)];rfl

end YM.Integration.WilsonOriginalNectarInvoice
end
