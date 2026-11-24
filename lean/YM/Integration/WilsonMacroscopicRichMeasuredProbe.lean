import YM.Integration.WilsonMacroscopicRichLastResponse
import YM.Integration.WilsonMacroscopicRichReportedRays
import YM.Integration.ActualWilsonPrimaryPreparation

/-! The complete fitted output of the actual marked Wilson forest is measured by its genuine nonlinear radial probes. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichMeasuredProbe
open Filter Function Set Lattice Wilson RG Source Labels Analysis Next.Foundations Push.Local Bid
open ProjectorNext.Equivariance Trace.Physical Trace.Physical.GermGraph RG16 RG16.Literal
open PhysicalNext.Repeat.Legato RGComparison.Core16 OPE PhysMS Spec
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} (R : Run G) {N p u : ℕ}

theorem measured (T : Slices R.family.path.levels p) (live : u < N) (h : ℕ)
    (Y : Config G (R.family.side N p) → ℂ) (ct : Continuous Y) (gi : GaugeInvariant Y)
    (door : Opened R.family h u p) (book : Booked R.family N p h Y u live.le) :
    let V := R.family.path.rep N p u
    let M := topReport R.family N p h R.makes u door live.le Y
    ∀ t : Probe G h, runProbe (R.family.labels.level h) t (fitting h N p u R.makes door live.le M) =
      Germ.jet R.family.params t V.p.threshold 0 (WilsonMacroscopicRichReportedPosterior.observation R T live.le h Y) := by
  intro V M t
  let q := sheet R.family N p h Y u live.le
  let F := R.family.labels.level h
  let A := R.family.params
  let B := R.family.localSection h
  let θ := V.p.threshold
  let f := WilsonMacroscopicRichReportedPosterior.observation R T live.le h Y
  let c : Config G (R.family.side u p) → ℂ := B.places (F.scaled θ⁻¹ q.x) 0
  obtain ⟨a,⟨formed,bill⟩,_,fits⟩ := WilsonMacroscopicRichReportedPosterior.issued R T live.le h Y door book
  have read := ActualWilsonPrimaryPreparation.original R h N p u door.post live.le
  have g := WilsonMacroscopicRichLastResponse.regular R T live h Y ct gi
  have sum := (WilsonMacroscopicRichReportedRays.original R T live.le h Y door book).1
  have visible : JetTest A 0 (F.coords.symm (F.scaled θ⁻¹ q.x)) c := by
    simpa only [Reads,if_pos (nonwrapping_placement B 0 read.fit)] using placed_reads B 0 read.fit read.sound (F.scaled θ⁻¹ q.x)
  have p0 : runProbe F t q.x = Germ.jet A t θ 0 c := by
    simpa only [F.coords.apply_symm_apply,F.scaled_inv (show θ ≠ 0 from V.p.threshold_pos.ne')]
      using Germ.charged F A θ visible t
  have test := Germ.computed A g 0 read.order
  have dt : Germ.jet A t θ 0 (f-c) = Germ.jet A t θ 0 f - Germ.jet A t θ 0 c :=
    iteratedDeriv_fun_sub ((test _).1.of_le (Nat.cast_le.mpr (Nat.le_of_lt_succ t.2.isLt)))
      ((visible _).1.of_le (Nat.cast_le.mpr (Nat.le_of_lt_succ t.2.isLt)))
  have total := Germ.vector_summable F A formed bill read.order read.power
  obtain ⟨_,_,_,_,_,_,⟨e,ce,he⟩,_⟩ := bill
  have se : Summable e := ce.2.1.of_nonneg_of_le (fun i => (he i).1) (fun i => V.p.loMass _ _ (he i).1)
  have localCore := (presented_good 0 read q.x).1
  have hf : HasOrderAt f 1 h := HasOrderAt.fewer read.order (g.smooth _ (one_healthy _ _ V.p.threshold_pos.le))
  have hc : HasOrderAt c 1 h := HasOrderAt.fewer read.order (localCore.smooth _ (one_healthy _ _ V.p.threshold_pos.le))
  have curve := jet_sum (P:=V.p) formed.smooth he se sum h (hf.sub hc) read.order A (θ • t.1) t.2 (Nat.le_of_lt_succ t.2.isLt)
  have each i : runProbe F t (Germ.vector F A θ 0 (q.regular i)) = Germ.jet A t θ 0 (q.regular i) :=
    Germ.charged _ _ _ (Germ.computed A (formed.smooth i) 0 read.order) t
  have hs : HasSum (fun i => runProbe F t (Germ.vector F A θ 0 (q.regular i))) (Germ.jet A t θ 0 (f-c)) := by
    simpa only [each,Germ.jet,Function.comp_def] using curve
  have eq := HasSum.unique (total.hasSum.mapL (runProbe F t)) hs
  have calibrated : fitting h N p u R.makes door live.le M = Germ.projection F A θ 0 q := by
    have orig : V.p = plank R.family u := (R.makes.wilson.represents N p u live.le).vac
    simpa only [page,←orig] using fits
  rw [calibrated]
  change runProbe F t (q.x+∑' i,Germ.vector F A θ 0 (q.regular i)) = Germ.jet A t θ 0 f
  rw [map_add,eq,dt,p0]; abel

end YM.Integration.WilsonMacroscopicRichMeasuredProbe
