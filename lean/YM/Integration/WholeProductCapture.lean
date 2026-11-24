import YM.Integration.OriginalProductCellMatch
import YM.Integration.WholeCaptureTransport

/-! The original finite Wilson product determines a paid signed trajectory
down to the prescribed stopping scale. Its leading slot vanishes there.
The remaining displacement of the intrinsic projected coordinate is paid by
the wrapping invoice of that same coefficient. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WholeProductCapture
open Function Filter Set MeasureTheory Lattice Wilson RG Source Labels
open Extra.Histories Relay Bid Cells Push.Local Motion MergeProof MergeProof.Accent
open RG16.Literal Trace.Physical.GermGraph PhysicalNext.Repeat
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} (C : Family G) (N b p d J s : ℕ) (H : C.Makes)
variable {W : Worth} {u ψ φ δ : ℕ → ℝ} {r : ℕ → ℕ} {ζ : ℕ → ℕ → ℝ}
variable {D : ∀ N p i : ℕ, i < N → GaugeDoor (C.path.rep N p (i+1)) (C.path.rep N p i)}
variable (h : Scrim C W u ψ φ δ ζ r D)
set_option quotPrecheck false
local notation "σ" => (C.labels.level d).coeffSize
local notation "R" => C.path.rep N p
local notation "V" => calValues (C := C) d N p
local notation "Θ" => value (C := C) d N p

/-- One signed trajectory in the true Wilson representation, its uniform
bill, its exact full end-coordinate correction and its wrapping remainder. -/
def Retained (ho : Opened C d s p) (hs : s ≤ b) (hb : b < N)
    (f : Cut C N p) (B : C.label d) (a : ℝ) : Prop :=
    ∃ (P : ∀ i, store C d p i) (g : ℕ → ℝ),
      (P s).x = 0 ∧
      (∀ i ≥ s, i < b → Θ i (P i) =
        transition (C := C) d N p i (Θ (i+1) (P (i+1)))) ∧
      (∀ i ≥ s, ∀ hi : i ≤ b,
        reads d N p i (P i) (g i) ∧
        credit C N p d f i (hi.trans hb.le) =
          Θ i (P i) + V i ((C.factory d N p).terminal.symm B) ∧
        Booked C N p d f i (hi.trans hb.le) ∧
        gainChart C.path b i * (g i + σ (P i).x) ≤ a) ∧
      mCost C d N p s
          (topReport C N p d H s ho (hs.trans hb.le) f - (C.factory d N p).terminal.symm B) ≤
        invoice (C := C) d s p * (a / gainChart C.path b s)

/-- A purchased receipt can be used at its published larger budget. -/
theorem Retained.weaken (ho : Opened C d s p) (hs : s ≤ b) (hb : b < N)
    (f : Cut C N p) (B : C.label d) {a a' : ℝ}
    (source : Retained C N b p d s H ho hs hb f B a) (haa : a ≤ a') :
    Retained C N b p d s H ho hs hb f B a' := by
  obtain ⟨P,g,hzero,hsteps,hpath,hend⟩ := source
  refine ⟨P,g,hzero,hsteps,?_,hend.trans ?_⟩
  · intro i hsi hib
    obtain ⟨hread,heq,hbook,hbound⟩ := hpath i hsi hib
    exact ⟨hread,heq,hbook,hbound.trans haa⟩
  · exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right haa (Real.exp_pos _).le)
      (invoice_nn d p s)

/-- Keep the actual fixed input coefficient and its fee visible. The
origin and every later step use that same calibrated family. -/
theorem from_model (ho : Opened C d s p) (f : Cut C N p) (hf : Continuous f)
    (B : C.label d) (stocked : ℕ) (hJ : J ≤ stocked) (hst : s ≤ stocked)
    (htb : stocked ≤ b) (hb : b < N) (width fee E : ℝ) (Q : store C d p b)
    (hq : Q.Format 0 C.params (R b))
    (hr : Q.remBound 0 (R b) (safety C b) fee) (hsize : σ Q.x ≤ fee)
    (hfull : Fleet C N p d b J f (hJ.trans (htb.trans hb.le))
      (march (fun _ : Site (C.side J p) => width) φ stocked b) Q hb.le)
    (ht : TransmittedCellMatch.Transmitted C N b stocked p d (2*width) h Q s
      ho.post hst htb hb.le fee E B) :
    Retained C N b p d s H ho (hst.trans htb) hb f B (4*(1+stock C b)*(2*fee)) := by
  have hs := hst.trans htb
  let X := (h.costs.aim d N p (ho.post.trans (hs.trans hb.le))).lyrics.choose
  let z := (C.factory d N p).terminal.symm B
  obtain ⟨hX,hSong,_,_⟩ := (h.costs.aim d N p (ho.post.trans (hs.trans hb.le))).lyrics.choose_spec
  obtain ⟨A,hTop,hC,_,endcoord⟩ :=
    TransmittedCellMatch.primary_iff C N b stocked p d (2*width) h Q
      s ho.post hst htb hb.le fee E B ht
  let P := dualize C.path N p X s b A (-z)
  have key (i : ℕ) (hsi : s ≤ i) (hib : i ≤ b) (v : C.label d) :=
    keys (C.localSection d) C.path N p C.params X v (hC.chairs i hsi hib)
      (hSong.earned i (ho.post.trans hsi) (hib.trans hb.le))
  have hstem : (A s).a = z := by
    apply (X.tone s).index.injective
    have hy := (key s le_rfl hs 0).1.symm.trans ((endcoord B).mp rfl)
    simpa only [add_zero] using hy
  have hzero : (P.voice s).x = 0 := by
    change ((A s).bar X (-z)).x = 0
    rw [(key s le_rfl hs _).1, hstem, add_neg_cancel, map_zero]
  have origin := originate (C.localSection d) C.path N p C.params X hb.le H.wilson
    (hSong.earned b (ho.post.trans hs) hb.le) hq hr
    (show σ Q.x + fee ≤ 2*fee by linarith only [hsize])
  have woke : P.Woke C.params W (C.localSection d) (2*fee) := by
    refine ⟨⟨hs,hb.le⟩, fun i hi he => (key i hi he _).2, ?_,
      fun i hi he => (hC.ships i hi he).tunes _, fun i hi he => (hC.ships i hi he).debt _,
      hzero, ?_⟩
    · intro i _ _
      let q := (C.path.levels.clock.op i p).ratio
      change 0 = q.parent 0
      have hz := q.embed_parent 0
      rw [embed_origin] at hz
      exact hz.symm
    · change (A b).cost X (-z) ≤ _
      change _ ≤ 2*fee + _*(2*fee + σ ((A b).bar X (-z)).x)
      rw [hTop]
      exact (origin.2 (-z)).2.2
  have hbudget := Work.G09.answer W C.path h.costs.cost h.costs.back N p d s b
    (C.labels.level d) (C.localSection d) C.params P (2*fee)
    (mul_nonneg zero_le_two (rem_nonneg hr)) woke
  have he (i : ℕ) (hi : s ≤ i) (he : i < b) :
      Θ i (P.voice i) = transition (C := C) d N p i (Θ (i+1) (P.voice (i+1))) :=
    (hC.ships i hi he).debt (-z)
  have hval : credit C N p d f b hb.le = Θ b Q :=
    Fleet.keeps C N p d b J H f hf (hJ.trans htb) hb.le _ Q ⟨hq,hr⟩ hfull
  have hbase : Θ b (P.voice b) = credit C N p d f b hb.le + V b (-z) := by
    have hplays : (C.factory d N p).entries b (-z) = (X.tone b).plays (-z) := by
      rw [show (C.factory d N p).entries = (X.draft C.path).inits from hX]
      rfl
    change Θ b ((A b).bar X (-z)) = _
    rw [hval, hTop]
    change _ = Θ b Q + Θ b ((C.factory d N p).entries b (-z))
    rw [hplays]
    exact (origin.2 (-z)).2.1
  have lex (i : ℕ) (hsi : s ≤ i) (hib : i ≤ b) :
      credit C N p d f i (hib.trans hb.le) = Θ i (P.voice i) + V i z := by
    induction hib using Nat.decreasingInduction with
    | self =>
      have zeroPair : V b (-z)+V b z = 0 := by
        rw [←cal_add d N p b H (ho.post.trans hsi) hb.le, neg_add_cancel,
          zero_cal d N p b H (ho.post.trans hsi) hb.le]
      rw [hbase, add_assoc, zeroPair, add_zero]
    | of_succ i hib ih =>
      have hsi' := hsi.trans i.le_succ
      have hN := hib.trans_le hb.le
      have hP : reads d N p (i+1) (P.voice (i+1)) (P.cost (i+1)) := (key _ hsi' hib _).2
      rw [credit_step C N p d f hf hN, ih hsi',
        transition_add d N p (u := Θ (i+1) (P.voice (i+1))) (v := V (i+1) z)
          (message d N p _ H (ho.post.trans hsi') hN hP)
          (message d N p _ H (ho.post.trans hsi') hN (entryOk d N p _ H (ho.post.trans hsi') hN z)),
        ←he i hsi hib, ←factory_eq d N p i H (ho.post.trans hsi) hN z]
  refine ⟨P.voice,P.cost,hzero,he,?_,?_⟩
  · intro i hsi hib
    have hP : reads d N p i (P.voice i) (P.cost i) := (key i hsi hib _).2
    have hz := entryOk d N p i H (ho.post.trans hsi) (hib.trans hb.le) z
    refine ⟨hP,lex i hsi hib,⟨_,_,presentation hP.1 hP.2 hz.1 hz.2,?_⟩,hbudget i hsi hib⟩
    exact (lex i hsi hib).trans
      (plus (H.wilson.represents _ _ _ (hib.trans hb.le)).good hP.2 hz.2 (C.localSection d)).symm
  · have hP : reads d N p s (P.voice s) (P.cost s) := (key s le_rfl hs _).2
    have hpage := (WholeCaptureTransport.read_signed C N p d H ho (hs.trans hb.le)
      z hP (lex s le_rfl hs)).2.1
    have hwrap := measured_diff d N p s H ho.post (hs.trans hb.le) hP
    rw [hzero, sub_zero] at hwrap
    change σ (measuring C d N p s (_ - z)) ≤ _
    rw [hpage]
    have hp := hbudget s le_rfl hs
    have hzeroSize : σ (P.voice s).x = 0 := by simp [hzero,Frame.coeffSize]
    rw [hzeroSize,add_zero,mul_comm] at hp
    have hprice := (le_div_iff₀ (Real.exp_pos _)).mpr hp
    exact hwrap.trans (mul_le_mul_of_nonneg_left hprice (invoice_nn d p s))

/-- Every whole original product source yields a paid signed trajectory all
the way down to its named stop. -/
theorem transported_stop (ho : Opened C d s p) (f : Cut C N p) (hf : Continuous f)
    {cap price : ℝ} (B : C.label d)
    (source : OriginalProductCellMatch.SourceAt C N b p d J h s ho.post f cap price B) :
    ∃ (hb : b < N) (hs : s ≤ b) (fee : ℝ),
      Retained C N b p d s H ho hs hb f B (4*(1+stock C b)*(2*fee)) := by
  obtain ⟨stocked,opened,hst,htb,hb,width,fee,E,Q,_,_,_,hq,hr,hsize,hfull,ht⟩ := source
  exact ⟨hb,hst.trans htb,fee,
    from_model C N b p d J s H h ho f hf B stocked opened.1 hst htb hb width fee E Q
      hq hr hsize hfull ht⟩

end YM.Integration.WholeProductCapture
