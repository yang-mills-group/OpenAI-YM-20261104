import YM.Integration.WilsonPublicOutputFrame
import YM.Integration.WilsonMSDictionaryVector

/-! Smooth ordinary OPE on a single moving exterior panel. Both displayed scalar
rows are actual unselected ordinary readings. The formal experiment is evaluated
at its own finite outer cutoff before its normalized independent limit. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPublicOutputSmooth
open Filter Set MeasureTheory Table Spec RG17 OPE OPE.Orbits PhysMS Trace.Pilot Climb
open FVA2 FVA2.Register FVA2.Scale FVA2.O FVA2.O.Score FVA2.O.Project
open Maxwell XSpace XSpace.Normalize MS MS.Land MS.Fleet MS.Theater
open RG12 SharpGram OPE.Log PhysicalNext.Repeat.Legato
open WilsonPositionHomogeneousFrame WilsonMacroscopicRichTwoDatePivot
open WilsonMatrixTicketLanesSmearedPivot WilsonMacroscopicRichPositionRows
open WilsonMacroscopicRichSignedAmplitude WilsonMSDictionaryVector
open private price from YM.Integration.WilsonPublicOutputDetector
open scoped Classical Topology BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (J : ℝ → tower S) (Z : WilsonPrescription G)

def exterior {h:ℕ} (B : Profiles R h) (w : B.probes.index → Atom (R:=R) h)
    (issued : ∀ j, B.probes.shell j = WilsonMatrixTicketLanesTwoSites.shell R.family.book.grid h (w j))
    {t:ℝ} (tp:0<t) (j:B.probes.index) : External R.family S :=
  stencil J (profile (B.probes.shell j) (w j) (issued j) (test B j)) tp
    ⟨h,active F J Z t h ((Bel R.family.book).project h (w j))⟩

theorem charge {h:ℕ} (B : Profiles R h) (w : B.probes.index → Atom (R:=R) h)
    (issued : ∀ j, B.probes.shell j = WilsonMatrixTicketLanesTwoSites.shell R.family.book.grid h (w j))
    {t:ℝ} (tp:0<t) (y:S.Field h) (j:B.probes.index) :
    (exterior F J Z B w issued tp j).charge F h y = row F J Z B t y j := by
  let X := exterior F J Z B w issued tp j
  let φ := profile (B.probes.shell j) (w j) (issued j) (test B j)
  let u := homogeneous F J Z t h ((Bel R.family.book).project h (w j))
  change (Next.UVStress.dilate tp φ).applyTo (X.pay h y) =
    WilsonMatrixTicketLanesSmearedRows.observation F J Z _ _ t h y
  rw [WilsonMacroscopicRichPositionRows.output F J Z _ (w j) (issued j) _ tp y, Next.UVStress.zoom_integral]
  apply integral_congr_ae
  filter_upwards with z
  by_cases hz : z ∈ tsupport φ
  · have val := X.pay_eq F h y (t • z) (Work.A05.smul_conf tp (φ.tsupport_subset hz))
    apply congrArg (φ z * ·)
    refine val.trans ?_
    have tags : X.tags = fun _ => ⟨h, u⟩ := by
      funext k
      change (⟨h,J t h (active F J Z t h ((Bel R.family.book).project h (w j)))⟩ : S.Tag) = ⟨h,u⟩
      rw [WilsonMacroscopicRichPositionRows.far F J Z B w t j]
    rw [tags]
    let V : Fin 2 → S.Tag := Fin.cons ⟨h,y⟩ (fun _ => ⟨h,u⟩)
    change S.read (t • z) (fun i=>⟨(V i).1,S.representative _ (V i).2⟩) = _
    apply congrArg (S.read (t • z))
    funext i
    fin_cases i <;> rfl
  · change φ z * _ = φ z * _
    rw [image_eq_zero_of_notMem_tsupport hz, zero_mul, zero_mul]

variable (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (ν:ℝ)
    {simple:G.Simple} {σ:Prescription (Press.portDeck G)} {branch:Bool} (ms:Main.Match Z simple M σ branch)

/-- Buy the physical spatial row once, then compare each of these very same moving
exterior two-site readings with the finite independent experiment at its true order. -/
theorem original {Y : (Bel R.family.book).Hierarchy}
    (lead : Leading F J) (owed : ∀ d, ∀ᶠ r in trail, Frame.obedient F Y (J r) d)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (fac : Facilities R.family f S) {l : Filter (ℕ×ℕ)} [l.NeBot] (lo : l ≤ f.fuse)
    (bill : MatrixTicket (C:=R.family) S F.sector.derivatives l) (h : ℕ) :
    LogTrace F Q.port ∧
    ∃ B : Profiles R h, ∃ w : B.probes.index → Atom (R:=R) h,
    ∃ issued : ∀ j, B.probes.shell j = WilsonMatrixTicketLanesTwoSites.shell R.family.book.grid h (w j),
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (g:ℝ→ℝ), Coupling G g → ∀ P E A : ℕ, P+E ≤ A →
    ∀ᶠ r in trail, let t:=r/((g r)^A)^2
    ∃ tp : 0<t, ∀ (n:ℕ) (d:Fin n→ℕ) (v:(i:Fin n)→RG17.Free R.family (d i))
      (ψ:Test n) (q:ℕ) (C D:ℝ), 0≤C →
      let pub:=homogeneous F J Z r
      let a:=fun i=>pub (d i) (v i)
      let physical:=RG17.basket Q h (d:=d) a r ψ
      let X:=exterior F J Z B w issued tp
      let obs:=fun j=>RG17.appeared F (d:=d) a (X j) r ψ
      let bank:=((ms.separatedOPE ν).wilson.light h).choose
      let value:=fun s=>experiment R.family d h Z M ν v ψ bank q (g r) s
      ‖(fun j=>(X j).charge F h physical) - obs‖ ≤ C*(((g r)^A)^2)^(h+1)/(g r)^E →
      (∃ᶠ s:ℝ in atTop, ‖obs-(fun j=>(X j).charge F h (pub h (value s)))‖
        ≤ D*(g r)^(P+A*(2*h+1))) →
      (∃ᶠ s:ℝ in atTop, ‖(pub h).symm physical-value s‖ ≤ K*(C+D)*(g r)^P) ∧
      ‖(pub h).symm physical-prediction R.family d h Z M ν v ψ q (g r)‖
        ≤ K*(C+D)*(g r)^P := by
  refine ⟨OPE.tickets_suffice F fac lo bill Q.spans,?_⟩
  obtain ⟨B,two,invert⟩ := WilsonMacroscopicRichTwoDatePivot.original F J Z lead owed simple h
  choose w issued using two
  obtain ⟨K,kp,decoder⟩ := invert (1/2) (by norm_num)
  refine ⟨B,w,issued,2*K,by positivity,?_⟩
  intro g hg P E A room
  have tends : Tendsto (fun r=>r/((g r)^A)^2) trail trail := by
    have eq : (fun r=>r/((g r)^A)^2) = WilsonThermometerWeakPairClock.scale g (A*2) :=
      funext fun r => by rw [WilsonThermometerWeakPairClock.scale,pow_mul]
    rw [eq]
    exact WilsonThermometerWeakPairClock.small simple g hg (A*2)
  filter_upwards [tends.eventually decoder,WilsonPublicOutputFrame.normalized F J Z lead owed simple h,
    hg.positive,length_rate.pos,(hg.conforms simple).eventually (ge_mem_nhds zero_lt_one)] with r read normed gp rp cap
  intro t
  have sp:=pow_pos (pow_pos gp A) 2
  have tp:0<t:=div_pos rp sp
  have window : ((g r)^A)^2 ∈ Ioc (0:ℝ) 1 :=
    ⟨sp,pow_le_one₀ (pow_nonneg gp.le _) (pow_le_one₀ gp.le cap)⟩
  have eq : ((g r)^A)^2*t=r := by dsimp only [t]; field_simp [sp.ne']
  refine ⟨tp,?_⟩
  intro n d v ψ q C D cp pub a physical X obs bank value sharp signed
  have measured (y:S.Field h) : (fun j=>(X j).charge F h y) = row F J Z B t y :=
    funext fun j=>charge F J Z B w issued tp y j
  rw [measured] at sharp
  let W:=A*(2*h+1)
  have wp:=pow_pos gp W
  have finite : ∃ᶠ s:ℝ in atTop, ‖(pub h).symm physical-value s‖≤(2*K)*(C+D)*(g r)^P := by
    refine signed.mono fun s sub=>?_
    rw [measured] at sub
    let y:=pub h (value s)
    have bound:=read _ window (physical-y)
    rw [eq,price gp A h,(row F J Z B t).map_sub] at bound
    have amount := (norm_sub_le_norm_sub_add_norm_sub _ obs _).trans (add_le_add sharp sub)
    have charged : (g r)^W*‖(J r h).symm (physical-y)‖ ≤
        K*(C*(((g r)^A)^2)^(h+1)/(g r)^E + D*(g r)^(P+W)) := by
      calc _ ≤ (g r)^W*(K*((g r)^W)⁻¹*‖row F J Z B t physical-row F J Z B t y‖) :=
              mul_le_mul_of_nonneg_left bound wp.le
           _ = K*‖row F J Z B t physical-row F J Z B t y‖ := by field_simp [wp.ne']
           _ ≤ _ := mul_le_mul_of_nonneg_left amount kp
    have result:=WilsonPublicOutputDetector.powers gp cap kp cp P E A h room charged
    have trueField:=normed (physical-y)
    change ‖(pub h).symm (physical-y)‖ ≤ 2*_ at trueField
    rw [map_sub,show (pub h).symm y=value s from LinearEquiv.symm_apply_apply ..] at trueField
    exact trueField.trans ((mul_le_mul_of_nonneg_left result (by norm_num : 0≤(2:ℝ))).trans_eq (by ring))
  have ready : Read.Detected (Measure.outlook Z.scheme Z.criterion) bank :=
    ((ms.separatedOPE ν).wilson.light h).choose_spec.2
  have limit:=experiment_limit R.family d h Z M ν v ψ ms bank ready q (g r)
  exact ⟨finite,le_of_tendsto_of_frequently ((tendsto_const_nhds (x:=(pub h).symm physical)).sub limit).norm finite⟩
end YM.Integration.WilsonPublicOutputSmooth
