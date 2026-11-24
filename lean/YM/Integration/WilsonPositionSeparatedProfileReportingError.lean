import YM.Integration.WilsonPositionSeparatedProfileReportingVariation

/-! The full earlier Wilson census of an ultraviolet insertion compared against
an independent field entered at a fixed, later reporting date. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileReportingError
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Extra.Histories
open OPE.Therm RG05Readout Address Native Harvest RG05Readout.Records MergeProof Accent
open WilsonPositionSeparatedProfileReportingCut
open scoped Classical BigOperators Topology
variable {G : Gauge} (C : Family G) (law : C.Makes) (N per : ℕ)

private theorem gust_sub {h j : ℕ} (date : j≤h) (F H : Goods G (C.side h per))
    (f : Integrable F (prior G _)) (g : Integrable H (prior G _)) :
    gust C.path N per h (F-H) j date=gust C.path N per h F j date-gust C.path N per h H j date := by
  induction date using Nat.decreasingInduction with
  | self => rw [gust_base,gust_base,gust_base]
  | of_succ i hi ih =>
    rw [gust_step _ _ _ _ _ hi,gust_step _ _ _ _ F hi,gust_step _ _ _ _ H hi,ih]
    funext V
    simp only [StepData.push,Pi.sub_apply,smul_sub]
    exact integral_sub (StepData.push_slice (C.path.levels.transition_mass ..) _ _ (gust_live _ _ _ _ _ f hi))
      (StepData.push_slice (C.path.levels.transition_mass ..) _ _ (gust_live _ _ _ _ _ g hi))

private theorem branch {k : ℕ} (F H : Bin G (C.side (k+1) per)) (f : BLight F) (h : BLight H) :
    journey C per k N 0 (F-H)=journey C per k N 0 F-journey C per k N 0 H := by
  calc journey C per k N 0 (F-H)=journey C per k N 0 (F+(-1:ℂ)•H) := by rw [neg_one_smul,sub_eq_add_neg]
       _ = journey C per k N 0 F+journey C per k N 0 ((-1:ℂ)•H) := sail_plus f (fun g=>(h g).smul (-1:ℂ))
       _ = _ := by rw [sail_pitch,neg_one_smul,sub_eq_add_neg]

private theorem descent {n u : ℕ} (span : u≤n) (F H : Bin G (C.side (n+1) per)) (f : BLight F) (h : BLight H) :
    BLight (lower C N per n F u span) ∧ BLight (lower C N per n H u span) ∧
    lower C N per n (F-H) u span=lower C N per n F u span-lower C N per n H u span := by
  induction span using Nat.decreasingInduction with
  | self =>
    have base (X : Bin G (C.side (n+1) per)):lower C N per n X n le_rfl=journey C per n N 0 X:=Nat.decreasingInduction_self ..
    simp only [base]; exact ⟨sailed _ f,sailed _ h,branch C N per F H f h⟩
  | of_succ i hi ih =>
    have step (X : Bin G (C.side (n+1) per)):lower C N per n X i hi.le=journey C per i N 0 (lower C N per n X (i+1) hi):=Nat.decreasingInduction_succ_left ..
    simp only [step,ih.2.2];exact ⟨sailed _ ih.1,sailed _ ih.2.1,branch C N per _ _ ih.1 ih.2.1⟩

private theorem subtract {n u h : ℕ} (date : n+1≤h) (span : u≤n) (F H : Goods G (C.side h per))
    (f : Integrable (fun V=>(C.path.rep N per h).eval V • F V) (prior G _))
    (g : Integrable (fun V=>(C.path.rep N per h).eval V • H V) (prior G _)) (b : Body) :
    field C N per date span (F-H) b=field C N per date span F b-field C N per date span H b := by
  let raw (X : Goods G (C.side h per)):=fun V=>(C.path.rep N per h).eval V • X V
  have sample : raw (F-H)=raw F-raw H:=by funext V; exact smul_sub _ _ _
  have birth : stock C N per date (F-H)=stock C N per date F-stock C N per date H := by
    funext body V
    change gust C.path N per h (raw (F-H)) _ date V=_
    rw [sample,gust_sub C N per date _ _ f g]
    rfl
  have op:=(descent C N per span (stock C N per date F) (stock C N per date H)
    (fun _=>gust_live _ _ _ _ _ f date) (fun _=>gust_live _ _ _ _ _ g date)).2.2
  funext V
  change lower C N per n (stock C N per date (F-H)) u span b V/_=
    lower C N per n (stock C N per date F) u span b V/_-lower C N per n (stock C N per date H) u span b V/_
  rw [birth,op]
  exact sub_div _ _ _

include law in
theorem original {h n u : ℕ} (issued : h≤N) (date : n+1≤h) (span : u≤n)
    (X : C(Config G (C.side N per),ℂ)) (Y : Goods G (C.side h per))
    (y : Integrable (fun V=>(C.path.rep N per h).eval V • Y V) (prior G _)) (g : Body) :
    (∫V,‖WilsonPositionSeparatedProfileTranslatedTest.field C (date.trans issued) span X g V-
        field C N per date span Y g V‖ ∂scene C.path N per u)≤
      ∫W,‖actualTransport C (N:=N) (fun U=>X U) issued W-Y W‖ ∂scene C.path N per h := by
  let Z:=actualTransport C (N:=N) (fun U=>X U) issued
  have z : Integrable (fun V=>(C.path.rep N per h).eval V • Z V) (prior G _) :=
    actualTransport_weighted_integrable_of_integrable C law le_rfl
      (by simpa only [Complex.real_smul] using (dye_grow (p:=per) (N:=N) law X.continuous)) issued
  have both:Integrable (fun V=>(C.path.rep N per h).eval V • (Z-Y) V) (prior G _) := by
    simp only [Pi.sub_apply,smul_sub];exact z.sub y
  have bill:=WilsonPositionSeparatedProfileReportingVariation.original C law N per issued date span (Z-Y) both g
  rw [subtract C N per date span Z Y z y g] at bill
  rw [←authentic C law N per issued date span X g]
  exact bill

end YM.Integration.WilsonPositionSeparatedProfileReportingError
