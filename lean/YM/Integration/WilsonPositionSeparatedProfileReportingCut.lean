import YM.Integration.WilsonPositionSeparatedProfileTranslatedTest

/-! A source enrolled at a fixed physical reporting date, with the original
Wilson action still regulated at an independently later cutoff. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileReportingCut
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Extra.Histories
open OPE.Therm RG05Readout Address Native Harvest RG05Readout.Records MergeProof Accent
open private branch from YM.Integration.WilsonPositionSeparatedProfileTranslatedMass
open scoped Classical BigOperators Topology
variable {G : Gauge} (C : Family G) (law : C.Makes) (N per : ℕ) {n u h : ℕ}

def lower (n : ℕ) (F : Bin G (C.side (n+1) per)) (u : ℕ) (span : u≤n) : Bin G (C.side u per) :=
  Nat.decreasingInduction (motive:=fun i _=>Bin G (C.side i per)) (fun i _=>journey C per i N 0)
    (journey C per n N 0 F) span

def stock (date : n+1≤h) (X : Goods G (C.side h per)) : Bin G (C.side (n+1) per) :=
  fun _=>gust C.path N per h (fun V=>(C.path.rep N per h).eval V • X V) (n+1) date

def field (date : n+1≤h) (span : u≤n) (X : Goods G (C.side h per)) (g : Body)
    (V : Config G (C.side u per)) : ℂ :=
  lower C N per n (stock C N per date X) u span g V/((C.path.rep N per u).eval V:ℂ)

private theorem charged {A : ℂ} (F : Bin G (C.side (n+1) per)) (live : BLight F)
    (invoice : ∀g,(∫X,F g X ∂prior G _)=A) (span : u≤n) :
    BLight (lower C N per n F u span) ∧ ∀g,(∫X,lower C N per n F u span g X ∂prior G _)=A := by
  induction span using Nat.decreasingInduction with
  | self =>
    rw [show lower C N per n F n le_rfl=journey C per n N 0 F from Nat.decreasingInduction_self ..]
    exact ⟨sailed F live,branch C N per n F live invoice⟩
  | of_succ k hk ih =>
    rw [show lower C N per n F k hk.le=journey C per k N 0 (lower C N per n F (k+1) hk)
      from Nat.decreasingInduction_succ_left ..]
    exact ⟨sailed _ ih.1,branch C N per k _ ih.1 ih.2⟩

include law in
theorem measured (high : h≤N) (date : n+1≤h) (span : u≤n) (X : Goods G (C.side h per))
    (budget : Integrable (fun V=>(C.path.rep N per h).eval V • X V) (prior G _)) (g : Body) :
    Integrable (field C N per date span X g) (scene C.path N per u) ∧
      (∫V,field C N per date span X g V ∂scene C.path N per u)=(∫V,X V ∂scene C.path N per h) := by
  let Q := stock C N per date X
  let raw := lower C N per n Q u span g
  have funds : BLight Q := fun _=>gust_live C.path N per h _ budget date
  have initial : ∀f,(∫V,Q f V ∂prior G _)=(∫V,(C.path.rep N per h).eval V • X V ∂prior G _) :=
    fun _=>gust_sum C.path N per h _ budget date
  have bank:=charged C N per Q funds initial span
  have reach : u≤N:=span.trans ((Nat.le_succ _).trans (date.trans high))
  have cancel (V : Config G (C.side u per)) :
      (C.path.rep N per u).eval V • field C N per date span X g V=raw V := by
    change (C.path.rep N per u).eval V • (raw V/((C.path.rep N per u).eval V:ℂ))=raw V
    rw [Complex.real_smul,←mul_div_assoc,mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr
      (Multi.AxisShift.chosen_positive law.wilson reach V).ne')]
  constructor
  · apply actualScene_integrable_of_weighted C law reach
    simpa only [cancel] using bank.1 g
  · rw [actualScene_formula C law reach,actualScene_formula C law high]
    simp_rw [cancel]
    exact congrArg (_ • ·) (bank.2 g)

private theorem stacked {k j i : ℕ} (down : i≤j) (top : j≤k) (X : Goods G (C.side k per)) :
    gust C.path N per j (gust C.path N per k X j top) i down=gust C.path N per k X i (down.trans top) := by
  induction down using Nat.decreasingInduction with
  | self => exact gust_base ..
  | of_succ l hl ih => rw [gust_step _ _ _ _ _ hl,ih,gust_step _ _ _ _ X (hl.trans_le top)]

include law in
theorem authentic (high : h≤N) (date : n+1≤h) (span : u≤n) (X : C(Config G (C.side N per),ℂ)) (g : Body) :
    field C N per date span (actualTransport C (N:=N) (fun U=>X U) high) g=
      WilsonPositionSeparatedProfileTranslatedTest.field C (date.trans high) span X g := by
  let A : Goods G (C.side N per):=fun V=>(C.path.rep N per N).eval V • X V
  have account : (fun V=>(C.path.rep N per h).eval V • actualTransport C (N:=N) (fun U=>X U) high V)=
      gust C.path N per N A h high := funext (actualTransport_unnormalize C law le_rfl (fun U=>X U) high)
  have birth : stock C N per date (actualTransport C (N:=N) (fun U=>X U) high)=
      arises C per N n (date.trans high) (fun _=>X) := by
    funext f
    unfold stock
    rw [account,stacked C N per date high]
    simp only [arises,RG05Readout.Records.dyes,A,Complex.real_smul]
  unfold field
  rw [birth]
  rfl

end YM.Integration.WilsonPositionSeparatedProfileReportingCut
