import YM.Integration.ManuscriptQLocalPrepared
import YM.LocalTaylorR2.Reel.Harmony

/-! Physical continuation of all ordinary activities on one unchanged
register, including every compulsory row and full independent Marked Taste. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ManuscriptQLocalOrdinaryScale
open Finset Function Filter Lattice Wilson RG Tree Precision Marker
open Overlay RG3.Forms RG3.Script.Picnic Push Push.AbsoluteSums
open AnalyticBridge ConnectedActivityE6 Comparison.RG02
open Pressure Pressure.Stores
open scoped BigOperators Classical

variable {G : Gauge} {f c : Side} {V X : Type} [DecidableEq V] [Fintype V]
    {Γ : Census V} {o : V→Site f} {S : StepData c f} {T : Tube G S}
    (Y : Rep G f)

def activities (t : ℝ) : Activities G f :=
  {Y.activities with E:=fun i=>t • Y.activities.E i}

def carrier (t : ℝ) : Rep G f := {Y with activities:=activities Y t}

omit [Fintype V] [DecidableEq V] in
theorem lane (t : ℝ) (i : ℕ) (U : Config G f) :
    (carrier Y t).activities.regularOccurrence Y.p i U =
      t*Y.activities.regularOccurrence Y.p i U := by
  change masked Y.p.threshold (Y.activities.reg i).support (t • Y.activities.E i) U =
    t * masked Y.p.threshold (Y.activities.reg i).support (Y.activities.E i) U
  by_cases h : Healthy Y.p.threshold (Y.activities.reg i).support U
  · rw [masked_eq _ _ _ _ h, masked_eq _ _ _ _ h]
    rfl
  · rw [masked_ne _ _ _ _ h, masked_ne _ _ _ _ h, mul_zero]

omit [Fintype V] [DecidableEq V] in
theorem ordinary (t : ℝ) (U : Config G f) :
    (carrier Y t).activities.additive Y.p U=t*Y.activities.additive Y.p U := by
  unfold Activities.additive
  simp_rw [lane Y t _ U]
  rw [tsum_mul_left]

omit [Fintype V] [DecidableEq V] in
theorem gas (t : ℝ) (U : Config G f) :
    (carrier Y t).activities.gas Y.p U=Y.activities.gas Y.p U := rfl

omit [Fintype V] [DecidableEq V] in
theorem exponent (t : ℝ) (U : Config G f) :
    (carrier Y t).exponent U=(1-t)*Y.activities.additive Y.p U+Y.exponent U := by
  change _-_- (carrier Y t).activities.additive Y.p U=
    (1-t)*Y.activities.additive Y.p U+(_-_-Y.activities.additive Y.p U)
  rw [ordinary]
  dsimp only [carrier]
  ring

omit [Fintype V] [DecidableEq V] in
theorem vacuum (t : ℝ) (U : Config G f) :
    (carrier Y t).eval U=Real.exp ((1-t)*Y.activities.additive Y.p U)*Y.eval U := by
  unfold Rep.eval
  rw [exponent,Real.exp_add]
  change _ * _ * Y.activities.gas Y.p U = _ * (_ * Y.activities.gas Y.p U)
  ring

omit [Fintype V] [DecidableEq V] in
theorem bound {e t : ℝ} (h : Y.activities.EBound Y.p e) (ht : |t|≤1) :
    (carrier Y t).activities.EBound Y.p e := by
  obtain ⟨b,hb,hs⟩:=h
  refine ⟨b,fun i=>?_,hs⟩
  have hh:=CouplingShape.sup_scale t (hb i)
  exact ⟨(hb i).1,fun U hu l hl hl' =>(hh.2 U hu l hl hl').trans
    (mul_le_of_le_one_left (hb i).1 ht)⟩

omit [Fintype V] [DecidableEq V] in
theorem valid {e k t : ℝ} (h : Y.activities.Valid Y.p e k) (ht : |t|≤1) :
    (carrier Y t).activities.Valid Y.p e k := by
  refine ⟨⟨fun i=>CouplingShape.reg_scale t (h.regular.smooth i),?_,?_⟩,
    ⟨h.forced.sym, h.forced.symtest, h.forced.meas, h.forced.meas_test,
      h.forced.reads, h.forced.reads_test, h.forced.permit⟩, ?_, bound Y h.boundE ht, h.boundK⟩
  · intro i
    change t*Y.activities.E i 1=0
    rw [h.regular.at_flat,mul_zero]
  · intro i hN u v hu hv
    rw [show (carrier Y t).activities.E i=t•Y.activities.E i from rfl,
      LocalTaylorR2.Reel.hess_scale t (h.regular.smooth i),
      h.regular.vanish i hN u v hu hv,mul_zero]
  · intro s b
    obtain ⟨r⟩:=h.moves s b
    exact ⟨⟨r.ep,r.kp,r.reg_site,r.reg_support,r.forced_support,r.forced_inventory,r.forced_tests,
      fun i U=>congrArg (fun y:ℝ=>t*y) (r.valuesE i U),r.valuesK⟩⟩

omit [Fintype V] [DecidableEq V] in
theorem intake {P : Teller G} {x t : ℝ} (h : Intake P T x Y) (ht : |t|≤1) :
    Intake P T x (carrier Y t) where
  ready:=h.ready
  received:=⟨h.received.path,h.received.clip,h.received.temp⟩
  cap:=⟨h.cap.paths,valid Y h.cap.labels ht⟩
  exponent:=h.exponent
  height:=h.height
  sizes:=h.sizes
  window:=h.window

def tasted (t : ℝ) (M : Taste X o Y Γ) : Taste X o (carrier Y t) Γ where
  menu:=⟨M.menu.origins,M.menu.rays,M.menu.branch,M.menu.marks,
    M.menu.global,M.menu.regular,M.menu.force⟩
  root:=M.root
  tag:=M.tag
  site:=M.site
  score:=M.score

theorem stored (t : ℝ) (M : Taste X o Y Γ) (x : X) (U : Config G f) :
    (((tasted Y t M).leaf x).log U=(M.leaf x).log U) ∧
    (((tasted Y t M).leaf x).contents.cluster U=(M.leaf x).contents.cluster U) :=
  ⟨rfl,rfl⟩

theorem marked (t : ℝ) (M : Taste X o Y Γ) (x : X) (U : Config G f) :
    ((tasted Y t M).leaf x).density U=
      (Real.exp ((1-t)*Y.activities.additive Y.p U):ℂ) • (M.leaf x).density U := by
  unfold Deck.density
  rw [(stored Y t M x U).1,(stored Y t M x U).2,exponent,Real.exp_add,
    Complex.ofReal_mul,smul_smul]

theorem pushed (t : ℝ) (M : Taste X o Y Γ) (x : X) (V' : Config G c) (s : Γ.Mode) :
    (Actual.Push S Y.beta (((tasted Y t M).leaf x).density) V').part s =
      S.push Y.beta (fun U=> (Real.exp ((1-t)*Y.activities.additive Y.p U):ℂ) *
        ((M.leaf x).density U).part s) V' := by
  rw [show (Actual.Push S Y.beta (((tasted Y t M).leaf x).density) V').part s =
    S.push Y.beta (Actual.atMark s (((tasted Y t M).leaf x).density)) V' from
    congrFun (Actual.grades ..) s]
  congr 1
  funext U
  change (((tasted Y t M).leaf x).density U).part s=_
  rw [marked,Poly.part_smul]

end YM.Integration.ManuscriptQLocalOrdinaryScale
end
