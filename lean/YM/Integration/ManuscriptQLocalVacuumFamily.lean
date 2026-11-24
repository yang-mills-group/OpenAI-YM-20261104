import YM.Integration.ManuscriptQLocalVacuumRadius
import YM.Integration.QLocalInheritedPhysicalInlet

/-!
# Physical marked measure of the enlarged old vacuum roster

The baseline retains all measured compulsory channels.  The added genuine curvature
entries use their own old supports and nominal powers.  At auxiliary argument one
the remaining physical multiplier is precisely the submitted calibration.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ManuscriptQLocalVacuumFamily
open Function Filter Lattice Wilson RG Marker Overlay RG3.Forms RG3.Held RG3.Script.Picnic
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open ManuscriptQLocalVacuumRadius
open scoped Topology BigOperators Classical

variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V}
  {X : Type} {o : V→Site n}

def source (Y : Rep G n) (S : List (Piece G n)) (g z : ℝ) : Rep G n :=
  let E:=Render.adorn (weight g z) Y.activities S
  {Y with activities:=⟨E.reg,Y.activities.forced,E.E,Y.activities.K⟩}

theorem actual (Y : Rep G n) (S : List (Piece G n)) (g z : ℝ) :
    source Y S g z=Render.append S Y (weight g z) := by
  let E:=Render.adorn (weight g z) Y.activities S
  have h:=ManuscriptQLocalVacuumRadius.forced g z Y.activities S
  have hE:(⟨E.reg,Y.activities.forced,E.E,Y.activities.K⟩:Activities G n)=E :=
    congrArg₂ (fun f k=>(⟨E.reg,f,E.E,k⟩:Activities G n)) h.1.symm h.2.symm
  exact congrArg (fun A=>{Y with activities:=A}) hE

def carry (Y : Rep G n) (S : List (Piece G n)) (g z : ℝ) (T : Taste X o Y Γ) :
    Taste X o (source Y S g z) Γ where
  menu:=⟨T.menu.origins,T.menu.rays,T.menu.branch,T.menu.marks,T.menu.global,T.menu.regular,T.menu.force⟩
  root:=T.root
  tag:=T.tag
  site:=T.site
  score:=T.score

omit [Fintype V] in
theorem active (Y : Rep G n) (S : List (Piece G n)) (g z : ℝ) (T : Taste X o Y Γ)
    (x : X) (h : (T.leaf x).Active) : ((carry Y S g z T).leaf x).Active :=
  ⟨⟨h.articles.proper,h.articles.pins,h.articles.regular,h.articles.occurs,h.articles.retained,
    h.articles.inspects,h.articles.keeps,h.articles.meas,h.articles.invi⟩,h.captions⟩

def budget (Y : Rep G n) (S : List (Piece G n)) (g z : ℝ) (T : Taste X o Y Γ)
    {p : BudgetPoint} {w : V→ℝ} {κ a b : ℝ} (h : FullBudget p T w κ a b) :
    FullBudget p (carry Y S g z T) w κ a b where
  white:=h.white
  black:=h.black
  gold:=h.gold
  unitBound:=h.unitBound
  active x:=active Y S g z T x (h.active x)
  radii:=h.radii
  divisor:=h.divisor
  white_nonnegative:=h.white_nonnegative
  regular i:=⟨(h.regular i).controls⟩
  regular_law:=h.regular_law
  black_nonnegative:=h.black_nonnegative
  forced:=h.forced
  gold_nonnegative:=h.gold_nonnegative
  caption:=h.caption
  unit_nonnegative:=h.unit_nonnegative
  unit:=h.unit
  regularTotal:=h.regularTotal
  forcedTotal:=h.forcedTotal

theorem exponent (Y : Rep G n) (S : List (Piece G n)) (g z : ℝ)
    {d k : ℝ} (hp : Render.permits S Y.p) (hY : Y.activities.Valid Y.p d k) (U : Config G n) :
    (source Y S g z).exponent U=Y.exponent U-Render.renders (weight g z) Y.p U S := by
  rw [actual]
  change Y.v*_-Y.path.inChannels Y.clip Y.p Y.beta U-
    (Render.append S Y (weight g z)).activities.additive Y.p U=_
  rw [Render.additive (weight g z) hp hY U]
  unfold Rep.exponent
  ring

theorem density (Y : Rep G n) (S : List (Piece G n)) (g z : ℝ)
    {d k : ℝ} (hp : Render.permits S Y.p) (hY : Y.activities.Valid Y.p d k)
    (T : Taste X o Y Γ) (x : X) (U : Config G n) :
    ((carry Y S g z T).leaf x).density U=
      (Real.exp (-Render.renders (weight g z) Y.p U S):ℂ) • (T.leaf x).density U := by
  have hl:((carry Y S g z T).leaf x).log U=(T.leaf x).log U:=rfl
  have hc:((carry Y S g z T).leaf x).contents.cluster U=(T.leaf x).contents.cluster U:=by
    apply tsum_congr
    intro b
    rfl
  unfold Deck.density
  rw [hl,hc,exponent Y S g z hp hY,sub_eq_add_neg,Real.exp_add,Complex.ofReal_mul,smul_smul,mul_comm]

variable {C : Family G} {J : Request V} {A : NumericSchedule C J} {d : LocalFormal.Datum C Γ}
  {F : AnalyticInput J A d} {η : ℝ} (I : FullPreparedInputAt F η)
local notation "Y₁" => QLocalInheritedPhysicalInlet.rep I
local notation "g₁" => Pert.Asymptotics.regulatorRun C d.cutoff d.period (d.level+1)

/-- Simultaneous unmarked and marked costs on the true original inlet. The
complete submitted K still has its original physical budget at that level. -/
theorem bought (hi : Retained.NativeIntake I) (z : ℝ) :
    ((source Y₁ F.layers g₁ z).activities.Valid (A.inputNorm d.level)
      (I.inherited+bill F.vacuum.packets g₁ z) (C.path.levels.clock.forcedAllowance (d.level+1))) ∧
    (source Y₁ F.layers g₁ z).activities.KBound (C.path.levels.budget (d.level+1))
      (C.path.levels.clock.forcedAllowance (d.level+1)) := by
  constructor
  · rw [actual]
    exact carrier F.vacuum.packets F.layers_paid (A.input_width_pos d.level) g₁ z (Y₁).activities
      (QLocalInheritedPhysicalInlet.valid I hi)
  · exact QLocalInheritedPhysicalInlet.original I hi

private theorem originalRows (U : Config G (C.side (d.level+1) d.period)) :
    Render.renders (Render.prefactor g₁) I.carrier.rep.p U F.layers=
      Render.renders (weight g₁ 1) (Y₁).p U F.layers := by
  have h (L : List (Piece G (C.side (d.level+1) d.period))) :
      Render.renders (Render.prefactor g₁) I.carrier.rep.p U L=
        Render.renders (weight g₁ 1) (Y₁).p U L := by
    induction L with
    | nil => rfl
    | cons a L ih =>
      simp only [Render.renders,ManuscriptQLocalVacuumRadius.weight,one_pow,one_mul,Payload.amount,
        QLocalInheritedPhysicalInlet.rep,I.wellFormed.threshold,ih]
  exact h F.layers

omit [Fintype V] in
private theorem combined (u e : ℝ) (M B : Poly Γ) :
    (Real.exp (-(u+e)):ℂ) • (M*B)=(Real.exp (-e):ℂ) • (M*((Real.exp (-u):ℂ) • B)) := by
  rw [mul_smul_comm,smul_smul,←Complex.ofReal_mul,←Real.exp_add,show -(u+e)=(-e)+(-u) by ring]

/-- The same physical layer and calibration split holds with arbitrary signed multiplicands. -/
theorem reweight (U : Config G (C.side (d.level+1) d.period)) (M B : Poly Γ) :
    (Real.exp (-QLocalInheritedPhysicalInlet.insertion I U):ℂ) • (M*B) =
      (Real.exp (-I.calibration.amount U):ℂ) •
        (M*((Real.exp (-Render.renders (weight g₁ 1) (Y₁).p U F.layers):ℂ) • B)) := by
  have hv : QLocalInheritedPhysicalInlet.insertion I U =
      Render.renders (weight g₁ 1) (Y₁).p U F.layers + I.calibration.amount U :=
    congrArg (fun e=>e+I.calibration.amount U) (originalRows I U)
  rw [hv,combined]

/-- At the physical auxiliary argument the sole remaining change in the full
signed prepared density is its original funded calibration. -/
theorem measured (hi : Retained.NativeIntake I) (x : TestSpace J.tests)
    (U : Config G (C.side (d.level+1) d.period)) :
    (I.input.leaf x).density U=(Real.exp (-I.calibration.amount U):ℂ) •
      (Poly.pass (F.packets.read x g₁ U) *
        ((carry Y₁ F.layers g₁ 1 (QLocalInheritedPhysicalInlet.carried I I.prepared.remainder)).leaf x).density U) := by
  let T:=QLocalInheritedPhysicalInlet.carried I I.prepared.remainder
  let M:=Poly.pass (F.packets.read x g₁ U)
  have hD:=density Y₁ F.layers g₁ 1 F.layers_paid (QLocalInheritedPhysicalInlet.valid I hi) T x U
  exact (QLocalInheritedPhysicalInlet.prepared I x U).trans
    ((reweight I U M ((T.leaf x).density U)).trans
      (congrArg (fun Z=>(Real.exp (-I.calibration.amount U):ℂ) • (M*Z)) hD.symm))

end YM.Integration.ManuscriptQLocalVacuumFamily
