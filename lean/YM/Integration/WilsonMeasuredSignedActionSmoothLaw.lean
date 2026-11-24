import YM.Integration.WilsonMeasuredSignedActionSmoothTest
/-! The two normalizing readings on the same true physical fields and the
same fixed compact pair, after the original finite-volume extractions. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 700000
noncomputable section
namespace YM.Integration.WilsonMeasuredSignedActionSmoothLaw
open Function Filter Set Spec Table Extraction Climb Trace Trace.Pilot PhysMS Maxwell Maxwell.Free
open Next.UVStress OPE OPE.Orbits Work TopologicalSpace MeasureTheory XSpace
open WilsonMeasuredSignedActionSmoothPacket (reading reflected)
open WilsonMeasuredSignedActionSmoothTest (Heard singleton)
open WilsonPhysicalPositionReflectedReturn (sites)
open scoped Topology BigOperators Classical
open private integrated from YM.Integration.WilsonGeneralReducedPhysicalSelfGappedSmooth
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)(J:ℝ→tower S)
local notation "D₄" => (Bel C.book).Field 4

def pair (w:D₄):MaxwellSlots C (fun _:Fin 2=>4):=![w,(Bel C.book).adj (spin_free C.labels) 4 0 w]
def two (b:ContDiffBump sites)(w:D₄)(r:ℝ):ℂ:=
  ∫y:Points 2,b.normed volume y • measured F none (J r) (pair w) r y

theorem second (lead:Leading F J)(b:ContDiffBump sites)(inside:tsupport b⊆conf 2)(w:D₄):
    Tendsto (two F J b w) trail (𝓝 (reading C b w)):=by
  let K:=tsupport b
  have compact:IsCompact K:=by dsimp [K];rw [b.tsupport_eq];exact isCompact_closedBall _ _
  let v:=pair w
  let h:=WickGoal v
  have hreg:ContinuousOn h (conf 2):=fun x hx=>(WickGoal_tied v hx).continuousAt.continuousWithinAt
  obtain ⟨B,cost⟩:=compact.exists_bound_of_continuousOn (f:=h) (hreg.mono inside)
  have supp(y:Points 2)(live:b.normed volume y≠0):y∈K:=by
    apply subset_tsupport
    rwa [b.support_eq,←b.support_normed_eq (μ:=volume)]
  let guarded(g:Points 2→ℂ):Points 2→ℂ:=(conf 2).piecewise g 0
  have guarded_meas(g:Points 2→ℂ)(reg:ContinuousOn g (conf 2)):Measurable (guarded g):=
    reg.measurable_piecewise continuousOn_const (conf_open _).measurableSet
  have same(g:Points 2→ℂ)(y:Points 2)(live:b.normed volume y≠0):guarded g y=g y:=by
    simp [guarded,inside (supp y live)]
  have cut(g:Points 2→ℂ):
      (∫y:Points 2,b.normed volume y • g y)=∫y:Points 2,b.normed volume y • guarded g y:=by
    apply integral_congr_ae
    apply ae_of_all
    intro y
    change b.normed volume y • g y=b.normed volume y • guarded g y
    by_cases off:b.normed volume y=0
    · simp only [off,zero_smul]
    · rw [same g y off]
  apply Metric.tendsto_nhds.mpr
  intro ε pos
  have paid:=Metric.tendstoUniformlyOn_iff.mp (lead.lead 2 (fun _=>4) v 0 K compact inside) (ε/2) (half_pos pos)
  filter_upwards [paid,self_mem_nhdsWithin] with r small hr
  let g:=measured F none (J r) v r
  have wilsonLimit:ContinuousOn g (conf 2):=by
    let z (i:Fin 2):S.Tag:=⟨4,J r 4 (v i)⟩
    intro x hx
    exact (((S.class_smooth (spectator F none) (spectate F none).smooth z).contDiffAt
      ((conf_open _).mem_nhds (Work.A05.smul_conf hr hx))).continuousAt.comp
        (continuousAt_id.const_smul r)).continuousWithinAt
  change dist (∫y:Points 2,b.normed volume y • g y) (∫y:Points 2,b.normed volume y • h y)<ε
  rw [dist_eq_norm,cut g,cut h]
  apply lt_of_le_of_lt (integrated b (guarded g) (guarded h) (guarded_meas g wilsonLimit)
    (guarded_meas h hreg) (C:=B) (δ:=ε/2) (fun y live=>by rw [same h y live];exact cost y (supp y live)) ?_)
    (half_lt_self pos)
  intro y live
  rw [same g y live,same h y live]
  have s:=small y (supp y live)
  rw [dist_comm,dist_eq_norm] at s
  have diff:iteratedFDeriv ℝ 0 g y - iteratedFDeriv ℝ 0 h y=iteratedFDeriv ℝ 0 (g-h) y:=by ext z;simp
  rw [←show g=measured F none (J r) v r from rfl,←show h=WickGoal v from rfl,
    diff,norm_iteratedFDeriv_zero] at s
  exact s.le

def one (w:D₄)(r:ℝ):ℂ:=
  measured F none (J r) (d:=fun _:Fin 1=>4) ![w] r 0

theorem first (lead:Leading F J)(w:D₄):Tendsto (one F J w) trail (𝓝 (singleton C w)):=by
  have clear:(0:Points 1)∈conf 1:=by intro i j _;exact Subsingleton.elim i j
  have eq:WickGoal (C:=C) (d:=fun _:Fin 1=>4) ![w] (0:Points 1)=singleton C w:=by
    let M:=Bel C.book
    let left:Fin 1→M.Tag:=fun i=>⟨4,(![w]:Fin 1→D₄) i⟩
    have tag:left=Fin.cons (⟨4,w⟩:M.Tag) (Next.UVStress.blank M):=by
      funext i
      fin_cases i
      rfl
    exact (congrArg (M.useAt M (0:Points 1)) tag).trans
      (Work.A01.front_eval (Next.UVStress.blank M) (0:Points 1) 4 w).symm
  rw [←eq]
  exact leading_at F lead (d:=fun _:Fin 1=>4) ![w] tendsto_id tendsto_const_nhds clear

def Returns {I:Type*}(b:ContDiffBump sites)(r:I→ℝ)(l:Filter I)(A:Module.End ℂ D₄):Prop:=
  Tendsto (fun i=>one F J (stepField C) (r i)) l (𝓝 (singleton C (A (stepField C)))) ∧
  Tendsto (fun i=>two F J b (stepField C) (r i)) l (𝓝 (reading C b (A (stepField C))))

theorem heard (lead:Leading F J)(b:ContDiffBump sites)(inside:tsupport b⊆conf 2)
    {I:Type*}{r:I→ℝ}{l:Filter I}[NeBot l](small:Tendsto r l trail){A:Module.End ℂ D₄}
    (bought:Returns F J b r l A):Heard C b A:=
  ⟨tendsto_nhds_unique bought.1 ((first F J lead _).comp small),
   tendsto_nhds_unique bought.2 ((second F J lead b inside _).comp small)⟩

end YM.Integration.WilsonMeasuredSignedActionSmoothLaw
end
