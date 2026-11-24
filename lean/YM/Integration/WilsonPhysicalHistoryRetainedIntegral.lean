import YM.Integration.WilsonPhysicalHistoryRetainedThermal

/-! Measurability and absolute integrability of the retained signed molecule
under the same current affine law, including its complete earlier gas. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Function Filter Finset Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson MeasureTheory
open ConnectedActivityE6 ConnectedActivityE6.Coat
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure
open Bloch Laurent PhysicalNext.Repeat.Legato
open scoped Topology BigOperators Classical
variable {G : Gauge}

private theorem regular_measurable {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
    {P : Teller G} {W C a : ℝ} (X : Coat T F) (O : Rep G f) (i : ℕ) (l : Finset ℕ)
    (M : ℕ) (Q : ChartRatio G) (he : ShellAccess S G X.x W X.width C) (ready : P.Funds S T)
    (smooth : Measurable (O.activities.E i)) :
    Measurable (fun s : F.Slice G × Air f G=>
      (X.wrapY s.1).vertex O Q W a l M s.2 (regularHead S i)) := by
  let u (s : F.Slice G × Air f G):=(X.wrapY s.1).liftA O.beta s.2
  have zm : Measurable u := (X.airwards he ready measurable_fst).2.2 O.beta measurable_snd
  have um:=X.summon measurable_fst zm
  have base : Measurable (O.activities.regularOccurrence O.p i) := masked_measurable _ _ _ smooth
  change Measurable (fun s : F.Slice G × Air f G=>Real.exp
    ((-O.activities.regularOccurrence O.p i ((X.wrapY s.1).input (u s)))*
      X.enforce (2*a) (u s) (X.plaza (Raw.regularFoot S.ratio 0 X.B O i)))-1)
  exact (Real.measurable_exp.comp ((base.comp um).neg.mul ((X.enforce_b _ _).comp zm))).sub measurable_const

theorem retained_integrable (R : Run G) {N n j d : ℕ} (hj : j<N) (A : Comparison R (p:=n) hj d)
    {c L : Side} {S : StepData c (R.family.side j n)} {T : Tube G S} {F : Forest S.ratio}
    {W μ C x : ℝ} {M : Teller G} {D : ConnectedActivityE6.Target G M} {o : Target.Order G W}
    (H : Cash W x μ L D o C T (R.family.path.rep N n j)) (X : Coat T F) (clock : X.x=x)
    (width : X.width=o.K) (mf : X.manifest)
    (small : (Real.sqrt 2*Pert.Asymptotics.regulatorRun R.family N n (j+1))^(d+1)≤1)
    (l : Finset ℕ) (p : Molecule S) :
    Measurable (X.body (approximation R (p:=n) hj d) D.table W o.a l D.halo p) ∧
    Integrable (X.body (approximation R (p:=n) hj d) D.table W o.a l D.halo p) ((F.order G).prod X.dice) := by
  let P:=R.family.path.rep N n j
  let Q:=approximation R (p:=n) hj d
  have access:=H.laws.data.access
  rw [←clock,←width] at access
  have intake:=H.laws.intake
  rw [←clock] at intake
  obtain ⟨b,pay,rows⟩:=molecule_rows R hj A
  have rates (i : ℕ) : 0≤b i := by
    have h:=(pay (P.activities.reg i).site).1 i
    change 0≤(if (P.activities.reg i).site=(P.activities.reg i).site then
      P.p.mass (P.activities.reg i).support (b i) else 0) at h
    rw [if_pos rfl] at h
    exact nonneg_of_mul_nonneg_right h (Real.exp_pos _)
  let loc (t : F.Slice G × Air (R.family.side j n) G) (v : Head S) :=
    (X.wrapY t.1).vertex Q D.table W o.a l D.halo t.2 v
  have filed (i : Head S) : Measurable (fun t=>loc t i) ∧
      ∃ h : ℝ, 0≤h ∧ ∀ t,|loc t i|≤h := by
    by_cases active : ∃ v,i=regularHead S v
    · obtain ⟨v,rfl⟩:=active
      have sm : Measurable (Q.activities.E v):=(A.posterior.fit.regular.smooth v).borel
      refine ⟨regular_measurable X Q v l D.halo D.table access intake.ready sm,?_⟩
      let i:=regularHead S v
      use H.fair i+2*(1+H.fair i)*b v
      constructor
      · have hf:=H.fair_price i; positivity [rates v]
      intro t
      let a:=(X.wrapY t.1).vertex P D.table W o.a l D.halo t.2 i
      have orig : |a|≤H.fair i := H.voice (X.wrapY t.1) clock width mf l i t.2
      have diff := (rows (X.wrapY t.1) D.table W o.a l D.halo t.2).1 v small
      calc |loc t i| = |a-(a-loc t i)| := by ring_nf
           _ ≤ |a|+|a-loc t i| := abs_sub _ _
           _ ≤ H.fair i+(2*(1+H.fair i))*b v := by
             refine add_le_add orig (diff.trans (mul_le_mul_of_nonneg_right ?_ (rates v)))
             linarith only [orig]
    · have same (t : F.Slice G × Air (R.family.side j n) G) := (rows (X.wrapY t.1)
        D.table W o.a l D.halo t.2).2 i (fun v eq=>active ⟨v,eq⟩)
      constructor
      · convert X.vertex_b D.table_exists intake access o.a l D.halo i measurable_fst measurable_snd using 1
        funext t
        exact (same t).symm
      use H.fair i,H.fair_price i
      intro t; exact (congrArg abs (same t)).symm.trans_le (H.voice (X.wrapY t.1) clock width mf l i t.2)
  have borel : Measurable (X.body Q D.table W o.a l D.halo p) :=
    Finset.measurable_fun_prod _ (fun i _=>(filed i).1)
  choose cap nonneg bounded using fun i=>(filed i).2
  refine ⟨borel,(memLp_top_of_bound borel.aestronglyMeasurable (∏ i∈p,cap i) (Eventually.of_forall ?_)).integrable le_top⟩
  intro t
  change |∏ i∈p,loc t i|≤_
  rw [abs_prod]
  exact Finset.prod_le_prod (fun _ _=>abs_nonneg _) (fun i _=>bounded i t)

end YM.Integration.OriginalMarkedRunAction
