import YangMills.WilsonProof.NativeSupport.JointComponentKernel

/-! Held-field measurability and exact coarse-edge/flag locality of measured components. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 25000
noncomputable section
namespace YM.Integration.InletSusceptibility.JointTicket
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.BetaTransport Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations
open SectorMeasure Oriented Work.E03 Mask Contract Work.F03 Presented LabelSum Sector Footprint
open Packets SliceRows Control Window Pulse Coat Matter Itinerary Census Horticulture ProbabilityTheory Poll Pond
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus JointCoat
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P : Teller G} {T : Tube G S}
    {F : Forest S.ratio} {R : Rep G f} {W μ C : ℝ}
    {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W}
variable (M : Team R) (X : Coat T F) (J : Finset (Bond c)) (probe : Bond c→ℝ→ℝ)
open Census Itinerary Art Rotation
variable (H : Cash W X.x μ L Q o C T R) (he : X.width=o.K)
variable (mh : ∀ b∈J,Measurable (probe b)) (unit : ∀ b∈J,∀ t∈Set.Icc 0 (linkCap S),‖probe b t‖≤1)
include H
private lemma fraction {A : Type*} [MeasurableSpace A] (V : A→ Config G c) (he' : Measurable V) (z : A→Air f G) (hz : Measurable z) :
    Measurable fun t => (vary X (V t)).thetaRef (z t) := by
  have hp:= H.laws.intake.ready
  have hF : Art.Borel fun t=> (vary X (V t)).plate := fun i j=> (Art.borel_plate X hp i j).comp he'
  have hx := (c_measured X.shutter hF).1
  let g t:=(vary X (V t)).relating
  have hg : Art.Borel g := hx
  have hc i : Measurable fun t=> WithLp.ofLp (z t) i := (EuclideanSpace.proj (ι:=Tubular f G) (𝕜:=ℝ) i).measurable.comp hz
  have hm : Measurable fun t=> dotProduct ((z t).ofLp) ((g t)⁻¹ *ᵥ WithLp.ofLp (z t)) := Finset.measurable_fun_sum _ fun i _ =>
    (hc i).mul (Art.borel_times (Art.inverse hg) (d:=fun t=> WithLp.ofLp (z t)) hc i)
  exact measurable_const.mul (Real.measurable_exp.comp ((((Real.measurable_log.comp (Art.det_m hg)).neg.div_const _).sub (hm.div_const _))))


include he mh unit
theorem held_sector (i : Molecule S) (l : Finset ℕ) : Measurable
    (fun V=> if RG.flags (Pressure.temp X.x) V=X.seeds.flags then tithe M (vary X V) J probe l W o.a Q.table Q.halo i else 0) := by
  let A:= (F.order G)
  let f' (V : Config G c) (p : F.Slice G×Air f G):=raw (W:=W) M (vary X V) l i o.a Q.table Q.halo J probe p
  have hg (V) (hv : RG.flags (Pressure.temp X.x) V=X.seeds.flags) : tithe M (vary X V) J probe l W o.a Q.table Q.halo i =
      ∫ y, (∫ z,f' V (y,z)*(vary X V).thetaRef z) ∂A := by
    let Y:= vary X V; have hY : Y.manifest := hv.symm
    have hp : Y.dice=MeasureTheory.volume.withDensity (fun x=> ENNReal.ofReal (Y.thetaRef x)) := Poll.sweep_pdf
      (H.laws.data.localP F Y rfl he hY).sails.fullC
    have he := (raw_price M Y H he hY l i J probe mh unit).1
    unfold tithe; rw [integral_prod _ he]; apply integral_congr_ae; filter_upwards with y
    have hf : Measurable (fun x=> ENNReal.ofReal (Y.thetaRef x)) := by unfold Coat.thetaRef dotProduct; fun_prop
    change _ = ∫ x,f' V (y,x) * _; rw [hp, integral_withDensity_eq_integral_toReal_smul hf (ae_of_all _ fun _=> ENNReal.ofReal_lt_top)]
    apply integral_congr_ae; filter_upwards with x
    change (ENNReal.ofReal _).toReal • f' V (y,x)=_
    rw [ENNReal.toReal_ofReal (show 0 ≤ Y.thetaRef x by unfold Coat.thetaRef bell; positivity),smul_eq_mul]; exact mul_comm ..
  have ht (V : Config G c) : (if RG.flags (Pressure.temp X.x) V=X.seeds.flags then tithe M (vary X V) J probe l W o.a Q.table Q.halo i else 0)=
      if RG.flags (Pressure.temp X.x) V=X.seeds.flags then ∫ y,(∫ z,f' V (y,z)*(vary X V).thetaRef z) ∂A else 0 := by
    split; next hx=> exact hg V hx
    next hx=> rfl
  simp_rw [ht]
  refine Measurable.ite (RG.flags_measurable_eq ..) ?_ measurable_const
  let X' := (Config G c × F.Slice G)× Air f G
  have hU : Measurable (fun y:X'=> y.1.1) := measurable_fst.comp measurable_fst
  have h' : Measurable (fun p:X' => f' p.1.1 (p.1.2,p.2)) := by
    have he' := H.laws.data; have hk := H.laws.intake
    have hz := (show ShellAccess S G X.x W X.width o.γ from by rw [he]; exact H.laws.data.access)
    let Y (p:X'):= (drive X p.1.1 p.1.2)
    let u p:= (Y p).liftA R.beta p.2
    have hv : Measurable u:= Art.levitate X hk.ready hz hU (measurable_snd.comp measurable_fst) R.beta measurable_snd
    have marked : Measurable (fun p:X'=> JointPhysical.sample S X.k J probe ((Y p).input (u p)) p.1.1) :=
      (JointPhysical.sample_env S X.k J probe (funds_branch hk.ready)
        (Art.entering X hU (measurable_snd.comp measurable_fst) hv) hU mh unit).1
    apply marked.mul
    unfold Team.into Team.premium
    split_ifs
    · have hh (M:Leaf R) : Measurable (fun p:X'=> M.paidU (Y p) o.a (u p)):=
        (M.borel.comp (Art.entering X hU (measurable_snd.comp measurable_fst) hv)).mul ((X.enforce_b (2*o.a) (X.plaza (Matter.areas R T 0 X.B (M.turn.badge S)))).comp hv)
      exact (Finset.measurable_fun_prod M.own (fun i _=>hh i)).mul (Finset.measurable_fun_prod _ fun k _=> Art.portage X hk Q.table Q.table_exists hz hU (measurable_snd.comp measurable_fst) measurable_snd ..)
    exact measurable_const

  have hF : Measurable (fun y:X' => f' y.1.1 (y.1.2,y.2)*(vary X y.1.1).thetaRef y.2) := h'.mul
    (fraction X H _ hU Prod.snd measurable_snd)
  have hx := hF.stronglyMeasurable.integral_prod_right' (ν:= MeasureTheory.volume); exact (hx.integral_prod_right' (ν:=A)).measurable

theorem held_measurable (s : Molecule S) : Measurable fun V=> bloom M (vary X V) J probe W o.a Q.table Q.halo s := by
  unfold bloom
  apply Measurable.ite (Cash.chatting (Q:=Q) X (show X.x=X.x from rfl) s) _ measurable_const
  unfold steep likely; refine measurable_const.mul (Finset.measurable_fun_sum _ fun i _=> ?_)
  let f (V) := tithe M ((planted (vary X V) s).taggedL i) J probe (Matter.own s) W o.a Q.table Q.halo s
  let Z d:= (preps (X.taggedL i) {(roster s) with flags:=d})
  let g (d : Support c) (V) := if RG.flags (Pressure.temp X.x) V=d then tithe M (vary (Z d) V) J probe (Matter.own s) W o.a Q.table Q.halo s else 0
  have he V : (∑ d,g d V)=f V := by
    unfold g f Z; classical
    rw [sum_ite_eq]; simp only [mem_univ, if_true]; rfl
  change Measurable f; rw [← funext he]; refine Finset.measurable_fun_sum _ fun i _=> ?_
  exact held_sector M (Z i) J probe H ‹X.width=o.K› mh unit _ _
theorem held_uses (s : Molecule S) (fresh : ∀ b∈J,zone S X.B b⊆H.unionP s) :
    UsesFinal (Pressure.temp X.x) (H.unionP s) (fun V=> bloom M (vary X V) J probe W o.a Q.table Q.halo s) := by
  intro U V h hp
  let t:= Pressure.temp X.x
  let Y:= vary X U; let Y':= vary X V
  let Z:=planted Y s; let Z':= planted Y' s
  let q:= H.unionP s; have hl : ground R T Q.halo X.B s=q := rfl
  have hh k : tithe M (Z.taggedL k) J probe (Matter.own s) W o.a Q.table Q.halo s=tithe M (Z'.taggedL k) J probe (Matter.own s) W o.a Q.table Q.halo s := by
    refine marginal (X:=Z.taggedL k) (Y:=Z'.taggedL k) (k:=Matter.own s) (l:=Matter.own s) (p:=s)
      M H J probe he (planted_valid Y s) (planted_valid Y' s) mh unit ?_ fresh (fun _ _=> Iff.rfl)
    apply Village.mk
    · change X.x=X.x; rfl
    · change X.width=X.width; rfl
    · change X.χ=X.χ; rfl
    case actual => exact h
    case frames => intro i h; change X.Y i=X.Y i; rfl
    case site => intro i hi; change Prod.fst k i=_; rfl
    case bond => intro i hi; change Prod.snd k i=_; rfl
    intro i hi
    have he : i ∈ q ∩ RG.flags t U ↔ i∈q∩RG.flags t V := by unfold t q; rw [hp]
    have hv : i∈RG.flags t U ↔ i∈ RG.flags t V := by simp only [mem_inter,show i∈q from hi,true_and] at he; exact he
    change i∈(planted Y s).seeds.place ↔ i ∈ (planted Y' s).seeds.place
    simp only [planted,vary,Y,Y',preps,place,mem_union,t] at hv ⊢; rw [hv]
  have hz : standsIn Y R Q.halo s ↔ standsIn Y' R Q.halo s := by
    unfold standsIn claimed
    change Ac.Spark (areas R T _ X.B) s ∧ troupe T R Q.halo X.B s ∧ RG.flags t U∩ground _ _ Q.halo X.B s=_ ↔
      Ac.Spark (areas R T _ X.B) s ∧ troupe T R Q.halo X.B s ∧ RG.flags t V∩ground _ _ Q.halo X.B s=_
    rw [hl,inter_comm (RG.flags t U),inter_comm (RG.flags t V),show q∩_= q∩_ from hp]
  change (if standsIn Y R Q.halo s then _ else _)=(if standsIn Y' R Q.halo s then _ else _); simp_rw [hz]; split
  next hk => exact congr_arg likely (funext hh)
  rfl


end YM.Integration.InletSusceptibility.JointTicket
