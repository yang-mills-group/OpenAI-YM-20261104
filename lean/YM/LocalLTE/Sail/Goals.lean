import YM.LocalLTE.Sail.Publication
/-!
# Accuracy after stamp & evaluations. Cost in true g. additional calendar.

No PT equivalence of thresholds on changing configs assumed. Only cost of marker
value probe at the actual kernel.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Spiral
open Function Filter Set Lattice RG RG.Shoot Pressure Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Mallow ConnectedActivityE6 Push.AbsoluteSums LocalLTE LocalLTE.Vinca VoucherB LocalLTE.Fan
open Next.Scheduling.Clock Next.Scheduling.Instrument Progress.DirectedRecipe Pressure
open Legato.Spool LocalLTE.Sail Bandage.Harmonics
variable {G:Gauge} {s:Sheet G} {D:Rolls s} {T:Protection D}
open Coat
-- true price in Stroke with supplied dimensions.Author P≥...
variable (K M P p p' u v T':ℕ)(e:ℝ)
structure ExpensePlan (G:Gauge)(K P p p' u i d T:ℕ)(v w:Stage)(L:Side)(z ε x:ℝ) :Prop where
    author: let y:= betaF G x L; intakeWeight u y * (3+v.columns) ≤ 1
    tracks: let y:= betaF G x L; intakeWeight u y *((1+2*v.columns)*z) ≤ 1
    stamp: let y:=betaF G x L; ∀ β, y/2 ≤ β → β≤2*y→
      ( (gStep β)^((P:ℝ)+1) ≤ (1/2:ℝ)) ∧ (LocalLTE.River.rotationP ((Labels.frames G).level d) w.order w.power)* y^(grantZ p' T 0) ≤ (gStep β)^((P:ℝ)+1) ∧ allocationK y ε ≤ (gStep β)^((P:ℝ)+1) ∧ y^(chronicleShift u*K) * (gStep β)^((P:ℝ)+1) ≤ (gStep β)^((p:ℝ)+1)
-- P final Ω residual budget BEFORE ratio. Issue Startup certified.Sc.H.A.
variable (v w:Stage)(L:Side)(z:ℝ) (hu:chronicleShift u*K < ((P:ℝ)-p)/2)(hε: -e < -((P:ℝ)+1)/2)(hp:grantZ p' T' 0 < -((P:ℝ)+1)/2)
include hu hε hp
variable (G)
lemma delivers (i d:ℕ) : ∀ᶠ x in atTop, ExpensePlan G K P p p' u i d T' v w L z e x :=by
    let θ:= chronicleShift u; let α:ℝ:= P; let A:ℝ:= α+1; let Y:= fun x=> betaF G x L
    have hP:-(4:ℝ)+ -e< -A/2:=by unfold A α; linarith only [hε]
    have hv : -θ < (0:ℝ):=by unfold θ chronicleShift; have he:=Nat.cast_nonneg (α:=ℝ) u; linarith
    let r:= LocalLTE.River.rotationP ((Labels.frames G).level d) w.order w.power
    filter_upwards [((Rate.power (G:=G) (L:=L) (a:=-θ)).mul_right (3+v.columns)).below hv 1 zero_lt_one,((Rate.power (G:=G) (L:=L) (a:=-θ)).mul_right ((1+2*v.columns)*z)).below hv 1 zero_lt_one, Work.E09.betaF_growth G L|>.eventually_ge_atTop 8, Urns.actualG L _ _ _ ((Rate.power (G:=G) (a:=grantZ p' T' 0)).mul_left r) hp, Urns.actualG L _ _ _ ((Rate.power (G:=G) (a:=-(4:ℝ))).mul Rate.power) hP, Urns.actualG L ((p:ℝ)-α) _ _ (Rate.power (G:=G) (a:=θ*K)) (by unfold θ α; linarith only [hu])] with x h he hz hx hV hK
    refine ⟨(le_abs_self _).trans h, (le_abs_self _).trans he,fun β h1 h2=>⟨?_,hx _ h1 h2,hV _ h1 h2,?_⟩⟩
    · have hy:4 ≤ β:=by linarith only [hz,h1]
      have hq:2 ≤ Real.sqrt β:=by nlinarith only [hy,Real.sq_sqrt (show 0 ≤ β from by linarith only [hy]),Real.sqrt_nonneg β]; -- comment
      let z:= Coat.gStep β; have h₁:z≤1/2:=by unfold z gStep; rw [← one_div]; exact one_div_le_one_div_of_le (by norm_num) hq -- real? inspect
      have h₂:0 <z:=by unfold z gStep; positivity
      apply le_trans _ h₁; nth_rw 1 [← Real.rpow_one z]; exact Real.rpow_le_rpow_of_exponent_ge h₂ (h₁.trans (by norm_num)) (by linarith only [Nat.cast_nonneg (α:=ℝ) P])
    have hh : 0<gStep β:=by unfold gStep; have hu:4 ≤ β:=(by linarith only [h1,hz]); positivity -- grouping
    apply le_trans (mul_le_mul_of_nonneg_right (hK _ h1 h2) (Real.rpow_nonneg hh.le _)) _; rw [← Real.rpow_add hh]; change (gStep β)^((p:ℝ)-α+(α+1))≤ _; apply le_of_eq; ring_nf
section getting
structure Patronage (K P p p' T':ℕ)(ε:ℝ){G:Gauge}{s:Sheet G}{D : Rolls s} {T:Protection D}(V:Delays T) : Prop where
    frames i j: StepStages i j→∀ x:ℝ,V.betaEntry i ≤ x→∀ d≤ j,∀ u≤T', ExpensePlan G K P p p' u i d T' (s.profile j) (s.profile i) (D.L i) (Bandage.Harmonics.capStone s j T') ε x
omit hu
variable (hG: chronicleShift T'*K < ((P:ℝ)-p)/2)
include hG
lemma pensions (V:Delays T) : ∃ U:Delays T, DelayLe V U ∧ ∀ W,DelayLe U W→ Patronage K P p p' T' e W:=by
   let f (i j:ℕ)(x:ℝ):= ∀ d≤ j,∀ u ≤ T', ExpensePlan G K P p p' u i d T' (s.profile j) (s.profile i) (D.L i) (Bandage.Harmonics.capStone s j T') e x
   have ht(i j:ℕ):∀ᶠ x in atTop, f i j x:=by
      let x0:= capStone s j T'; let t:= D.L i; let s':= s.profile j; let v':= s.profile i
      have hu(d:ℕ) : ∀ᶠ x in atTop,∀ u≤T',ExpensePlan G K P p p' u i d T' s' v' t x0 e x:=by
         have h(u:Fin (T'+1)):chronicleShift u.val*(K:ℝ)< ((P:ℝ)-p)/2:= lt_of_le_of_lt (mul_le_mul_of_nonneg_right (show chronicleShift u.val ≤ _ from (by unfold chronicleShift; gcongr; have := u.isLt; omega)) (Nat.cast_nonneg _)) hG -- likely unbound _
         filter_upwards [eventually_all.mpr (fun u:Fin (T'+1)=>delivers G K P p p' u T' e s' v' t x0 (h u) hε hp i d)] with x hx; exact fun u hu=>hx ⟨u,Nat.lt_succ_of_le hu⟩
      filter_upwards [eventually_all.mpr (fun d:Fin (j+1)=>hu d)] with x he; exact fun d hd=> he ⟨d,Nat.lt_succ_of_le hd⟩
   obtain ⟨x,-,h,hP⟩:= collect_upper V.betaEntry _ fun j=> eventually_transitions j _ _ (fun i _=>ht j i)
   refine ⟨{V with betaEntry:=x},⟨h,le_rfl,le_rfl,le_rfl⟩,fun Y h=>⟨?_⟩⟩ -- typo
   intro j i hh x hx; exact hP _ _ ((h.beta _).trans hx) _ hh
noncomputable def hinter (F:Elixir G M): Elixir G M where
    invests {X _ _ _ _ _ _} X' k l f Q:= F.invests (X:=X) X' k l f Q∧Patronage K P p p' T' e Q
    pays:= by
       intro X Kf C Y ht μ k h; obtain ⟨u,hU⟩:= F.pays C Y ht μ k h
       refine ⟨u, fun f hf D w v T R t l Q=>?_⟩
       obtain ⟨U,hV,h⟩:=hU f hf D R t l Q;
       obtain ⟨W,hW,hp⟩:= pensions G K P p p' T' e hε hp hG U
       exact ⟨W,hV.trans hW,fun Y hy=>⟨h Y (hW.trans hy),hp Y hy⟩⟩
end getting
end YM.PhysicalNext.Repeat.Legato.Spiral
