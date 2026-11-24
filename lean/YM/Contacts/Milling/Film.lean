import YM.Contacts.Milling.Mallet
import YM.Next.STATIONARY.Shape.SoftTransfers
import YM.Next.STATIONARY.Joint.Chart
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.LogLink
namespace YM.Contacts.Milling
open Function Set Filter Metric Asymptotics MeasureTheory
open Finset Lattice RG Wilson Precision Exterior PertExtension.Series Pulse YM.Stationary ConnectedActivityE6 Push.SectorMeasure
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}{c f n: Side}{k:ℕ}
namespace Kale
-- Ward prerequisites for an aggregate scalar homogeneous up to the current
-- `k` in (coupling,fields). Here section invariance at *fixed loop* ℓ. The aggregate
-- periodic shadows will have this even though the finite-torus expansion differs by winding.
structure Guards (P:Link G n→ℝ)(k:ℕ): Prop where
  cont: Continuous P
  analytic: AnalyticAt ℝ P 0
  color u x: P (stain u x)=P x
  spins u x: P (orderTurn u x)=P x -- no translations here, sym enough
  grade: Rays k (fun z:Swatch G n=> P (moveField z)-P z.2)
def walk (x:Site n): Lattice.Walk:= route 0 (lift x) (Equiv.refl Axis) -- order?
lemma route_e (x:Site n): stop 0 (walk x)=x:= by
  rw [← map_zero (wrap n),← wrap_stop_cover]; unfold walk; rw [route_end, wrap_lift]
def bring (U:Config G n)(x:Site n) := travel U 0 (walk x)
def alive (U:Config G n) := Lattice.gauge (bring U) U
lemma foldGauge (U:Config G n)(t:Site n→ G.El): alive (Lattice.gauge t U)=Lattice.gauge (fun _=> t 0) (alive U):= by
  funext ⟨x,b⟩; unfold alive; have he (x:Site n): bring (Lattice.gauge t U) x=t 0 *bring U x*(t x)⁻¹:= by unfold bring; rw [travel_gauge,route_e]
  rw [Lattice.gauge,he,he,Lattice.gauge,Lattice.gauge,Lattice.gauge]; group
@[fun_prop] lemma active_cont: Continuous (alive (G:=G) (n:=n)):= by unfold alive bring Lattice.gauge; fun_prop
lemma troops : Army (bring (G:=G) ∘ input G n) 0 := by
  intro i; unfold Function.comp bring
  have H: Army (input G n) 0:= Army.powL contDiffAt_id; set a:= walk i; suffices h : ∀ a:Lattice.Walk,∀ i:Site n, ContDiffAt ℝ ω (fun z=> G.mat (travel (input G n z) i a)) 0 from h a 0
  intro a; induction a with
  | nil=> exact fun _ => contDiffAt_const
  | cons c a ih=> intro x; simp_rw [travel,G.mat_mul]; apply ContDiffAt.mul; swap; exact ih _
                  unfold Step.read; split; · simp only [G.mat_inv]; exact (starL ℝ).contDiff.contDiffAt.comp _ (H _)
                  exact H _
lemma travel_identity (n : Side)(u:Lattice.Walk)(x: Site n): travel (1:Config G n) x u=1:=by induction u generalizing x with | nil=>rfl | cons v a ih =>rw [travel,Step.read,ih,mul_one]; split <;> simp
lemma brings_zero : (bring (n:=n) (1:Config G n))=1:= funext fun i=> travel_identity ..
def charHeight (G:Gauge):=(reliable G).choose_spec.choose
lemma guardChar (G:Gauge): Reliable G (charHeight G) (reliable G).choose:= (reliable G).choose_spec.choose_spec.2 _ (reliable G).choose_spec.choose_spec.1 le_rfl
def bevel (n:Side)(U:Config G n): Link G n:= (arm _ _ 1).symm (fun i=> cutLog Chi.canonical (charHeight G) (U (i.1,axisEquiv.symm i.2)))
-- proof as in Reliable.borel, retaining continuity requested
private lemma cut_cont (G:Gauge) {d γ:ℝ}(h:Reliable G d γ) (χ : Chi) : Continuous (cutLog χ d (G:=G)):= by
  rw [continuous_iff_continuousAt]; intro u
  by_cases hx : G.chord u ≤ 2*d
  · have hp : ContinuousAt (fun v : G.El => χ.innerShare d (G.chord v)) u := by
      unfold Chi.innerShare; exact (χ.smooth.continuous.comp (f:=fun v : G.El => (G.chord v/d)^2) (by fun_prop)).continuousAt
    exact hp.smul ((h.patch _ hx).continuousAt.comp (f:=G.mat) G.continuous_mat.continuousAt)
  refine ContinuousAt.congr (f := fun _ : G.El => (0:G.Color)) continuousAt_const ?_
  have he : ∀ᶠ v in 𝓝 u, 2*d < G.chord v := G.continuous_chord.continuousAt.eventually
    (lt_mem_nhds (lt_of_not_ge hx))
  filter_upwards [he] with v hv
  have hk : χ.innerShare d (G.chord v)=0 := by
    by_contra hu; exact (χ.chosen_lt _ _ h.down hu).not_ge hv.le
  rw [cutLog,hk,zero_smul]
lemma bevel_cont (n:Side): Continuous (bevel (G:=G) n):= (arm G n 1).symm.continuous.comp <| continuous_pi fun i:Body 1 n=> (cut_cont G (guardChar G) _).comp (continuous_apply _)
lemma bevel_conj (n:Side)(u:G.El)(U:Config G n): bevel n (Lattice.gauge (fun _=>u) U)= stain u (bevel n U) := by
  apply (arm G n 1).injective; unfold stain bevel; simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.apply_symm_apply]; exact funext fun i=> (guardChar G).conjugate ..
lemma summit (n:Side): bevel (G:=G) n =ᶠ[𝓝 1] content := by
  have he : ∀ i: Edge (Site n), ∀ᶠ U: Config G n in 𝓝 1, cutLog Chi.canonical (charHeight G) (U i)=G.plog (G.mat (U i)):= by
    intro i; have h := ((continuous_apply i).tendsto (1:Config G n)); have hU : ∀ᶠ x:G.El in 𝓝 1,G.chord x < charHeight G:= by simpa using (show ∀ᶠ x:G.El in 𝓝 1,G.chord x < charHeight G from G.continuous_chord.continuousAt.eventually (gt_mem_nhds (by simpa using (guardChar G).down)))
    exact (h.eventually hU).mono (fun U hv=> (guardChar G).kept _ _ hv.le)
  filter_upwards [eventually_all.mpr he] with U hu; unfold content bevel; exact congr_arg _ (funext fun i=> hu _)

variable {P:Link G n→ℝ}
def fire (P:Link G n→ℝ)(U:Config G n) := P (bevel n (alive U))
lemma fire_cont (h: Guards P k): Continuous (fire P):= h.cont.comp ((bevel_cont _).comp active_cont)
lemma fire_color (h:Guards P k): GaugeInvariant (fire P):= fun t U=> by rw [fire,foldGauge,bevel_conj,h.color]; rfl
private def plaster (x:Link G n): Swatch G n:= (frameLog (bring (input G n x)),x)
lemma flame : AnalyticAt ℝ (plaster (G:=G) (n:=n)) 0:= ContDiffAt.analyticAt ((Army.logG troops (by simp [brings_zero])).prodMk contDiffAt_id)
lemma flash : plaster (0:Link G n)=0:=by simp [plaster,brings_zero]
lemma region : (bevel (G:=G) n∘ alive ∘ input G n) =ᶠ[𝓝 0] (moveField ∘ plaster):= by
  have hi: Tendsto (bring ∘ input G n) (𝓝 0) (𝓝 (1:Coats G n)):= by simpa [brings_zero] using! (troops (n:=n) (G:=G)|>.cont.tendsto)
  have hp: Tendsto (alive ∘ input G n) (𝓝 0) (𝓝 (1:Config G n)):= by
    have he:alive (1:Config G n)=1:=by unfold alive; rw [brings_zero]; funext; simp [Lattice.gauge]
    simpa [he] using (active_cont.comp (input_cont (m:=n) (G:=G))).tendsto 0
  filter_upwards [hi.eventually switch_frameLog,hp.eventually (summit n)] with i hx hu; simp only [Function.comp_apply] at *; change bevel _ _ = content (Lattice.gauge (switchSite (frameLog _)) _); rw [hu,hx]; rfl
lemma fires (h:Guards P k) : AnalyticAt ℝ (fire P ∘ input G n) 0 ∧ Rays k ((fire P ∘ input G n)-P):= by
  let p:=moveField (G:=G) (m:=n); have ht:(fire P ∘ input G n) =ᶠ[𝓝 0] ((P∘p)∘plaster):= (region (n:=n) (G:=G)).mono fun i hi=> congr_arg P hi
  let q:= P∘p; have hp:AnalyticAt ℝ q 0:= AnalyticAt.comp (by unfold p; rw [moveField_zero]; exact h.analytic) moveField_analytic
  have hx : AnalyticAt ℝ (q∘plaster) 0:= AnalyticAt.comp (by rw [flash]; exact hp) flame; refine ⟨hx.congr ht.symm,?_⟩; let F : Swatch G n→ℝ:= P∘Prod.snd; have hF : AnalyticAt ℝ F 0:= h.analytic.comp (f:=⇑(ContinuousLinearMap.snd ℝ (BaseSites G n) (Link G n))) (ContinuousLinearMap.analyticAt _ _) -- comp
  intro v; exact (merkin (hp.sub hF) h.grade _ (flame (G:=G) (n:=n)) flash v).congr' ((along v).eventually ((ht.sub (f:=_) (.refl _ _))).symm) .rfl -- inspect
structure Wedge (F: Config G n→ℝ): Prop where
  rounds s U : F (pull s 0 U)=F U
  invariance : GaugeInvariant F
  consent: Continuous F
  radiant: AnalyticAt ℝ (F∘ input G n) 0
lemma evidence (F: Config G n→ℝ)(h: Wedge F): Pointwise (F ∘ input G n):= point_actual _ h.radiant h.invariance h.rounds
def mirror (F:Config G n→ℝ)(U:Config G n):= Patch.average (fun i:Signed=> F (pull i 0 U))
lemma seams (F:Config G n→ℝ)(a:Signed): (fun x=>F (pull a 0 (input G n x)))=(F ∘ input G n) ∘ orderTurn (G:=G) (m:=n) a:= funext fun i=> by change _=F _; exact congr_arg F (flip_links a i)
lemma planted (h:Guards P k): Wedge (mirror (fire P)) := by
   refine ⟨fun i U=> orbit_axis _ U i, fun t U=> ?_,?_ ,?_⟩
   · unfold mirror; simp only [Work.F05.pull_gauge_zero,fire_color h _ _]
   · unfold mirror Patch.average; exact continuous_const.mul (continuous_finsetSum _ fun i _ => (fire_cont h).comp (continuous_pull ..))
   have he (i: Signed): ContDiffAt ℝ ω (fun x=> fire P (pull i 0 (input G n x))) 0 := by rw [seams]; apply ContDiffAt.comp; swap; exact (orderTurn i).contDiff.contDiffAt; rw [map_zero]; exact (fires h).1.contDiffAt
   exact (contDiffAt_const.mul (ContDiffAt.sum (f:=fun (i:Signed) x=>fire P (pull i 0 (input G n x))) (s:=univ) (fun i _=> he i))).analyticAt
lemma survives (h:Guards P k): Rays k ((mirror (fire P) ∘ input G n) - P) := by
   let f (i:Signed)(x:Link G n):= fire P (pull i 0 (input G n x))-P x
   have he : ∀ i, Rays k (f i):= fun i=> by
     let V:=orderTurn (G:=G) (m:=n) i; let g:=fire P ∘ input G n; have hv:Rays k ((g-P) ∘ V) := merkin ((fires h).1.sub h.analytic) (fires h).2 _ (V.analyticAt _) V.map_zero; rw [show f i=(g-P)∘V from funext fun x=> by unfold f; rw [flip_links]; change _= g _-P _; rw [show P (V x)=_ from h.spins i x]; rfl]; exact hv
   let a:ℝ:= Fintype.card Signed; have ha : a≠0:= by unfold a; exact_mod_cast (Fintype.card_pos (α:=Signed)).ne'
   rw [show mirror _ ∘ input G n-P=(fun x=>a⁻¹*∑ i,f i x) from funext fun x=>by simp only [Function.comp_apply, f,mirror, Patch.average,Pi.sub_apply,sum_sub_distrib,sum_const,card_univ]; change a⁻¹*_ - _ = a⁻¹*(_- _); rw [mul_sub, nsmul_eq_mul,← mul_assoc]; change _ = _ - a⁻¹*a *_; rw [inv_mul_cancel₀ ha,one_mul]]
   exact fun x=> (IsBigO.sum fun i _=> he i x).const_mul_left _
end Kale
end
end YM.Contacts.Milling
