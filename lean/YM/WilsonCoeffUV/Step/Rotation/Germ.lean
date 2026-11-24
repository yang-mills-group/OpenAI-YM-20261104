import YM.WilsonCoeffUV.Step.Rotation.Swap
/-!
# Auxiliary: unscaled re-tree germ at 0, both active spaces on common B coordinates.
Use actual Haar equation, then log-shell cancellation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Power.Freedom
open Wilson Lattice Laurent Exterior Bloch Matrix Precision Stationary RG Blue
open Next.Free FreeResolvent Tree Work.F05 Function Filter Gauge
open YM.PertExtension.Chart (expLinks physical jacobian)
open MeasureTheory
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {c f : Side}{G:Gauge}(S:StepData c f)
variable {B T:Forest S.ratio}(e:B.Free≃T.Free)
private abbrev Ccol := Woods G c
abbrev Sector := (B.Free→ G.Color)×TreeVars G c
variable (G) in
def shiftPi : T.Slice G ≃ᵐ B.Slice G := MeasurableEquiv.piCongrLeft (fun _ : B.Free=> G.El) e.symm
lemma shift_Haar : MeasurePreserving (shiftPi G S e) (T.order G) (B.order G) := measurePreserving_piCongrLeft (fun _=> G.probHaar) e.symm
lemma shift_at (q:T.Slice G)(j:B.Free) : shiftPi G S e q j=q (e j) := by
  conv_lhs => arg 3; rw [← e.symm_apply_apply j]
  exact Equiv.piCongrLeft_apply_apply _ _ _ _
lemma re_expose (w:B.Free→ G.Color): shiftPi G S e (expLinks G _ (Work.F05.index e w))=expLinks G _ w := by
  ext1 i; rw [shift_at]; change G.lieExp _ = _; rw [index_apply]; rfl
lemma j_shift (Ñ:ChartRatio G) (w:B.Free→ G.Color) : jacobian Ñ (Work.F05.index e w) = jacobian Ñ w := by
  rw [PertExtension.Chart.jacobian,PertExtension.Chart.jacobian,← e.prod_comp]; simp_rw [index_apply]

-- before and after logs. No actual masked assertions.
variable (B) in
def rawD (w:Sector (S:=S) (G:=G) (B:=B)):= B.drape (expLinks G B.Free w.1)
variable (G) in
def newT (q:B.Slice G) : B.Slice G:= shiftPi G S e (Profiles.reroute B T G q)
def newG (v:Sector (S:=S) (G:=G) (B:=B)) := newT G S e (expLinks G B.Free v.1)
-- unshifted measure transition
lemma newG_at (v:Sector (S:=S) (G:=G) (B:=B)): newG S e v=shiftPi G S e (collapse S T (rawD S B v)):=rfl
private lemma drape_one (H:Forest S.ratio) : H.drape (1:H.Slice G)=1 := by
  funext i; by_cases h:i∈H.trunks
  · exact H.on_tree _ ⟨i,h⟩
  exact H.off_tree _ ⟨i,h⟩
lemma newG_zero : newG (G:=G) S e 0=1 := by
  rw [newG_at,show rawD S B 0=(1:Config G f) from ?c,← drape_one S T,coll_once]; funext i; rw [shift_at]; rfl
  case c=> change B.drape (expLinks G B.Free 0)=_; rw [show expLinks G B.Free 0=1 from funext fun _=> G.mat_lieExp_zero]; apply drape_one
lemma newT_pres : MeasurePreserving (newT G S e) (physical G B.Free) (physical G B.Free) := (shift_Haar S e).comp (Profiles.spending B T G)
lemma newT_inj : Injective (newT G S e) := (shiftPi G S e).injective.comp (Profiles.reroute B T G).injective

variable (B) in
lemma rawD_green (i:Edge (Site f)) : ContDiffAt ℝ ω (fun v=>G.mat (rawD S B v i)) 0 := by
  by_cases hh:i∈B.trunks
  · simp_rw [show ∀ v,rawD S B (G:=G) v i=1 from fun v=> B.on_tree _ ⟨i,hh⟩]; exact contDiffAt_const
  simp_rw [show ∀ v:Sector (S:=S) (G:=G) (B:=B),rawD S B v i = G.lieExp (v.1 ⟨i,hh⟩) from fun v=> B.off_tree _ ⟨i,hh⟩]
  exact G.exp_jet.contDiffAt.comp (f:=fun v:Sector (S:=S) (G:=G) (B:=B)=> v.1 ⟨i,hh⟩) 0 ((contDiffAt_apply ℝ _ _ _).comp (f:=Prod.fst) 0 contDiffAt_fst)
lemma gauge_green (T:Forest S.ratio)(i:Site f) : ContDiffAt ℝ ω (fun v=>G.mat (T.foldAt (rawD S B v) i)) 0 := by
  have he (w:Walk)(u:Site f): ContDiffAt ℝ ω (fun v=>G.mat (travel (rawD S B v) u w)) 0 := by
    induction w generalizing u with
    | nil=> exact contDiffAt_const
    | cons a w h=> simp only [travel,G.mat_mul]; apply ContDiffAt.mul _ (h _); unfold Step.read; split
                   · exact Push.Loops.mat_inv_diff (rawD_green S B _)
                   exact rawD_green S B _
  exact Push.Loops.mat_inv_diff (he _ _)
lemma newG_mat (i:B.Free) : ContDiffAt ℝ ω (fun v=>G.mat (newG S e v i)) 0 := by
  simp_rw [newG_at,shift_at,collapse,Lattice.gauge,G.mat_mul]
  exact ((gauge_green S T _).mul (rawD_green S B _)).mul (Push.Loops.mat_inv_diff (gauge_green S T _))

def fresh (v:Sector (S:=S) (G:=G) (B:=B)) : B.Free→ G.Color := mapLog (S:=S) B (newG S e v)
lemma fresh_zero : fresh (G:=G) S e 0=0 := by unfold fresh mapLog LocalH.snap; rw [newG_zero]; ext; simp
lemma fresh_green : ContDiffAt ℝ ω (fresh (G:=G) S e) 0 := by
  apply contDiffAt_pi.mpr; intro i
  exact ContDiffAt.comp (g:=G.plog) 0 (by rw [show G.mat (newG S e 0 i)=1 from by rw [newG_zero]; rfl]; exact G.plog_diff) (newG_mat S e i)
lemma fresh_auth : ∀ᶠ v in 𝓝 (0: Sector (S:=S) (G:=G) (B:=B)), expLinks G B.Free (fresh S e v)=newG S e v:= by
  have ht i : Tendsto (fun v=>newG S e (G:=G) v i) (𝓝 0) (𝓝 1) := by
    apply Push.Loops.tendsto_mat.mpr
    have he:= (newG_mat (G:=G) S e i).continuousAt.tendsto; rw [newG_zero] at he; exact he
  filter_upwards [eventually_all.mpr (fun i=> (ht i).eventually G.plog_right)] with v hv; exact funext hv
lemma fresh_area (Ñ:ChartRatio G)(p:LocalRatio Ñ) :
    let F:=fresh S e (G:=G)
    ∀ᶠ v:Sector (S:=S) (G:=G) (B:=B) in 𝓝 0, |(fderiv ℝ (fun y=>F (y,v.2)) v.1).det| *jacobian Ñ (F v)=jacobian Ñ v.1 := by
  intro F
  exact areaP p F (fresh_zero S e) (fun _=>newT G S e) (fun _=> newT_pres ..) (fun _=> newT_inj ..) (fresh_green ..) (fresh_auth ..)
end YM.WilsonCoeffUV.Power.Freedom
