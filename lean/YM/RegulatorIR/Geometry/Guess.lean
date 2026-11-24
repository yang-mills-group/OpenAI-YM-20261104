import YM.RegulatorIR.Geometry.Fields
import YM.Branch.Covariant
import YM.PREC.Derivative

/-! Deterministic unmasked predictor branch at the flat. Off-chart use a
measurable covariant extension: freeze one (shared!) physical tag site and
bond assignment with actual evaluation rule including the default tests. No
claim that this is the real Wilson germ on a mask, or samples the same
real torus stochastic kernel globally. It gives exactly the same prediction
on a neighborhood of the flat as any choice; its quotient block penalties
integrate to one globally. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Geometry
open Function Set Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Field RG Push Precision
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius
variable {c f:Side}(S:StepData c f) {G:Gauge}

def invS : YM.Signed := ⟨Equiv.refl _,fun _=>true⟩
lemma spun (s:Config G c)(i: Edge (Site c)): pull invS 0 s i= (s (reflect i))⁻¹ := by
 rcases i with ⟨a,b⟩
 have hp: affine invS 0 a=-a := by rw [affine, add_zero]; ext1 j; simp [invS,Signed.act]
 unfold pull; rw [hp, show Step.rotate (posDir b) invS=negDir b from rfl]; rfl

def directive : S.Choices :=⟨fun _=>(S.patch.center,Equiv.refl Axis),fun _=>S.patch.center⟩
lemma directs (x:Site c) : S.withinChoice invS x (directive S)=directive S:=by
 let t:= directive S; let p:= S.patch
 change S.withinChoice invS x t= _
 apply Prod.ext
 · funext v; change S.withinSites invS x t.1 v=t.1 v
   obtain ⟨z,rfl⟩:= (StepData.sendSites invS x).surjective v
   rw [show StepData.sendSites invS x z=affine invS x z from rfl,S.port_site]
   apply Prod.ext _ rfl
   exact Subtype.ext (show invS.act (0:Cover)=0 from invS.act_zero)
 funext e; change S.withinBond invS x t.2 e = t.2 e
 obtain ⟨a,rfl⟩:= (StepData.sendBonds invS x).surjective e
 rw [show StepData.sendBonds invS x a=sendEdge invS x a from rfl,S.port_bond]; exact Subtype.ext (show invS.act (0:Cover)=0 from invS.act_zero)

def predictor (U:spins G f) : spins G c:=fun i=> S.prediction (orbLift U) (directive S) i.val
variable (H:S.patch.Branches S.kernel G)
include H
lemma pec (U:spins G f)(hv:Even f.val): orbLift (predictor S U)= S.prediction (orbLift U) (directive S):=by
 let P:=S.prediction (orbLift U) (directive S); have hf : ∀ i,P (reflect i)= (P i)⁻¹:= by
   have ht: pull invS 0 (orbLift U)=orbLift U:=by ext1 i; rw [spun,show orbLift _ _=(orbLift U i)⁻¹ from lift_flip hv .., inv_inv]
   have hp:= S.prediction_channel H invS 0 (orbLift U) (directive S)
   rw [directs, show S.ratio.embed 0=0 from S.ratio.root.map_zero,ht] at hp
   intro i; rw [show P i=(P (reflect i))⁻¹ from (congr_fun hp i).trans (spun ..),inv_inv] -- rewrite replaces?
 obtain ⟨V,hv⟩:= is_sheet P hf
 have hx: predictor S U=V:=by ext1 i; rw [predictor];change P _=_; rw [hv]; exact lift_at ..
 rw [hx];exact hv.symm
lemma prediction_flow (U:spins G f)(k:Site f→G.El)(hc:compatible k): predictor S (goat k U)=goat (k ∘ S.ratio.embed) (predictor S U):=by
 ext1 e; rw [goat_at,predictor,goat_lift _ _ hc]; unfold StepData.prediction; rw [S.updateGauged H,(S.patch.bond_gauge (h:=H) ..).2]; rfl
lemma predict_measurable : Measurable (predictor (G:=G) S):=measurable_pi_lambda _ fun _=>measurable_pi_apply _ |>.comp ((S.prediction_meas H (directive S)).comp ((lift_cont G (n:=f)).measurable))
omit H in
lemma lift_one : orbLift (1:spins G f)=1:=by funext i; unfold orbLift liftLinks; split <;> simp
lemma predict_zero : predictor S (1:spins G f)=1:=by funext i; rw [predictor,lift_one, Push.settled _ H]; rfl

-- only at fixed regulator. All analytic jets use any choices on their branch domain.
omit H in
lemma examines (x: Site c): S.patch.usesMin S.kernel (expandAt (S.ratio.embed x) (1:Config G f)):=by rw [← Precision.link_one]; exact Push.picks S x
lemma checks (t: S.SitesChoice) (i:Edge (Site c)): S.patch.usesBest S.kernel (S.connector (1:Config G f) t i):=by
 rw [← Precision.link_one,show S.connector (represent 0) t i= (1:S.patch.Connector G) from funext fun j=> Push.deck_zero S H i t j]; refine lt_of_le_of_lt ((S.patch.bond_min (1:S.patch.Connector G)).choose_spec 1) ?_
 simpa [Patch.bondCost] using S.kernel.predictor_cut_pos
omit H in
lemma precinct : ∀ᶠ x : Config G f in 𝓝 1,∀ i: Site c, S.patch.usesMin S.kernel (expandAt (S.ratio.embed i) x):= eventually_all.mpr fun i => ((show Continuous (expandAt (K:=G.El) (S.ratio.embed i)) by unfold expandAt; fun_prop).tendsto 1).eventually (S.patch.min_open.mem_nhds (examines S i))
private lemma selects (b: Site c) : ContinuousAt (fun u:Config G f=> S.patch.selected (expandAt (S.ratio.embed b) u)) 1:=by
 let m:=expandAt (K:=G.El) (S.ratio.embed b); let P:=S.patch
 have h: ContinuousAt (P.selected (G:=G)) (m 1):= (P.selected_cont H).continuousAt (P.min_open.mem_nhds (examines S b))
 apply h.comp (f:=m)
 exact (show Continuous m from by unfold m expandAt; fun_prop).continuousAt
private lemma dance (t:S.SitesChoice) (b: Edge (Site c)): ContinuousAt (fun U:Config G f=> S.connector U t b) 1:=by
 apply continuousAt_pi.mpr;intro x
 have hh (y : Site c): ContinuousAt (fun u:Config G f=> S.frames u t y x) 1:= by
    have he := continuousAt_pi.mp (selects S H y) x
    apply he.congr; filter_upwards [precinct S (G:=G)] with u hu; unfold StepData.frames Patch.frame;rw [if_pos (hu _)]
 have hp: Continuous (fun U:Config G f=>travel (expandAt (S.ratio.embed b.1) U) x.val (S.repath b.2)):= (continuous_travel _ _).comp (show Continuous (expandAt (K:=G.El) (S.ratio.embed b.1)) from by unfold expandAt; fun_prop)
 exact ((hh b.1).mul hp.continuousAt).mul (hh (b.1+Lattice.step b.2)).inv
lemma look (t: S.Choices): ContinuousAt (fun x: Config G f=> S.prediction x t) 1:= by
 apply continuousAt_pi.mpr; intro i
 let F:=fun x:Config G f=> S.connector x t.1 i
 have ht:= S.patch.best_open.mem_nhds (checks S H t.1 i)
 have hh : ContinuousAt S.patch.best (F 1):= (Patch.best_cont S.patch H).continuousAt ht
 have hx: ContinuousAt F 1:= dance S H ..
 apply (hh.comp (f:=F) hx).congr; refine (hx.tendsto.eventually ht)|>.mono fun x h=> ?_
 dsimp only [Function.comp_apply]; change S.patch.best (F x)=S.patch.predict S.kernel (F x) (t.2 i);rw [Patch.predict,if_pos (show S.patch.usesBest _ (F x) from h)]
lemma prediction_zero_cont : ContinuousAt (predictor (G:=G) S) 1:=by
 let F:= orbLift (f:=f) (G:=G)
 have hx: ContinuousAt (fun U:Config G f=>S.prediction U (directive S)) (F 1):= by unfold F; rw [lift_one]; exact look S H _
 have hh:= hx.comp (f:=F) (show ContinuousAt F 1 from (lift_cont G (n:=f)).continuousAt)
 apply continuousAt_pi.mpr; intro i; exact continuousAt_pi.mp hh i.val -- 1 argument cast
lemma shared (t : S.Choices): (fun U: Config G f=> S.prediction U t) =ᶠ[𝓝 1] (fun U=> S.prediction U (directive S)):= by
 let p:=directive S
 have Hs i : ∀ᶠ U:Config G f in 𝓝 1, S.patch.usesBest S.kernel (S.connector U t.1 i):= (dance S H t.1 i).tendsto.eventually (S.patch.best_open.mem_nhds (checks S H _ _))
 filter_upwards [precinct S (G:=G),eventually_all.mpr Hs] with i hi hx
 have hr: S.frames i t.1= S.frames i p.1:= by ext1 y; unfold StepData.frames Patch.frame; rw [if_pos (hi _),if_pos (hi _)]
 ext1 z; have hh: S.connector i t.1 z=S.connector i p.1 z:=by unfold StepData.connector; rw [hr]
 change S.patch.predict S.kernel (S.connector i t.1 z) _= S.patch.predict S.kernel (S.connector i p.1 z) _;rw [←hh,Patch.predict,Patch.predict, if_pos (hx z),if_pos (hx z)]
-- torus density equals tag-independent near identity for any β
lemma branchKernel : ∀ᶠ U:Config G f in 𝓝 1,∀ β:ℝ,∀ V: Config G c, S.density β U V=S.noise β (S.prediction U (directive S)) V:=by
 filter_upwards [eventually_all.mpr (shared S H)] with x hx b V
 unfold StepData.density; simp_rw [fun i=> show S.prediction x i=S.prediction x (directive S) from hx i,← Finset.sum_mul,S.chosen H,one_mul]
omit H in
lemma goat_cont (k:Site f→ G.El) : Continuous (goat k):=by
 apply continuous_pi; intro i; simp_rw [goat_at]; fun_prop
lemma look_flat (U:spins G f)(k:Site f→G.El)(h:compatible k)(hh:goat k U=1): ContinuousAt (predictor S) U:=by
 let v :=k ∘ S.ratio.embed
 have hx:= prediction_zero_cont S H; rw [← hh] at hx
 have ht: predictor S = goat (v⁻¹) ∘ predictor S ∘ (goat k):=by
    ext1 z; dsimp only [Function.comp_apply]; rw [prediction_flow S H z k h,← show v=k∘ _ from rfl, goat_pair,inv_mul_cancel,goat_one]
 change ContinuousAt (predictor S) U
 rw [ht]; exact (goat_cont (v⁻¹)).continuousAt.comp (hx.comp (goat_cont k).continuousAt)
end YM.RegulatorIR.Geometry
