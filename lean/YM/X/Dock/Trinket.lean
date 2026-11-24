import YM.X.Dock.Stout
/-!
# first derivative distribution test. licenses PD extensions of Bolt.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PositionX.Chir.Dock
open Lattice Wilson Next.Rank LiftMark PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Shelf Tot
open Finset Metric MeasureTheory Filter Set Function Reed Ocean Stems Hinge Haze Fielding Print Tri Plate Imprint CellsInt Beamer Asymptotics Crate.Fund
open Maxwell (Green normal grad)
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge} {m k d:ℕ} {V:Type*} {n:Side} {q:ℕ+}{r R e c:ℝ}
local notation "ε"=> epsilon q
local notation "L"=>(atTop:Filter ℕ)
variable (u:E4→ℝ)(h:ContDiff ℝ ∞ u)(hq:1<q.val)
local notation "D"=> Maxwell.grad
variable (i:Axis)
include hq
lemma G_atlas : Atlas q 0 h0 Green:= ⟨air_graph _ _ rfl,fun hx hy h=> cope hq h hx hy 0 []⟩
lemma grad_atlas : Atlas q 1 (ds i h0) (pull i Green):= by
    rw [show h0= graphS [] 0 from rfl, graph_d]; refine ⟨(air 1).neg_mem (air_graph _ _ rfl),fun hx hy h=>?_⟩; refine ((cope hq h hx hy (0-step i) [i]).neg).congr fun k=>?_ ; simp only [cable,sprite_val,Pi.neg_apply, mul_neg]; rfl
abbrev swim (q:ℕ+)(u:E4→ℝ):Mist ℝ:= fun i z=> u (spot (epsilon q i) z)
include h
lemma shiftL (hr:R≥0):Focus q R 0 (swim q u) u:= ⟨visa_smooth [] h hr hq,fun _ z hz _ _=> h.continuous.continuousAt.tendsto.comp hz⟩
lemma hunt (hr:R≥0): Focus q R 0 (prospect i q (swim q u)) (D i u):= by
    have he:= Visa.asPow (c:=-1) (visa_smooth [i] h hr hq); simp only [List.length_cons,List.length_nil,Nat.zero_add,Nat.cast_one,neg_add_cancel,zpow_neg,zpow_one] at he; exact ⟨he,fun x z hz _ _=> forwards hq i u h x z hz⟩
abbrev cell (q:ℕ+)(d:ℕ)(F:Scaff)(k:ℕ):= pin q 0 (run q 0 d F) k
omit h hq in
lemma pull_green (w:E4)(h:w≠0): pull i Green (-w)= D i Green w := by unfold pull; rw [Pi.neg_apply, Maxwell.first_Green h, Maxwell.first_Green (neg_ne_zero.mpr h)];simp
variable (χ:Floor R)
lemma held : Integrable (fun x:E4=>χ.s x*(D i Green x * u x))∧ Integrable (fun x:E4=>χ.s x*(Green x * D i u x)) ∧ Integrable (fun x:E4=> - D i χ.s x *(Green x*u x)) ∧ (∫ x:E4,χ.s x*(D i Green x * u x))=(∫ x:E4, -D i χ.s x*(Green x*u x))-(∫ x:E4,χ.s x*(Green x* D i u x)):= by
   have hp: plot q (fun _=>0) 0:= plot.constant hq 0; let A:=cell q 0 h0; let C:= swim q u; have hx := own hq _ (G_atlas hq) hp χ.positive.le; have hh: Focus q R (-3) A Green:= by
        apply Focus.rise hq (j:= -2) _ χ.positive.le (by decide); simpa only [zero_add,zero_sub,Maxwell.even_Green,A,cell,Nat.add_zero,Nat.cast_ofNat,Pi.zero_def] using! hx -- dcast
   let B:=prospect i q A; have he: Focus q R (-3) B (D i Green):= by
        have hv:=own hq _ (grad_atlas hq i) hp χ.positive.le; rw [prospect_eq] at hv; refine ⟨hv.bank,fun z v hv' hz he=>?_⟩; simpa only [zero_add,zero_sub,pull_green i z hz,A,B,cell,Pi.zero_def] using! hv.foot z v hv' hz he
   have hY:=χ.positive; obtain ⟨ht,hW⟩:= magnify_mask hq χ (he.mix (shiftL u h hq χ.positive.le)); obtain ⟨hv,hg,H⟩:= range_focus hq χ i hh (west hq χ.positive.le (lt_add_one R) i (shiftL u h hq (R:=R+1) (by linarith))) (west hq χ.positive.le (lt_add_one R) i (hunt u h hq i (R:=R+1) (by linarith))); exact ⟨ht,hg,hv,tendsto_nhds_unique hW H⟩
omit hq
lemma green_weak (he:HasCompactSupport u): Integrable (fun x:E4=> D i Green x * u x)∧ Integrable (fun x:E4=> Green x * D i u x) ∧ (∫ x:E4,D i Green x *u x) = -(∫ x:E4,Green x*D i u x):= by
    obtain ⟨d,hR⟩:= Metric.isBounded_iff_subset_ball (0:E4)|>.mp he.isCompact.isBounded; let c:=max d 1; have hc:c>0:= zero_lt_one.trans_le (le_max_right ..); have h' : tsupport u ⊆ ball (0:E4) c:=hR.trans (ball_subset_ball (le_max_left ..))
    let χ:Floor (10*c):= ⟨⟨c,2*c,hc,by linarith⟩,by dsimp;linarith⟩; obtain ⟨hp,he,hS,h⟩:=held u h (q:=2) (by decide) i χ
    let f: ContDiffBump (0:E4):=χ.s; have hh(x:E4)(h:x∈tsupport u) : (f:E4→ℝ) =ᶠ[𝓝 x] (1:E4→ℝ):= Filter.mem_of_superset (isOpen_ball.mem_nhds (h' h)) (fun y hy=> f.one_of_mem_closedBall (ball_subset_closedBall hy));
    have hu(x:E4)(h:x∈tsupport u) : D i χ.s x=0:= by unfold Maxwell.grad Analysis.D; rw [(hh x h).fderiv_eq,show fderiv ℝ (1:E4→ℝ) x=0 from (hasFDerivAt_const (𝕜:=ℝ) 1 x).fderiv]; rfl -- unfold f and function
    have ht(x:E4): χ.s x*(D i Green x*u x)=D i Green x*u x∧ χ.s x*(Green x* D i u x)=Green x*D i u x∧ -D i χ.s x*(Green x*u x)=0:= by
       by_cases hv:x∈ tsupport u; · rw [show χ.s x=1 from (hh x hv).eq_of_nhds, hu x hv];simp
       simp [image_eq_zero_of_notMem_tsupport hv, Maxwell.grad, Analysis.D, fderiv_of_notMem_tsupport _ hv] -- indent
    simp_rw [fun x=>(ht x).1] at hp h -- can't rw binder?
    simp_rw [fun x=>(ht x).2.1] at he h; simp_rw [fun x=>(ht x).2.2, integral_zero,zero_sub] at h; exact ⟨hp,he,h⟩
end YM.PositionX.Chir.Dock
