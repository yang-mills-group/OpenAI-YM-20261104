import YM.WilsonCoeffUV.Step.Ward.Transport
/-!
# Real coordinate regauging germ at trivial

Comparison of two arbitrary *analytic backgrounds*, related by lattice gauge
and signed affine pull. Rotated trees need not be repeated; we re-tree using
Haar on all free variables. Formal use takes only its log jets. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Power
open Lattice Laurent Bloch Exterior Wilson Precision RG Function Filter
open Blue MeasureTheory Set Metric Matrix Gauge
open FreeResolvent Tree
open YM.PertExtension.Chart (tangent physical expLinks jacobian fee)
open scoped ContDiff Topology BigOperators Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {c f : Side}{G:Gauge}(S:StepData c f)(F:Forest S.ratio)

def vcloth (G:Gauge): Lawn (Active G F)≃L[ℝ] (F.Free→G.Color):= LinearEquiv.toContinuousLinearEquiv {
     toFun:= profile F
     invFun:= active F
     left_inv:= active_profile F
     right_inv:=fun _=>rfl
     map_add':=fun _ _=>rfl
     map_smul':=fun _ _=>rfl }
lemma v_extend (q:Lawn (Active G F)) : mantle (reveal G S F *ᵥ q)=F.drape (expLinks G _ (vcloth S F G q)) := by
  let P:= vcloth S F G
  let u:=P q
  have he : reveal G S F *ᵥ q = flatten (Bid.stretch (S:=S) F (0,u)) := chart_flow S F u
  rw [he, placed]; funext i
  have hx := Work.F01.collect_vertical (S:=S) F u i
  rw [Work.F03.represent_link]
  change G.lieExp (collect G (Bid.stretch (S:=S) F (0,u)) i)=_
  rw [hx]; split
  next h => rw [G.mat_lieExp_zero]; exact (F.on_tree _ ⟨i,h⟩).symm
  next h => exact (F.off_tree (expLinks G _ u) ⟨i,h⟩).symm
lemma prism (u:F.Free→G.Color)(Ñ:ChartRatio G)(h:LocalRatio Ñ) : unhaar Ñ (reveal G S F*ᵥ (vcloth S F G).symm u) =∑ i:F.Free, Real.log (Ñ.J (u i)) := by
  unfold unhaar
  let A:=reveal G S F *ᵥ (vcloth S F G).symm u
  have he (i : Edge (Site f)) : coatC G (dyes A i)= if w:i∈F.trunks then 0 else u ⟨i,w⟩ := by
    rw [dyes,ContinuousLinearEquiv.apply_symm_apply]; unfold A
    have hx:= chart_flow S F u; rw [show (vcloth S F G).symm u = active F u from rfl,hx]
    apply Work.F01.collect_vertical F u i
  let B:=F.trunksᶜ
  let f i:=Real.log (dij Ñ (dyes A i))
  change ∑ i,f i=_
  calc
    _ = ∑ i∈B, f i := Eq.symm (Finset.sum_subset (Finset.subset_univ B) (fun i _ hx=> by unfold f dij; rw [he,dif_pos ?_,h.anchored,Real.log_one]; simpa [B] using hx))
    _ = _ := by
      rw [Finset.sum_subtype B (p:=fun i=>i ∉ F.trunks) (by simp [B])]; apply Finset.sum_congr rfl; intro i _; unfold f dij; rw [he,dif_neg i.property]
lemma log_event {Ñ:ChartRatio G}(h:LocalRatio Ñ) :
    ∀ᶠ u : F.Free→G.Color in 𝓝 0, Ñ.scale^Fintype.card F.Free * Real.exp (unhaar Ñ (reveal G S F *ᵥ (vcloth S F G).symm u))=jacobian Ñ u := by
  have he i : ContinuousAt (fun x:F.Free→G.Color=>x i) 0:=(continuous_apply i).continuousAt
  filter_upwards [eventually_all.mpr fun i=> (he i).eventually (by
    change ∀ᶠ x : G.Color in 𝓝 0, x∈ball 0 Ñ.radius; exact ball_mem_nhds _ h.patch)] with u hu
  rw [prism S F u Ñ h, Real.exp_sum, PertExtension.Chart.jacobian];
  have hx i : fee Ñ (u i)=Ñ.scale*Ñ.J (u i) := max_eq_left (mul_pos h.scale (h.pos _ (hu i))).le
  simp_rw [hx,Real.exp_log (h.pos _ (hu _)),Finset.prod_mul_distrib]; simp

section coarse
variable {Y:Type}[Fintype Y]
/-- Test two analytic background gauges, exponent argument already unscaled. -/
structure TurnsG (s:Signed)(b:Site c)(q:Lawn Y→Site c→G.El)(X X':Lawn Y→TreeVars G c) : Prop where
  g₀ : Green X
  g₁ : Green X'
  f₀ : X 0=0
  f₁ : X' 0=0
  gauge (i:Site c) : Green fun w=>G.mat (q w i)
  shift : ∀ᶠ w:Lawn Y in 𝓝 0, mantle (X' w)= Lattice.gauge (q w) (pull s b (mantle (X w)))

variable (s:Signed)(b:Site c)(q:Lawn Y→Site c→G.El)
def drifter (w:Lawn Y) := q w ∘ S.ratio.parent
-- Axis and auxiliary
def walk (v:(F.Free→G.Color)×Lawn Y) := retract S F s b (drifter S q v.2) (expLinks G _ v.1)
def mapLog (p:F.Slice G): F.Free→G.Color:= fun i=> LocalH.snap G (p i)
def surf (v:(F.Free→G.Color)×Lawn Y):= mapLog (S:=S) F (walk S F s b q v)

section smooth
variable {q} {X X':Lawn Y→TreeVars G c}(H:TurnsG s b q X X')
include H
lemma sail_root (i j : Site c): q 0 i=q 0 j := by
  have he : mantle (X' 0)= Lattice.gauge (q 0) (pull s b (mantle (X 0))) := by have := mem_of_mem_nhds H.shift; exact this
  rw [H.f₀,H.f₁,mantle_zero] at he; exact force_const _ _ _ he.symm i j
lemma sail_zero : walk S F s b q 0=1 := by
  have he : expLinks G F.Free 0=1 := funext fun _=> G.mat_lieExp_zero
  have hh : F.drape (1:F.Slice G)=1 := by funext i; by_cases hx:i∈F.trunks; exact F.on_tree _ ⟨i,hx⟩; exact F.off_tree _ ⟨i,hx⟩
  have hV : process S s b (drifter S q 0) 1=1 := by rw [process,pull_first]; funext i; simp [drifter,Lattice.gauge,sail_root s b H _ 0]
  unfold walk; change retract S F s b (drifter S q 0) (expLinks G F.Free 0)=_
  rw [he,retract,hh,hV,← hh]; exact coll_once ..
omit [Fintype Y] H in
private lemma aux_trav {Z:Type}[NormedAddCommGroup Z][NormedSpace ℝ Z]{U: Z→Config G f}
    (h:∀ i,ContDiffAt ℝ ω (fun x=>G.mat (U x i)) 0) (w:Walk)(u:Site f): ContDiffAt ℝ ω (fun x=> G.mat (travel (U x) u w)) 0:= by
  induction w generalizing u with
  | nil=> exact contDiffAt_const
  | cons a l ih=>
    simp only [travel, G.mat_mul]; refine ContDiffAt.mul ?_ (ih _); unfold Lattice.Step.read; split
    · exact Push.Loops.mat_inv_diff (h _)
    exact h _
lemma crest (e:Site f) : ContDiffAt ℝ ω (fun w:(F.Free→G.Color) × Lawn Y=> G.mat ((F.foldAt (process S s b (drifter S q w.2) (F.drape (expLinks G _ w.1)))* drifter S q w.2) e)) 0 := by
  let C:= (F.Free→G.Color) × Lawn Y
  let U (p:C):= F.drape (expLinks G F.Free p.1); let W (p:C):= process S s b (drifter S q p.2) (U p)
  have he i: ContDiffAt ℝ ω (fun x:C=> G.mat (U x i)) 0 := by
    by_cases hh:i∈ F.trunks
    · simp_rw [show ∀ x,U x i=1 from fun x=> F.on_tree _ ⟨i,hh⟩]; exact contDiffAt_const
    simp_rw [show ∀ x,U x i=G.lieExp (x.1 ⟨i,hh⟩) from fun x=> F.off_tree _ ⟨i,hh⟩];
    exact G.exp_jet.contDiffAt.comp (f:=fun x:C=>x.1 ⟨i,hh⟩) 0 ((contDiffAt_apply ℝ _ _ _).comp (f:=Prod.fst) 0 contDiffAt_fst)
  have hg (i): ContDiffAt ℝ ω (fun p:C=>G.mat (drifter S q p.2 i)) 0 :=
    ContDiffAt.comp (g:=fun w=>G.mat (q w (S.ratio.parent i))) (f:=Prod.snd) (0:C) (H.gauge _) contDiffAt_snd
  have ht i : ContDiffAt ℝ ω (fun p:C=>G.mat (W p i)) 0 := by
    have hp : ContDiffAt ℝ ω (fun p:C=>G.mat (pull s (S.ratio.embed b) (U p) i)) 0 := by
      unfold pull Lattice.Step.read; split
      · exact Push.Loops.mat_inv_diff (he _)
      exact he _
    change ContDiffAt ℝ ω (fun p:C=>G.mat _) 0
    unfold W process Lattice.gauge; simp only [G.mat_mul]
    exact ((hg _).mul hp).mul (Push.Loops.mat_inv_diff (hg _))
  have hv i: ContDiffAt ℝ ω (fun x:C=> G.mat (F.foldAt (W x) i)) 0 := by unfold Forest.foldAt; apply Push.Loops.mat_inv_diff; exact aux_trav ht _ _
  exact (hv e).mul (hg e)
lemma mesh_forms (e : F.Free): ContDiffAt ℝ ω (fun w:(F.Free→G.Color)×Lawn Y => G.mat (walk S F s b q w e)) 0 := by
  let C:= (F.Free→G.Color) × Lawn Y
  let U (p:C):= F.drape (expLinks G F.Free p.1); let W (p:C):= process S s b (drifter S q p.2) (U p)
  have he i: ContDiffAt ℝ ω (fun x:C=> G.mat (U x i)) 0 := by
    by_cases hh:i∈ F.trunks
    · simp_rw [show ∀ x,U x i=1 from fun x=> F.on_tree _ ⟨i,hh⟩]; exact contDiffAt_const
    simp_rw [show ∀ x,U x i=G.lieExp (x.1 ⟨i,hh⟩) from fun x=> F.off_tree _ ⟨i,hh⟩];
    exact G.exp_jet.contDiffAt.comp (f:=fun x:C=>x.1 ⟨i,hh⟩) 0 ((contDiffAt_apply ℝ _ _ _).comp (f:=Prod.fst) 0 contDiffAt_fst)
  have hg (i): ContDiffAt ℝ ω (fun p:C=>G.mat (drifter S q p.2 i)) 0 :=
    ContDiffAt.comp (g:=fun w=>G.mat (q w (S.ratio.parent i))) (f:=Prod.snd) (0:C) (H.gauge _) contDiffAt_snd
  have ht i : ContDiffAt ℝ ω (fun p:C=>G.mat (W p i)) 0 := by
    have hp : ContDiffAt ℝ ω (fun p:C=>G.mat (pull s (S.ratio.embed b) (U p) i)) 0 := by
      unfold pull Lattice.Step.read; split
      · exact Push.Loops.mat_inv_diff (he _)
      exact he _
    change ContDiffAt ℝ ω (fun p:C=>G.mat _) 0
    unfold W process Lattice.gauge; simp only [G.mat_mul]
    exact ((hg _).mul hp).mul (Push.Loops.mat_inv_diff (hg _))
  have hv i: ContDiffAt ℝ ω (fun x:C=> G.mat (F.foldAt (W x) i)) 0 := by unfold Forest.foldAt; apply Push.Loops.mat_inv_diff; exact aux_trav ht _ _
  change ContDiffAt ℝ ω (fun x:C=>G.mat ((F.foldAt (W x) _* W x _)* (F.foldAt (W x) _)⁻¹)) 0
  simp only [G.mat_mul]; exact ((hv _).mul (ht _)).mul (Push.Loops.mat_inv_diff (hv _))
lemma surf_diff : ContDiffAt ℝ ω (surf S F s b q) 0 := by
  apply contDiffAt_pi.mpr; intro i
  exact ContDiffAt.comp (g:=G.plog) _ (by rw [show G.mat (walk S F s b q 0 i)=1 from by rw [sail_zero S F s b H]; rfl]; exact G.plog_diff) (mesh_forms S F s b H i)
lemma surf_zero : surf S F s b q 0=0 := by unfold surf mapLog LocalH.snap; rw [sail_zero S F s b H]; funext i; simp
lemma surf_auth : ∀ᶠ v:(F.Free→G.Color)×Lawn Y in 𝓝 0, expLinks G F.Free (surf S F s b q v) = walk S F s b q v := by
  have ht i: Tendsto (fun v=>walk S F s b q v i) (𝓝 0) (𝓝 1):= by
    apply Push.Loops.tendsto_mat.mpr
    have he := (mesh_forms S F s b H i).continuousAt.tendsto; rw [sail_zero S F s b H] at he; exact he
  filter_upwards [eventually_all.mpr fun i=> (ht i).eventually G.plog_right] with v hv; exact funext hv
end smooth
end coarse
end YM.WilsonCoeffUV.Power
