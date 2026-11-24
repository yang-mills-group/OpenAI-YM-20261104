import YM.WilsonCoeffUV.Step.Ward.Course
/-! Mix and re-centre from the two shores. The signed Ward partner even
when it moves the marked origin across coarse blocks. -/
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
variable {Y:Type}[Fintype Y]

/- canonical orientation start(X,z) to end(X',surfCoord). -/
variable (M:Matrix (Woods G f) (Woods G c) ℝ) (X X': Lawn Y→ TreeVars G c)

def rise (u: Lawn Y) : Lawn (Active G F):= ((reveal G S F).transpose*M)*ᵥ X u

def ride (w:Lawn (Active G F⊕Y)) : (F.Free→G.Color) × Lawn Y:= (vcloth S F G (leftArm w+rise S F M X (rightArm w)),rightArm w)
def wend (g: (F.Free→G.Color) × Lawn Y→ (F.Free→G.Color))(w:Lawn (Active G F⊕Y)): Lawn (Active G F):= (vcloth S F G).symm (g (ride S F M X w))-rise S F M X' (rightArm w)

lemma ride_diff (h:Green X) : Green (ride S F M X) := by
  classical
  have ht: Green fun w:Lawn (Active G F ⊕ Y)=> X (rightArm w) := h.comp (f:=rightArm) 0 rightGreen
  exact ((vcloth S F G).contDiff.contDiffAt.comp (f:=fun w=> leftArm w+rise S F M X (rightArm w)) 0 (ContDiffAt.add leftGreen (((reveal G S F).transpose*M).mulVecLin.toContinuousLinearMap.contDiff.contDiffAt.comp 0 ht))).prodMk rightGreen
omit [Fintype Y] in
lemma ride_zero (h:X 0=0): ride S F M X 0=0:= by rw [ride,rightZero,leftZero,rise,h, Matrix.mulVec_zero,add_zero,map_zero]; rfl
lemma wend_diff (h:Green X) (e:X 0=0)(h':Green X') (g: (F.Free→G.Color) × Lawn Y→ (F.Free→G.Color))(hg:ContDiffAt ℝ ω g 0) : Green (wend S F M X X' g) := by
  classical
  have ht: Green fun w:Lawn (Active G F ⊕ Y)=> X' (rightArm w) := h'.comp (f:=rightArm) 0 rightGreen
  rw [← ride_zero S F M X e] at hg
  refine ContDiffAt.sub ((vcloth S F G).symm.contDiff.contDiffAt.comp (f:=fun w=>g (ride S F M X w)) _ (hg.comp (f:=ride S F M X) 0 (ride_diff S F M X h))) ?_
  exact (((reveal G S F).transpose*M).mulVecLin.toContinuousLinearMap.contDiff.contDiffAt.comp (f:=fun w=>X' (rightArm w)) 0 ht)
omit [Fintype Y] in
lemma wend_zero (g:(F.Free→G.Color) × Lawn Y→ (F.Free→G.Color))(hz:g 0=0)(h:X 0=0)(h':X' 0=0): wend S F M X X' g 0=0:= by rw [wend,ride_zero _ _ _ _ h,hz,rightZero,rise,h',Matrix.mulVec_zero,map_zero,sub_zero]

-- mix west/east

def bag (U Y : Type)(Z:Type) (A:Lawn (U⊕Y)→ Lawn U)(B:Lawn Y→Lawn Z)(u:Lawn (U⊕Y)):= Sum.elim (A u) (B (rightArm u))
def west := bag (Active G F) Y _ leftArm X
def east (g: (F.Free→G.Color) × Lawn Y→ (F.Free→G.Color)):= bag _ Y _ (wend S F M X X' g) X'
omit [Fintype Y] in
lemma west_log (hM:M=reveal G S F*((reveal G S F).transpose*M))(u : Lawn (Active G F⊕Y)) :
    camSlice G S F M *ᵥ west S F X u = reveal G S F *ᵥ (vcloth S F G).symm (ride S F M X u).1 := by
  let r := ride S F M X u
  simp only [camber_tree,Matrix.add_mulVec,← Matrix.mulVec_mulVec,left_hit,right_hit]
  change _ + M *ᵥ X (rightArm u)= _ *ᵥ (vcloth S F G).symm (vcloth S F G _)
  rw [ContinuousLinearEquiv.symm_apply_apply,Matrix.mulVec_add];
  congr 1; unfold rise; rw [Matrix.mulVec_mulVec,←hM]
omit [Fintype Y] in
lemma east_log (g)(hM:M=reveal G S F * ((reveal G S F).transpose*M))(u : Lawn (Active G F⊕Y)) :
    camSlice G S F M *ᵥ east S F M X X' g u = reveal G S F *ᵥ (vcloth S F G).symm (g (ride S F M X u)) := by
  rw [camber_tree,Matrix.add_mulVec,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,left_hit,right_hit];
  change reveal G S F *ᵥ ((vcloth S F G).symm _ - rise S F M X' (rightArm u))+M*ᵥ X' (rightArm u)=_
  rw [Matrix.mulVec_sub,rise,Matrix.mulVec_mulVec, ←hM, sub_add_cancel]
lemma west_diff (h:Green X) : Green (west S F X) := by
  classical
  apply sumGreen leftGreen; exact h.comp (f:=rightArm) 0 rightGreen
omit [Fintype Y] in
lemma west_zero (h:X 0=0): west S F X 0=0 := by unfold west bag; rw [rightZero,h,leftZero]; exact funext fun x=> by cases x<;>rfl
lemma east_diff (h:Green X)(e:X 0=0)(h':Green X')(g)(hg:ContDiffAt ℝ ω g 0): Green (east S F M X X' g) := by
  classical
  refine sumGreen (wend_diff S F M X X' h e h' g hg) ?_
  exact h'.comp (f:=rightArm) 0 rightGreen
omit [Fintype Y] in
lemma east_zero (h:X 0=0)(h':X' 0=0)(g)(hg:g 0=0): east S F M X X' g 0=0:= by unfold east bag; rw [rightZero,h',wend_zero S F M X X' g hg h h']; exact funext fun x=> by cases x <;> rfl

section shift
variable (s:Signed)(b:Site c)(q:Lawn Y→Site c→G.El)(A:TurnsG s b q X X')
private abbrev armW := Lawn (Active G F⊕Y)
def fineRot (u : armW S F (G:=G) (Y:=Y)): Site f→G.El :=
  let k := drifter S q (rightArm u)
  let v := F.drape (expLinks G _ (ride S F M X u).1)
  F.foldAt (process S s b k v) * k
-- rotation of actual fine fields
include A in
lemma fine_rot_green (j) : Green fun u=> G.mat (fineRot S F M X s b q u j) := by
  have H : ContDiffAt ℝ ω (fun w:(F.Free→G.Color) × Lawn Y=> G.mat ((F.foldAt (process S s b (drifter S q w.2) (F.drape (expLinks G _ w.1)))* drifter S q w.2) j)) 0:= crest S F s b A j
  have he := ride_zero S F M X A.f₀; rw [← he] at H; exact H.comp (f:=ride S F M X) _ (ride_diff S F M X A.g₀)
include A
lemma turned (hM:M=reveal G S F*((reveal G S F).transpose*M)) :
  let t:=surf S F s b q
  let f:= fun u=> camSlice G S F M*ᵥ west S F X u
  let f':=fun u=> camSlice G S F M*ᵥ east S F M X X' t u
  ∀ᶠ w:armW S F in 𝓝 0,mantle (f' w)=Lattice.gauge (fineRot S F M X s b q w) (pull s (S.ratio.embed b) (mantle (f w))) := by
  intro t x y
  have hx:= (ride_diff S F M X A.g₀).continuousAt.tendsto; rw [ride_zero _ _ _ _ A.f₀] at hx
  filter_upwards [hx.eventually (surf_auth S F s b A)] with u hu
  dsimp only [y,x]
  rw [west_log _ _ _ _ hM u,east_log _ _ _ _ _ t hM u,v_extend,v_extend,ContinuousLinearEquiv.apply_symm_apply,ContinuousLinearEquiv.apply_symm_apply]
  unfold t; rw [hu];
  unfold walk retract; rw [tree_coll,process, together]; rfl
omit A [Fintype Y] in
lemma fine_rot_roots (u) : fineRot S F M X s b q u ∘ S.ratio.embed=q (rightArm u) := by
  funext i; simp [fineRot,F.fold_root,drifter,Lattice.Ratio.embed_parent]
lemma turn_complete (hM:M=reveal G S F*((reveal G S F).transpose*M)): TurnsG s (S.ratio.embed b) (fineRot S F M X s b q) (fun u=>camSlice G S F M*ᵥwest S F X u) (fun u=>camSlice G S F M*ᵥeast S F M X X' (surf S F s b q) u) := by
  classical
  have hg := board (camSlice G S F M)
  have ht:=surf_diff S F s b A
  have he:=west_zero S F X A.f₀; have hu:=east_zero S F M X X' A.f₀ A.f₁ _ (surf_zero S F s b A)
  refine ⟨?f',?d,by rw [he,Matrix.mulVec_zero],by rw [hu,Matrix.mulVec_zero],fun i=> fine_rot_green S F M X X' s b q A i,turned S F M X X' s b q A hM⟩
  case f' => unfold Green at hg; rw [← he] at hg; exact ContDiffAt.comp _ hg (west_diff S F X A.g₀)
  case d=> unfold Green at hg; rw [← hu] at hg; exact ContDiffAt.comp _ hg (east_diff S F M X X' A.g₀ A.f₀ A.g₁ _ ht)
end shift
end YM.WilsonCoeffUV.Power
