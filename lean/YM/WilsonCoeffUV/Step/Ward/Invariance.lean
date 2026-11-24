import YM.WilsonCoeffUV.Step.Ward.Covariance
/-! Vacuum invariant; no horizon growth restriction used on finite tori.
No actual-interaction derivative here. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Power
open Lattice Laurent Bloch Exterior Wilson Precision RG Function Filter
open Blue MeasureTheory Set Metric Matrix Gauge PowerSeries
open FreeResolvent Tree
open YM.PertExtension.Chart (tangent physical expLinks jacobian fee)
open scoped ContDiff Topology BigOperators Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {c f : Side}{G:Gauge}(S:StepData c f)(F:Forest S.ratio)

section law
variable {Z:Type} [Fintype Z][DecidableEq Z]
variable (M: Matrix (Woods G f) (Woods G c) ℝ)
variable (H Y:FreeResolvent.FaceRow)
variable (s:Signed)(b:Site c)(q:Lawn Z→Site c→G.El)(X X':Lawn Z→TreeVars G c)
variable (Ñ:ChartRatio G)
local notation "Ξ"=> surf S F s b q
local notation "θ"=> wend S F M X X' Ξ
local notation "Φ"=> fanWest (X:=Active G F) (spool X)
local notation "Ψ"=> reroll (spool X') (spool θ)

private lemma away_sign {Z:Type}[Fintype Z] {d: Lawn Z→ℝ}(h:Green d) (x:d 0≠0): Green fun i=>|d i| := by
  rcases lt_or_gt_of_ne x with ha|ha
  · apply (ContDiffAt.neg h).congr_of_eventuallyEq
    filter_upwards [h.continuousAt.eventually (gt_mem_nhds ha)] with i hi using abs_of_neg hi
  apply h.congr_of_eventuallyEq; filter_upwards [h.continuousAt.eventually (lt_mem_nhds ha)] with i hi using abs_of_pos hi

lemma shine_city (p: LocalRatio Ñ)(hM:M=reveal G S F*((reveal G S F).transpose*M))(E:TurnsG s b q X X') :
    let J:= loom (camSlice G S F M) (jet (unhaar Ñ))
    (motionJ (spool θ)).det*raiseE (Ψ J) = realS ((edgeM θ 0).det)*raiseE (Φ J) := by
  classical
  intro J
  let D:= Active G F
  let W:=Woods G c
  let Y:= west S F X; let B:=east S F M X X' Ξ
  let C:= city S F M Ñ
  have ht:= surf_diff S F s b E; have hv:= surf_zero S F s b E
  have hU:Y 0=0:= west_zero S F X E.f₀; have hV:B 0=0:=east_zero _ _ _ X X' E.f₀ E.f₁ _ hv
  have hu: Green Y:= west_diff _ _ X E.g₀; have hb:Green B:=east_diff S F M X X' E.g₀ E.f₀ E.g₁ _ ht
  have hy:C 0=0:= by unfold C city; rw [Matrix.mulVec_zero,unhaar_zero p]
  have hC: Green C:= by
    have h : camSlice G S F M *ᵥ 0=0:= Matrix.mulVec_zero _
    exact (show ContDiffAt ℝ ω _ _ from h.symm ▸ (show ContDiffAt ℝ ω (unhaar (n:=f) Ñ) (0:TreeVars G f) from unhaar_green p)).comp (f:=fun v=> camSlice G S F M*ᵥ v) 0 (board _)
  have hJ: J=jet C := loom_jet _ _ (unhaar_green p)
  have h₀ : Φ J=jet (C ∘ Y) := by rw [west_train S F X E.g₀ E.f₀,hJ]; exact traveling Y hu hU C hC
  have h₁ : Ψ J=jet (C ∘ B) := by rw [east_train S F M s b q X X' E,hJ]; exact traveling B hb hV _ hC
  let d (v:Lawn (Active G F⊕Z)) := (edgeM θ v).det
  have hs:= city_area S F M X X' s b q Ñ E p hM
  have hm : |d 0|=1:= arm_det S F M X X' s b q Ñ E p hM
  have hp' : d 0*d 0=1:= by rcases (abs_eq_abs.mp (show |d 0|=|(1:ℝ)| by rwa [abs_one])) with ha|ha <;> rw [ha]<;>norm_num
  have hg: Green (C ∘ Y):= (show ContDiffAt ℝ ω C (Y 0) from hU.symm ▸ hC).comp 0 hu
  have hh: Green (C ∘ B):= (show ContDiffAt ℝ ω C (B 0) from hV.symm ▸ hC).comp 0 hb
  have hf:=edge_green _ (wend_diff S F M X X' E.g₀ E.f₀ E.g₁ _ ht)
  have hx: Green d:= by unfold Green d; simp_rw [Matrix.det_apply']; apply ContDiffAt.sum; intro i _; exact ContDiffAt.mul contDiffAt_const (contDiffAt_prod (fun j _=> hf _ _))
  have hX : jet (fun v=>Real.exp ((C∘Y) v))=jet ((fun v=>|d v|)*(fun v=>Real.exp ((C∘B) v))) := jet_congr (Eventually.mono hs (fun i hi=> Eq.symm hi))
  rw [literal_exp hg (by rw [Function.comp_apply,hU,hy]), jet_mul (f:=fun v=> |d v|) (g:=fun v=>Real.exp ((C∘B) v)) (away_sign hx (left_ne_zero_of_mul (b:=d 0) (hp' ▸ one_ne_zero))) hh.exp,literal_exp hh (by rw [Function.comp_apply,hV,hy])] at hX
  rw [h₀,h₁,hX, show jet (fun v=>|d v|)=_ from det_jet S F M X X' s b q Ñ E p hM, ← mul_assoc,←mul_assoc (realS _),←map_mul, hp']; simp
end law

section witness
variable (H Y:FreeResolvent.FaceRow)(Q:Matrix (Body 1 f) (Body 1 c) ℝ){Ñ:ChartRatio G}
variable {P:PChart G f}(hp:shellK 2 P)(hz:P 0=shine (orbQ (precisionC G f H)))(he:S.patch.Branches S.kernel G)(p:LocalRatio Ñ)
    (hI:IsUnit (treeMatrix G S F H).det)(h:Inputs S Q (H.acts f) (Y.acts c))(hs:(H.acts f).transpose=H.acts f)
    (w:Warded (flash P))

include hp hz he p hI h hs w
lemma converge_transport {Z:Type} [Fintype Z] [DecidableEq Z]
    (s:Signed)(b:Site c){q:Lawn Z→ Site c→G.El}{X X':Lawn Z→TreeVars G c}(E: TurnsG s b q X X') :
    let M:=extractV G S F Q
    BridgeK (spool X) (spool X') (wend S F M X X' (surf S F s b q)) (treeMatrix G S F H) (orbC (precisionC G c Y)) (loom (camSlice G S F M) (jet (unhaar Ñ))) (unscaled S F Q P) (shot S F Q Ñ P):= by
  classical
  intro M
  let T:= surf S F s b q
  have ht:T 0=0:= surf_zero S F s b E
  have hM : M=reveal G S F * ((reveal G S F).transpose*M):= sweeps G S F Q Y hI h
  have hu := arm_det S F M X X' s b q Ñ E p hM
  refine ⟨wend_zero S F M X X' T ht E.f₀ E.f₁, wend_diff S F M X X' E.g₀ E.f₀ E.g₁ _ (surf_diff S F s b E), ?ig, ?b, shot_bill S F H Y Q hp hz he h hs, ?c, shine_city S F M s b q X X' Ñ p hM E, isUnit_iff_ne_zero.mpr (by intro hc; rw [hc] at hu; simp at hu)⟩
  case ig=> apply floor_pres (by simp [loom]); rw [jet_lead,unhaar_zero p,map_zero]
  case b=> exact floor_pres (T:=loom (overM G S F)) (by simp [loom]) (flash_blank (pack_zero S p))
  case c=> unfold unscaled; rw [map_add,map_add, wire_orbit S F M s b q X X' hM E _ _ (w s (S.ratio.embed b)),wind_price S F M s b q X X' he hM E]

theorem survives (v:∀ i, Pure (P i)): Warded (flash (winter S F H Y Q Ñ P)) := by
  classical
  intro s b Z hf q X X' E
  rw [winter_read S F H Y Q hp p he hs v,map_add,map_add,income, income]; refine congr_arg₂ (· + ·) ?_ rfl
  have hx := converge_transport S F H Y Q hp hz he p hI h hs w _ _ E
  let T:= treeMatrix G S F H
  have ht : T.transpose=T:=by unfold T treeMatrix; rw [transpose_submatrix,full_symmetric _ hs]
  have he : inside S F H Q Ñ P=Wick (Woods G c) T⁻¹ (raiseE (shot S F Q Ñ P)) := by simp_rw [inside,treeInverse,resolve,zero_smul,add_zero]; rfl
  rw [he]
  apply hx.read ht hI
  rw [← he]; exact inside_mass S F H Q p
end witness
end YM.WilsonCoeffUV.Power
