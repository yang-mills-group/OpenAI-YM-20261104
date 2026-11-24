import YM.UVExt.JetDelivery
import YM.Push.LOOP_COEFFICIENT.GermWard

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.UVExt.Paths
open RG Function Filter Wilson Precision Lattice Laurent Bid Exterior Matrix Tensor Set
open Next.Free.UV Work.F02
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {M : ℕ→PathData G} {W : Shadow G} {σ C Λ : ℝ} {p : Clip}
variable {n : Side} (v : Dir G n) {e q : ℕ}
local notation "⨳" => ((Fintype.card Signed:ℝ)⁻¹)

noncomputable def knotted (n : Side) (p : Clip) (U : PathData G) (v : Dir G n) := mainTerm p U (represent v)
noncomputable def tread (n : Side) (U : PathData G) (v : Dir G n) := Precision.loop U (represent v)
noncomputable def centered (n : Side) (U : PathData G) (p : Clip) (v : Dir G n) := secondTerm p U (represent v)
lemma main_analytic (U : PathData G) (ht : U.Bounds p σ C Λ) : ContDiffAt ℝ ω (knotted n p U) 0 := (Work.F02.answer G _ _ σ _ _ ht).crown _ _ (fun (y : Dir G n) =>represent y) link_one (fun e=> Work.F03.represent_smooth e |>.contDiffAt)
lemma loop_analytic (U : PathData G) (ht : U.Bounds p σ C Λ) : ContDiffAt ℝ ω (tread n U) 0 := Push.Loops.loop_diff (fun i=> Work.F03.represent_smooth .. |>.contDiffAt) ht
lemma atom_analytic (k) (U : ℕ→RG.Atom G k) (ht : SumBudget (fun i=>(U i).budget σ) C) (hσ : 0<σ) (s : Signed) : ContDiffAt ℝ ω (fun x : Dir G n=>uncut U (pull s 0 (represent x))) 0 := by
  apply Work.F02.uncut_contDiffAt hσ ht (A:=pull s 0 ∘ represent); intro j
  dsimp only [Function.comp_apply]; unfold pull Lattice.Step.read; split
  · exact Push.Loops.mat_inv_diff ((Work.F03.represent_smooth _).contDiffAt)
  exact (Work.F03.represent_smooth _).contDiffAt
lemma centered_analytic (U : PathData G) (ht : U.Bounds p σ C Λ) : ContDiffAt ℝ ω (centered n U p) 0 := by
  change ContDiffAt ℝ ω (fun x : Dir G n=> centered n U p x) 0
  rw [show (fun x : Dir G n=> centered n U p x)=fun x=> knotted n p U x- ⨳ * ∑ s : Signed, (uncut U.cubic (pull s 0 (represent x))+uncut U.quartic (pull s 0 (represent x))) by
      funext x; unfold knotted mainTerm centered secondTerm Patch.average; simp only [Finset.sum_add_distrib]; ring] -- congr unneeded
  exact ContDiffAt.sub (main_analytic _ ht) (contDiffAt_const.mul (ContDiffAt.sum fun i _=> (atom_analytic _ _ ht.three ht.width i).add (atom_analytic _ _ ht.four ht.width i)))

lemma spiral_jet e (h : PaidShadow W C Λ σ) (ht : 0<σ) : tag e (spiral W v) = ⨳ * ∑ s:Signed, ∑ x, tag e (song (pulled v s) x W.loop) := by
  let F₁ s := ∑ x, song (pulled v s) x W.loop
  have hg (s : Signed) : ContDiff ℝ ∞ (F₁ s) := flow_sum fun x=> song_smooth _ h.coeffTwo ht x
  change tag e (⨳ • ∑ s,F₁ s)=_
  rw [tag_smul _ (flow_sum hg),tag_sum _ hg]
  exact congr_arg (⨳ * ·) (Finset.sum_congr rfl fun s _=> tag_sum _ (fun x=>song_smooth _ h.coeffTwo ht x))

namespace Passing
variable (h : Passing M W σ C Λ p)
include h
lemma flow_bench : Tendsto (fun i=> tag q (bench (wick (M i)) v p)) atTop (𝓝 (tag q (bench W v p))) := by
  classical
  let F (Q : Shadow G) s (j : Face (Per n)) := tag q (ringLit (pulled v s) p j) + (1/2:ℝ)*tag q (words (pulled v s) j.1 (fun k=> score Q j.2 k.1))
  have hF (s : Signed) (j : Face (Per n)) : Tendsto (fun i=> F (wick (M i)) s j) atTop (𝓝 (F W s j)) := tendsto_const_nhds.add (Tendsto.const_mul (1/2:ℝ) (words_tends (C:= ((Fintype.card G.ColorIndex:ℝ)*C^2)) _ (fun i k=>score (wick (M i)) j.2 k.1) (h.mask.mono fun i hi=>paid_chord _ (shadow_pay _ hi) _) (tendsto_pi_nhds.mpr (fun z=> (tendsto_pi_nhds.mp (h.row j.2) z.1.1).mul ((tendsto_pi_nhds.mp (h.row j.2) z.1.2)))) h.width j.1 q 0))
  rw [bench_jet q h.limit h.width]; exact (Tendsto.const_mul ⨳ (tendsto_finsetSum _ fun s hs=> tendsto_finsetSum Finset.univ (fun j _=> hF s j))).congr' (h.mask.mono fun i hi=>Eq.symm (bench_jet _ (shadow_pay _ hi) h.width _)) -- fix
lemma flow_jet : Tendsto (fun i=>tag e (payload (wick (M i)) v p)) atTop (𝓝 (tag e (payload W v p))) := by
  let A (Q : Shadow G) := ∑ s : Signed, ((∑ x, tag e (song (pulled v s) x Q.cubic)) + ∑ x, tag e (song (pulled v s) x Q.quartic))
  have hA : Tendsto (fun i=>A (wick (M i))) atTop (𝓝 (A W)) := tendsto_finsetSum _ fun i _ => (tendsto_finsetSum _ fun x _=> song_tends (C:=C) (pulled v i) _ (h.mask.mono fun i hi=> (shadow_pay _ hi).coeffThree) h.three h.width _ _ _).add (tendsto_finsetSum _ fun x _=> song_tends (C:=C) (pulled v i) _ (h.mask.mono fun i hi=> (shadow_pay _ hi).coeffFour) h.four h.width _ _ _)
  rw [payload_jet e h.limit h.width]; exact ((h.flow_bench (q:=e) v).add (hA.const_mul ⨳)).congr' (h.mask.mono fun i hi=>Eq.symm (payload_jet _ (shadow_pay _ hi) h.width _))
lemma flow_loop : Tendsto (fun i=>tag q (spiral (wick (M i)) v)) atTop (𝓝 (tag q (spiral W v))) := by
  rw [spiral_jet _ _ h.limit h.width]; exact (Tendsto.const_mul ⨳ (tendsto_finsetSum _ fun i _=>tendsto_finsetSum _ fun x _=>song_tends (σ:=σ) (pulled v i) (fun j=>(wick (M j)).loop) (h.mask.mono fun i hi=>(shadow_pay _ hi).coeffTwo) h.loop h.width x _ _)).congr' (h.mask.mono fun i hi=> Eq.symm (spiral_jet v _ (shadow_pay (M i) hi) h.width))

section stable
variable (n q)
include h
private lemma mainTensor' : ∃ P : T (Dir G n) ℝ q, Tendsto (spray (fun i=>knotted n p (M i)) q) atTop (𝓝 P) ∧ Tensor.diagonal P=fun v=> tag q (payload W v p) :=
 tensor_lim (f:=fun i=> knotted n p (M i)) (h.mask.mono fun i hi=> (main_analytic (M i) hi).of_le le_top) (fun v=>tag _ (payload W v p)) (fun v=> (h.flow_jet v).congr' <| h.mask.mono fun i hi=>congr_arg (tag q) (payload_main _ _ hi))
noncomputable def planeTensor := (mainTensor' (M:=M) n q h).choose
private lemma loopTensor' : ∃ P : T (Dir G n) ℝ q, Tendsto (spray (fun i=>tread n (M i)) q) atTop (𝓝 P) ∧ Tensor.diagonal P=fun v:Dir G n=>tag q (spiral W v) :=
 tensor_lim (f:=fun i=> tread n (M i)) (h.mask.mono fun i hi=> (loop_analytic (M i) hi).of_le le_top) (fun v=>tag _ (spiral W v)) (fun v=> (h.flow_loop v).congr' <| h.mask.mono fun i hi=>congr_arg (tag q) (spiral_loop _ _ hi))
private lemma benchTensor' : ∃ P : T (Dir G n) ℝ q, Tendsto (spray (fun i=>centered n (M i) p) q) atTop (𝓝 P) ∧ Tensor.diagonal P=fun v=> tag q (bench W v p) :=
 tensor_lim (f:=fun i=> centered n (M i) p) (h.mask.mono fun i hi=> (centered_analytic (M i) hi).of_le le_top) (fun v=>tag _ (bench W v _)) (fun v=> (h.flow_bench v).congr' <| h.mask.mono fun i hi=>congr_arg (tag q) (bench_raw _ _ hi))
noncomputable def spiralTensor := (loopTensor' (M:=M) n q h).choose
noncomputable def economicTensor := (benchTensor' (M:=M) n q h).choose
lemma mainLimit : Tendsto (spray (fun i=>knotted n p (M i)) q) atTop (𝓝 (planeTensor n q h)) ∧ Tensor.diagonal (planeTensor n q h)=fun v=>tag q (payload W v p) := (mainTensor' (M:=M) n q h).choose_spec
lemma loopLimit : Tendsto (spray (fun i=>tread n (M i)) q) atTop (𝓝 (spiralTensor n q h)) ∧ Tensor.diagonal (spiralTensor n q h)=fun v=>tag q (spiral W v) := (loopTensor' (M:=M) n q h).choose_spec
lemma centeredLimit : Tendsto (spray (fun i=>centered n (M i) p) q) atTop (𝓝 (economicTensor n q h)) ∧ Tensor.diagonal (economicTensor n q h)=fun v=>tag q (bench W v p) := (benchTensor' (M:=M) n q h).choose_spec
lemma groomed : lucid (fun i=>knotted n p (M i)) := h.mask.mono fun i hi=>(main_analytic _ hi).of_le le_top
lemma loop_groomed : lucid (fun i=>tread n (M i)) := h.mask.mono fun i hi=>(loop_analytic _ hi).of_le le_top
lemma second_groomed : lucid (fun i=>centered n (M i) p) := h.mask.mono fun i hi=>(centered_analytic _ hi).of_le le_top
lemma everyMain : Junction (fun i=> knotted n p (M i)) (fun i=>knotted n p (M i)) q := fun k _=> ⟨planeTensor n k h,h.mainLimit n k |>.1,h.mainLimit n k |>.1⟩
lemma everyLoop : Junction (fun i=> tread n (M i)) (fun i=>tread n (M i)) q := fun k _=> ⟨spiralTensor n k h,h.loopLimit n k |>.1,h.loopLimit n k |>.1⟩
end stable
end Passing
end YM.UVExt.Paths
