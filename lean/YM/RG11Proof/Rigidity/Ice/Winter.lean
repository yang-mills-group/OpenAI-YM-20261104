import YM.RG11Proof.Rigidity.Ice.Balance
import Mathlib.Topology.Sequences

/-!
# Charges near identity. No lifting assumption needed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity.Ice
open Fields Labels Maxwell Function Extra.FD Reads Maxwell.Free Set Filter Pert.Position
open scoped Classical BigOperators Topology ContDiff InnerProductSpace
variable {G:Gauge}{F:Frames G}{d:ℕ}
local notation "V"=>G.Color
local notation "Y"=>V→L[ℝ] V

abbrev rays (i : G.ColorIndex) := (EuclideanSpace.basisFun G.ColorIndex ℝ) i
def nearest (O:Y) := ∑ i:G.ColorIndex, ⟪O (rays i)-rays i,O (rays i)-rays i⟫_ℝ
lemma near_cont : Continuous (nearest (G:=G)):= by
  have he (v : V) : Continuous fun O:Y=> O v - v:= (ContinuousLinearMap.apply ℝ V v).continuous.sub continuous_const
  unfold nearest; exact continuous_finsetSum _ fun i _=> (he _).inner (he _)
lemma near_one : nearest (1:Y)=0:= by unfold nearest; simp
lemma near_pos (O:Y):0≤nearest O:=Finset.sum_nonneg fun _ _=> real_inner_self_nonneg
lemma near_zero (O:Y)(h : nearest O = 0): O=1:=by
  let f:= O.toLinearMap
  suffices he : f=(1:Y).toLinearMap from ContinuousLinearMap.ext fun x=> LinearMap.congr_fun he x
  apply (EuclideanSpace.basisFun G.ColorIndex ℝ).toBasis.ext
  intro i
  have hi : ∀ (j : G.ColorIndex), ⟪O (rays j)-rays j,O (rays j)-rays j⟫_ℝ=0:= fun j=>
    (Finset.sum_eq_zero_iff_of_nonneg (fun s _=> show 0 ≤ inner ℝ (O (rays s)-rays s) _ from real_inner_self_nonneg)).mp h j (Finset.mem_univ j)
  exact sub_eq_zero.mp (inner_self_eq_zero.mp (hi i))

def Winner (b:Buffer F d)(t:ℝ)(O:Y): Prop := Feasible b t O ∧ ∀ p,Feasible b t p → nearest O ≤ nearest p

lemma rolling {b:Buffer F d}(H:Frigid b)(hd:4≤d)(hG:G.Simple) (s:ℝ):∃ O:Y, Winner b s O:=by
  obtain ⟨O,hO⟩:=H.feasible hd hG s
  obtain ⟨S,hS,hP⟩ := (ice_pool b s).exists_isMinOn ⟨steers O,hO⟩ near_cont.continuousOn
  exact ⟨S,hS,fun p hp=>hP (a:=p) hp⟩

/-- Limit of winning charges when the parameter retracts. -/
lemma winner_limit {b:Buffer F d}(u:ℕ→ℝ)(h:Tendsto u atTop (𝓝 0))(T:ℕ→Y)(he:∀ n,Winner b (u n) (T n))
    {P:Y}(ht:Tendsto T atTop (𝓝 P)):P=1:=by
  have hf:Feasible b 0 P:= (iceClosed b).mem_of_tendsto (h.prodMk_nhds ht) (Eventually.of_forall fun n=> (he n).1)
  obtain ⟨W,rfl⟩:=hf.folds
  let v:= steers W; let q:=steers W.symm
  have his : v*q=(1:Y):= ContinuousLinearMap.ext fun x=> W.apply_symm_apply x
  apply near_zero; apply le_antisymm _ (near_pos _)
  have hc:= near_cont.continuousAt.tendsto.comp ht
  have hq := ht.mul (tendsto_const_nhds (x:=q))
  rw [show steers W*q=1 from his] at hq
  have hx:= (near_cont.continuousAt (x:=(1:Y))).tendsto.comp hq
  rw [near_one] at hx
  exact le_of_tendsto_of_tendsto hc hx (Eventually.of_forall fun n=>
    (he n).2 (T n*q) ((he n).1.adjust hf his (W.symm.inner_map_map)))
end YM.RG11.Rigidity.Ice
