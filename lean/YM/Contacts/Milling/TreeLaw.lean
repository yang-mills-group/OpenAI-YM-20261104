import YM.Contacts.Milling.Film
import YM.Tree.Cut
/-! # Quotient homeomorphism for Ward tests of stationary expansion

One tree on whole period. Rotating coordinates need not preserve that tree.
Measure preservation proof uses the actual full product measure, not invariance
of individual near masks. Output applies at each fixed period before attempting
a flat comparison. -/
noncomputable section
namespace YM.Contacts.Milling
open Function Set Filter Metric Asymptotics MeasureTheory
open Finset Lattice RG Wilson Precision Exterior PertExtension.Series Pulse YM.Stationary Tree
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius ENNReal
variable {G:Gauge}{c f n: Side}
namespace Kale
variable {T:Ratio c f}(A:Forest T)
def dawn (U:Config G f): Forest.Slice A G:= fun i=> Lattice.gauge (A.foldAt U) U i.val
lemma dawn_d (U:Config G f): A.drape (dawn A U)= Lattice.gauge (A.foldAt U) U := by
  funext i; by_cases h:i∈A.trunks; · exact (A.on_tree _ ⟨i,h⟩).trans (A.compress U i h).symm
  exact A.off_tree (dawn A U) ⟨i,h⟩
lemma dawn_fold (U:Config G f)(k : Site f → G.El)(h:∀ i,k (T.embed i)=1): dawn A (gauge k U) = dawn A U:= by
  have he i : A.foldAt (gauge k U) i=A.foldAt U i * (k i)⁻¹:= by rw [Forest.foldAt,travel_gauge,A.hike_root,h]; simp; rfl
  funext i; rw [dawn,Lattice.gauge,he,he,dawn,Lattice.gauge,Lattice.gauge]; group
lemma dawn_swing (S:A.Slice G) : dawn A (A.drape S)=S := by
  have he : A.foldAt (A.drape S)=1:= by rw [A.names _ 1 (fun i h => A.on_tree S ⟨i,h⟩)]; funext i; unfold Forest.foldAt; rw [travel_identity,inv_one]; rfl
  funext i; rw [dawn,he,Lattice.gauge,A.off_tree]; simp
@[fun_prop] lemma dawn_cont: Continuous (dawn A (G:=G)):= continuous_pi fun i=> by unfold dawn Lattice.gauge; fun_prop
lemma dawn_preserved : MeasurePreserving (dawn A (G:=G)) (prior G f) (A.order G):= by
  have hm:= dawn_cont (G:=G) A|>.measurable; refine ⟨hm,?_⟩; ext s hs; let u:=s.indicator fun (i : A.Slice G)=>(1:ℝ)
  have h (x:Config G f): ((dawn A) ⁻¹' s).indicator (fun _=> (1:ℝ)) x = u (dawn A x):= by unfold u; simp [Set.indicator]
  have he : (prior G f).real (dawn A ⁻¹' s) = (A.order G).real s:= by
    rw [← MeasureTheory.setIntegral_one_eq_measureReal, ← MeasureTheory.setIntegral_one_eq_measureReal, ← integral_indicator hs, ← integral_indicator (hm hs)]; simp_rw [h]; apply Eq.trans (A.pack _ ?_ ?_); · simp_rw [dawn_swing]; rfl
    · simp_rw [← h]; exact Integrable.indicator (integrable_const _) (hm hs)
    intro k hk V; rw [dawn_fold A V k hk]
  rw [Measure.map_apply hm hs]; exact (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp he

-- One-step shipments
def released (T:Ratio c f)(R:Config G f→Config G f): Prop := ∀ (k:Site f→G.El), (∀ i,k (T.embed i)=1) → ∀ U,∃ z:Site f→G.El,(∀ i,z (T.embed i)=1) ∧ R (gauge k U)=gauge z (R U)
lemma exp_dawn (R:Config G f→ Config G f)(h:released T R)(U:Config G f): dawn A (R (A.drape (dawn A U)))=dawn A (R U) := by
   obtain ⟨z,hz,H⟩:= h (A.foldAt U) (A.fold_root U) U; rw [dawn_d,H,dawn_fold A _ _ hz]
def swing {L:Config G f ≃ₜ Config G f}(h:released T L)(ht:released T L.symm): A.Slice G ≃ₜ A.Slice G where
  toFun v:= dawn A (L (A.drape v))
  invFun v:=dawn A (L.symm (A.drape v))
  left_inv v:= by dsimp only; rw [exp_dawn A _ ht,L.symm_apply_apply, dawn_swing]
  right_inv v:= by dsimp only; rw [exp_dawn A _ h,L.apply_symm_apply,dawn_swing]
  continuous_toFun := by fun_prop
  continuous_invFun:=by fun_prop
lemma swing_preserve {L:Config G f≃ₜ Config G f}(h:released T L)(ht:released T L.symm)(hp:MeasurePreserving L (prior G f) (prior G f)): MeasurePreserving (swing A h ht) (A.order G) (A.order G):= by
  let S:=swing A h ht; have hm:= S.continuous.measurable; refine ⟨hm,?_⟩; change Measure.map S _ = _
  have he := dawn_preserved (G:=G) A; rw (occs:=.pos [1]) [← he.map_eq]; rw [Measure.map_map hm he.measurable,show S ∘ dawn A = dawn A ∘ L from funext fun U=>exp_dawn A _ h U, ← Measure.map_map he.measurable hp.measurable, hp.map_eq,he.map_eq]
lemma curtain_one : A.drape (1:A.Slice G)=1:= by funext i; by_cases h:i∈A.trunks; exact A.on_tree _ ⟨i,h⟩; exact (A.off_tree (1:A.Slice G) ⟨i,h⟩)
@[simp] lemma dawn_one: dawn A (1:Config G f)=1:= by rw [← curtain_one A,dawn_swing]
section symm
variable (g:Ratio c f) (n:Side)
def roam (k:Site n→G.El): (Config G n)≃ₜConfig G n where
  toFun := Lattice.gauge k
  invFun:= Lattice.gauge k⁻¹
  left_inv u:= by ext1 i; simp only [Lattice.gauge,Pi.inv_apply]; group
  right_inv u:= by ext1 i; simp only [Lattice.gauge,Pi.inv_apply]; group
  continuous_toFun := continuous_pi fun i => (continuous_const.mul (continuous_apply i)).mul continuous_const
  continuous_invFun := continuous_pi fun i => (continuous_const.mul (continuous_apply i)).mul continuous_const
def turn (G:Gauge)(s:Signed): Config G n≃ₜ Config G n where
  toFun:=pull s 0
  invFun:=pull s⁻¹ 0
  left_inv i:= by simp only [pull_pull,affine, Signed.act_zero,add_zero,mul_inv_cancel,inv_mul_cancel,pull_one]; funext; simp [Lattice.translate] -- translation zero
  right_inv i := by simp only [pull_pull,affine,Signed.act_zero, add_zero,mul_inv_cancel,inv_mul_cancel,pull_one]; funext; simp [Lattice.translate]
  continuous_toFun:= continuous_pull ..
  continuous_invFun:= continuous_pull ..
lemma roam_fed (k: Site f→G.El): released g (roam f k):= fun z h u=> by
  refine ⟨fun i=>k i*z i*(k i)⁻¹,fun i=>by simp [h i],?_⟩; funext i; change Lattice.gauge k (Lattice.gauge z u) _= Lattice.gauge _ (Lattice.gauge k u) _; simp only [Lattice.gauge]; group
lemma turn_fed (h:Odd g.count.val)(s:Signed): released g (turn f G s):=fun z hp u=> by
  rw [show (turn f G s) (gauge z u)=_ from Work.F05.pull_gauge_zero ..]; refine ⟨_,?_,rfl⟩; intro i; change z _ = 1; simp only [Lattice.affine,add_zero]; rw [← g.signed, hp]
end symm
end Kale
end YM.Contacts.Milling
