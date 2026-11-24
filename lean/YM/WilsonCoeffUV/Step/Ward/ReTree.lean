import YM.WilsonCoeffUV.Step.Log
/-!
# Actual product-Haar re-tree

Even when testing a permutation changing trunks. On each orbit of the
root-pinned gauge subgroup there is exactly one drape. This is a finite
ordinary regulator statement, no assumption of gauge choice commuting with
those permutations. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Power
open MeasureTheory Wilson Lattice Laurent Exterior Bloch Matrix Precision RG Blue
open Next.Free FreeResolvent Tree Filter Metric Function Set
open scoped Topology ContDiff BigOperators
variable {c f n : Side}{G:Gauge}(S:StepData c f)

lemma together (t k : Site n→ G.El)(U : Config G n): gauge t (gauge k U)= gauge (t*k) U := by funext u; unfold Lattice.gauge; simp only [Pi.mul_apply]; group
lemma gauge_roll (s: Signed)(b : Site n)(k:Site n→G.El)(U: Config G n): pull s b (gauge k U)=gauge (k ∘ affine s b) (pull s b U) := by
  funext e; unfold pull; rw [Step.gauge_read]; simp only [Lattice.gauge,Step.vec_rotate, Step.vec_pos,Function.comp_apply,affine,Signed.act_add]; rw [add_right_comm]
lemma roll_back (s:Signed)(b : Site n)(U:Config G n) : pull s⁻¹ (-s⁻¹.act b) (pull s b U) = U := by
  rw [pull_pull,mul_inv_cancel, show affine s b (-s⁻¹.act b)=0 from ?a,pull_id]
  case a=> simp only [affine, Signed.act_neg]; simp
-- exact side lift
lemma switch_back (s:Signed)(b:Site c)(U:Config G f): pull s⁻¹ (S.ratio.embed (-s⁻¹.act b)) (pull s (S.ratio.embed b) U)=U := by
  have he : affine s b (-s⁻¹.act b)=0:= by simp [affine,Signed.act_neg]
  rw [pull_pull, S.port, he, mul_inv_cancel, show S.ratio.embed 0=0 from by simpa using S.ratio.embed_wrap 0, Lattice.pull_id]

variable (F:Forest S.ratio)

def collapse (U:Config G f) : F.Slice G := fun i=> gauge (F.foldAt U) U i
lemma tree_coll (U:Config G f): F.drape (collapse S F U) = gauge (F.foldAt U) U := by
  funext i; by_cases h:i∈F.trunks
  · exact (F.on_tree _ ⟨i,h⟩).trans (F.compress _ _ h).symm
  exact F.off_tree _ ⟨i,h⟩
lemma collapse_orbit (X:Config G f)(t:Site f→ G.El)(h: ∀ i,t (S.ratio.embed i)=1): collapse S F (gauge t X)=collapse S F X := by
  have hx : F.foldAt (gauge t X)*t= F.foldAt X := by
    funext i; simp only [Pi.mul_apply,Forest.foldAt,Lattice.travel_gauge, F.hike_root,h,inv_one,mul_one, _root_.mul_inv_rev, inv_mul_cancel_right]
  funext i; rw [collapse,collapse, together,hx]
lemma coll_once (u:F.Slice G): collapse S F (F.drape u)=u := by
  have h:F.foldAt (F.drape u)=F.foldAt 1:= F.names _ _ (fun i hi=>F.on_tree _ ⟨i,hi⟩)
  have he (w:Walk)(y : Site f): travel (1:Config G f) y w=1 := by induction w generalizing y with
                                                                       | nil=>rfl
                                                                       | cons i l H=> simp [travel,H,Step.read]
  funext i; rw [collapse,h]; unfold Lattice.gauge; simp_rw [Forest.foldAt,he]; rw [F.off_tree]; simp

lemma coll_cont : Continuous (collapse S F (G:=G)) := by unfold collapse Lattice.gauge; fun_prop

lemma coll_pres : MeasurePreserving (collapse S F (G:=G)) (prior G f) (F.order G) := by
  let h:=coll_cont (G:=G) S F
  refine ⟨h.measurable, Measure.ext fun x hx=>?_⟩
  rw [Measure.map_apply h.measurable hx]
  classical
  let C:=collapse S F (G:=G)
  let E:= x.indicator (fun _=> (1:ℝ))
  have he : (C ⁻¹' x).indicator (fun _=> (1:ℝ)) = E ∘ C := by ext i; by_cases h:C i∈x <;> simp [E,indicator,h]
  have hy : (∫ u,(C ⁻¹' x).indicator (fun _=> (1:ℝ)) u ∂ (prior G f))=(∫ u,E u∂(F.order G)) := by
    rw [F.pack]
    · simp_rw [he, Function.comp_apply]; congr 1; funext u; rw [show C _=u from coll_once S F u]
    · apply (integrable_const _).indicator (h.measurable hx)
    intro k hk U; rw [he]; change E _= E _; rw [show C _= _ from collapse_orbit S F U k hk]
  change (prior G f) _= _; apply (ENNReal.toReal_eq_toReal_iff' (by simp) (by simp)).mp
  exact ((integral_indicator_one (μ:=prior G f) (h.measurable hx)).symm.trans hy).trans (integral_indicator_one hx)

section
variable (s:Signed)(b:Site c)(z:Site f→G.El)

def process (X:Config G f) := gauge z (pull s (S.ratio.embed b) X)
def retract (u:F.Slice G) := collapse S F (process S s b z (F.drape u))
lemma process_roll (X: Config G f)(k:Site f→ G.El)(h:∀ i,k (S.ratio.embed i)=1):
    collapse S F (process S s b z (gauge k X)) = collapse S F (process S s b z X) := by
  let v := k ∘ affine s (S.ratio.embed b)
  have he i:v (S.ratio.embed i)=1:= by unfold v; rw [Function.comp_apply,S.port]; exact h _
  unfold process; rw [gauge_roll,together,← collapse_orbit S F (gauge z _) (z*v*z⁻¹) (fun i=> by simp [he i]), together]
  rw [inv_mul_cancel_right]
lemma process_one (X:Config G f): retract S F s b z (collapse S F X)=collapse S F (process S s b z X):= by rw [retract,tree_coll, process_roll S F s b z X _ (F.fold_root _)]
lemma retract_pres : MeasurePreserving (retract S F s b z) (F.order G) (F.order G) := by
  have hm : MeasurePreserving (process S s b z) (prior G f) (prior G f) := (prior_gauge z).comp (prior_pull _ _)
  have hf : Measurable (retract S F s b z) := (coll_cont S F).measurable.comp (hm.measurable.comp F.continuous_drape.measurable)
  refine ⟨hf,?_⟩; have hr := ((coll_pres S F).comp hm).map_eq
  rw [← (coll_pres S F).map_eq, Measure.map_map hf (coll_pres S F).measurable, (coll_pres S F).map_eq, show retract S F s b z ∘ collapse S F=collapse S F ∘ process S s b z from funext fun X=> process_one S F s b z X]
  exact hr
lemma retract_inj : Injective (retract S F s b z) := by
  let c':= -s⁻¹.act b
  let z':= z⁻¹ ∘ affine s⁻¹ (S.ratio.embed c')
  have h p : process S s⁻¹ c' z' (process S s b z p)=p:= by
    unfold process; rw [gauge_roll,switch_back]; unfold z'; funext; simp [Lattice.gauge]; group
  apply Function.LeftInverse.injective (g:=retract S F s⁻¹ c' z')
  intro i; change retract S F s⁻¹ c' z' (collapse S F _) = _; rw [process_one,h,coll_once]
end
lemma pull_first (s: Signed)(b : Site n): pull s b (1 : Config G n)=1 := by funext i; simp [pull,Step.read]
lemma force_const (s: Signed)(b : Site n)(k:Site n→G.El)(h:gauge k (pull s b (1:Config G n))=1) : ∀ i j,k i=k j := by
  rw [pull_first] at h
  have he (w:Walk)(i:Site n): travel (1:Config G n) i w=1:=by induction w generalizing i with
                                                                   | nil=> rfl
                                                                   | cons a l ih=>rw [travel,ih]; simp [Step.read]
  intro i j
  let w:=route (lift i) (lift j) 1
  have hj: stop i w=j:= by rw [← wrap_lift i,←wrap_stop_cover, route_end,wrap_lift]
  have H:=congr_arg (fun U=> travel U i w) h; simp_rw [travel_gauge,he,hj] at H; exact mul_inv_eq_one.mp (by simpa using H)
end YM.WilsonCoeffUV.Power
