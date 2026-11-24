import YM.PhysMS.Frame.Measured
import YM.PhysMS.Frame.ShellIteration

/-! # Positions/Vev jets in the actual fields. Drop degeneracy under slot-equivalent
compositions on the filtration; used when transferring comparisons of measured and dynamically
adjusted slots, keeping scale and compact separated tests. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysMS.Frame
open Function Set Filter Table Spec Climb Spin Trace Trace.Pilot OPE
open scoped Topology ContDiff Classical BigOperators Matrix.Norms.Frobenius
variable {G : Gauge}{C : Family G}{f : Extraction.Order}{S : Table C.book}{n j : ℕ}
variable {X : Type*} {l:Filter X}
section jets
local instance(m:ℕ): ContinuousSMul ℝ (Points m):= IsBoundedSMul.continuousSMul
variable {X : Type*} {V : Fin n → Type*} [∀ i, AddCommGroup (V i)][∀ i, Module ℂ (V i)]
variable {K : Points n → MultilinearMap ℂ V ℂ}{x : Points n}
-- Don't apply at contact.
private def mv (j : ℕ) (x : Points n) (K : Points n → MultilinearMap ℂ V ℂ)
    (h:∀ v,ContDiffAt ℝ (j:WithTop ℕ∞) (fun x=> K x v) x) : MultilinearMap ℂ V (ContinuousMultilinearMap ℝ (fun _:Fin j=> Points n) ℂ) where
  toFun v := iteratedFDeriv ℝ j (fun x=> K x v) x
  map_update_add' v i p q:= by
    change iteratedFDeriv ℝ j _ x= _
    simp_rw [MultilinearMap.map_update_add]; apply iteratedFDeriv_add_apply (h _) (h _)
  map_update_smul' v i c p:= by simp_rw [MultilinearMap.map_update_smul]; exact iteratedFDeriv_const_smul_apply' (h _)

def positionsJet {L : Register G} (S T:Table L) (H:T.Smooth) (d:Caps n) (j:ℕ) (r:ℝ) (x:Points n):
       MultilinearMap ℂ (fun i=> S.Field (d i)) (ContinuousMultilinearMap ℝ (fun _:Fin j=>Points n) ℂ) :=
  if h : r • x ∈ conf n then mv j x (fun y=> S.classMoment T d (r • y))
    (fun v => (((S.class_smooth T H fun i=>⟨d i,v i⟩).contDiffAt
      ((conf_open n).mem_nhds h)).comp x (contDiffAt_id.const_smul r)).of_le (WithTop.coe_le_coe.mpr le_top))
  else 0

lemma positions_at {L : Register G}(S T:Table L)(H:T.Smooth)(d:Caps n) (j:ℕ) (r:ℝ) (x:Points n) (h:r • x∈conf n) (v) :
    positionsJet S T H d j r x v= iteratedFDeriv ℝ j (fun y=> S.classMoment T d (r • y) v) x := by rw [positionsJet,dif_pos h]; rfl
end jets

section finite
-- uniform finite combination lemma paying the coefficient costs too
variable {I : Type} [Fintype I] {V:I → Type} [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℂ (V i)][∀i,FiniteDimensional ℂ (V i)]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]

lemma combinations {E : Type*} [TopologicalSpace E] {S:Set E} (hs:IsCompact S)
    {ι : I → Type}[∀ i, Fintype (ι i)] (B : ∀ i,Module.Basis (ι i) ℂ (V i))
    {F : X → E → MultilinearMap ℂ V Y}{P:E → MultilinearMap ℂ V Y}
    (hc:∀ v,ContinuousOn (fun x=>P x v) S)
    (hb:∀ z: ∀ i,ι i,TendstoUniformlyOn (fun i x=> F i x (fun j=>B j (z j))) (fun x=> P x (fun j=>B j (z j))) l S)
    {v:X→∀ i,V i} {w} (hv: ∀ i,Tendsto (fun x=>v x i) l (𝓝 (w i))) :
      TendstoUniformlyOn (fun i x=> F i x (v i)) (fun x=> P x w) l S := by
   let J:= ∀ i,ι i; let u (i:J) (j:I):= B j (i j); let a (z : ∀ i,V i) (i:J):= ∏ j:I,(B j).repr (z j) (i j)
   have hA (i:J) : Tendsto (fun x=> a (v x) i) l (𝓝 (a w i)):=
      tendsto_finsetProd _ (fun j _=>(((B j).coord (i j)).continuous_of_finiteDimensional.tendsto _).comp (hv j))
   have hf (W:MultilinearMap ℂ V Y)(z): W z=∑ i:J, a z i • W (u i):=by
      conv_lhs=> rw [show z= fun j=> ∑ i, (B j).repr (z j) i • B j i from funext fun j=> ((B j).sum_repr _).symm]
      rw [MultilinearMap.map_sum]; exact Finset.sum_congr rfl fun i _=> W.map_smul_univ _ _
   rw [Metric.tendstoUniformlyOn_iff]; intro ε he
   let τ:=max 1 (Fintype.card J:ℝ); have ht : 0<τ:= lt_max_of_lt_left zero_lt_one
   let d:=ε/(4*τ); have hd:0<d:= by unfold d; positivity
   have hu (i:J):∀ᶠ k in l,∀ x∈S, ‖a (v k) i • F k x (u i)- a w i • P x (u i)‖ ≤ d+d :=by
       obtain ⟨A,hP⟩:= (hs.image_of_continuousOn ((hc (u i)).norm)).bddAbove; let t:=max A 1; let c:=‖a w i‖+1; have ht:0<t:=by unfold t; positivity
       have hz:0<c:=by unfold c; positivity
       filter_upwards [Metric.tendsto_nhds.mp (hA i) (d/t) (by positivity), Metric.tendstoUniformlyOn_iff.mp (hb i) (d/c) (by positivity), ((hA i).norm.eventually (ge_mem_nhds (lt_add_one _)))] with k hkd hh hk x hx
       have h₁:‖a (v k) i‖≤c:=hk; have h₂:‖a (v k) i-a w i‖ ≤ d/t:=(dist_eq_norm ..).symm.trans_le hkd.le
       let z:= F k x (u i); let b:=P x (u i); have h₃:‖z-b‖≤d/c:=((dist_eq_norm ..).symm.trans (dist_comm z b)).trans_le ((hh x hx).le); have h₄:‖b‖ ≤ t:=le_trans (show ‖b‖≤A from hP (mem_image_of_mem _ hx)) (le_max_left ..)
       calc ‖a (v k) i • z- a w i • b‖= ‖a (v k) i • (z-b)+(a (v k) i-a w i) • b‖:=by rw[smul_sub,sub_smul]; congr 1; abel
            _ ≤ _ :=(norm_add_le ..).trans (by rw [norm_smul,norm_smul]; exact add_le_add ((mul_le_mul h₁ h₃ (norm_nonneg _) hz.le).trans_eq (mul_div_cancel₀ _ hz.ne')) ((mul_le_mul h₂ h₄ (norm_nonneg _) (by positivity)).trans_eq (div_mul_cancel₀ _ ht.ne')))
   filter_upwards [eventually_all.mpr hu] with i hi x hx
   rw [dist_comm,dist_eq_norm]; rw [hf (P x), hf (F i x) (v i),←Finset.sum_sub_distrib]
   refine lt_of_le_of_lt ((norm_sum_le ..).trans (le_trans (b:=∑ _:J,(d+d)) (Finset.sum_le_sum fun j _=>hi j x hx) ?_)) (half_lt_self he)
   simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; refine (mul_le_mul_of_nonneg_right (le_max_right (1:ℝ) _) (by positivity : 0≤d+d)).trans_eq ?_
   change τ*(d+d)=ε / 2; unfold d; field_simp; ring
end finite

section apply
variable (F:Final C f S)
lemma measured_tensor {v:X→Viewers F} {r:X→ℝ}(hr:∀ᶠ i in l,0<r i) {P:X→tower S}
    (d:Caps n)(j:ℕ) {I:Fin n→Type}[∀ i,Fintype (I i)] (B:∀ i, Module.Basis (I i) ℂ ((Bel C.book).Field (d i)))
    {E:Set (Points n)}(he:IsCompact E)(h:E ⊆ conf n)
    (hp:∀ y:∀ i,I i, TendstoUniformlyOn (fun i=> iteratedFDeriv ℝ j (measured F (v i) (P i) (fun k=> B k (y k)) (r i)))
      (iteratedFDeriv ℝ j (WickGoal (fun k=> B k (y k)))) l E)
    {w:X→ MaxwellSlots C d}{u:MaxwellSlots C d} (hw : ∀ i,Tendsto (fun k=> w k i) l (𝓝 (u i))) :
    TendstoUniformlyOn (fun i=> iteratedFDeriv ℝ j (measured F (v i) (P i) (w i) (r i))) (iteratedFDeriv ℝ j (WickGoal u)) l E := by
  let Φ i x:= (positionsJet S (spectator F (v i)) (spectate F (v i)).smooth d j (r i) x).compLinearMap
        (fun k=> (P i (d k)).toLinearMap)
  let Q x:= positionsJet (Bel C.book) (Bel C.book) (Maxwell.table_smooth _) d j 1 x
  have h₁ (i:X)(hi:0<r i)(u)(x)(hx:x∈E): Φ i x u=iteratedFDeriv ℝ j (measured F (v i) (P i) u (r i)) x :=
       positions_at S _ _ d j (r i) x (Work.A05.smul_conf hi (h hx)) _
  have h₂ u x (hx:x∈E) : Q x u= iteratedFDeriv ℝ j (WickGoal u) x:= by
       unfold Q; rw [positions_at]; simp_rw[one_smul]; rfl; rw [one_smul]; exact h hx
  have hc(u): ContinuousOn (fun x=> Q x u) E := (show ContinuousOn _ E from (fun x hx=>
        ((WickGoal_tied (C:=C) u (h hx)).continuousAt_iteratedFDeriv (k:=j) (WithTop.coe_le_coe.mpr le_top)).continuousWithinAt)).congr (fun x hx=> h₂ u x hx)
  have hZ(y:∀ i,I i): TendstoUniformlyOn (fun i x=> Φ i x (fun k=> B k (y k))) (fun x=> Q x (fun k=> B k (y k))) l E:=by
     rw [Metric.tendstoUniformlyOn_iff]; intro ε he; filter_upwards [hr,Metric.tendstoUniformlyOn_iff.mp (hp y) ε he] with i hi hf x hx; rw [h₂ _ x hx,h₁ i hi _ x hx]; exact hf x hx
  rw [Metric.tendstoUniformlyOn_iff]; intro ε hε; filter_upwards [hr, Metric.tendstoUniformlyOn_iff.mp (combinations he B hc hZ hw) ε hε] with i hi hf x hx; specialize hf x hx; rwa [h₂ _ x hx,h₁ i hi _ x hx] at hf
end apply
end YM.PhysMS.Frame
