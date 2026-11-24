import YM.Planned.PRIMARY_INTEGRAL_295.Stain
import YM.FormalBulk08.Kemp.Chart

/-! Radial extraction. Full continuum off-shell F.Frame grades;
uses **actual** link holonomy `H`. `carrier` is evaluated coefficientwise,
no gauge-variant radius of convergence asserted after summing paths.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Pose
open Filter Function Lattice Laurent Gauge Wilson Exterior Stationary
open Lava Lotus Mesa Gorge Shore City Kemp Rift
open Planned.PrimaryIntegral295 Place Carrier Film Labels Source Source.Drops Next.Foundations
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G : Gauge} {r u d j n:ℕ} {η A:ℝ} {I : Type*}

def monall {E:Type*} (b : E × Loc G 1) := (show TypeFace 1 from b.2.1)
def bearing {E:Type*} (b:E × Loc G 1):Axis:=axisEquiv.symm b.2.1

def curtain (v : edgeL G) (X : Snap G d) : ℝ:= Film.lane (Place.seat v.1) (bearing v) X v.2.2

def tier (v:chain (edgeL G) r) (X:Snap G d):= ∏ i, curtain (v i) X
lemma curtain_diff (v:edgeL G): ContDiffAt ℝ ω (curtain (d:=d) v) 0 := by unfold curtain; exact ((EuclideanSpace.proj (𝕜:=ℝ) v.2.2).contDiff).contDiffAt.comp (g:=_) _ (lane_smooth ..)
lemma rack_prod {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]{F:I→E→ℝ}{x:E}(S:Finset I)(h:∀ i∈S,ContDiffAt ℝ ω (F i) x): ContDiffAt ℝ ω (fun y=>∏ i∈S,F i y) x:= by
   induction S using Finset.induction with
   | empty=> simp only [Finset.prod_empty]; exact contDiffAt_const
   | @insert i S he ih=>simp_rw [Finset.prod_insert he]; exact (h i (Finset.mem_insert_self ..)).mul (ih fun j hj=>h j (Finset.mem_insert_of_mem hj))
lemma tier_diff (v:chain (edgeL G) r): ContDiffAt ℝ ω (tier (d:=d) v) 0:= by unfold tier; exact rack_prod _ (fun j _=> curtain_diff _)

abbrev Slate (G:Gauge)(d n : ℕ):= Tensor.T (Snap G d) ℝ n


-- Cost polynomial at fixed order from archive roads

def tileCons (v: chain (edgeL G) r) (d:ℕ) := ContinuousLinearMap.pi (fun i=> sampleIn (Place.seat (v i).1) (bearing (v i)) (G:=G) (d:=d))
def nacre (u: chain (hue G) r) (Z : Fin r→ EdgeRead G d):=∏ i, logo (Z i) (u i)
lemma nacre_diff (u:chain (hue G) r): ContDiffAt ℝ ω (nacre (d:=d) u) 0:= by
   unfold nacre; apply rack_prod; intro i _; exact (EuclideanSpace.proj (𝕜:=ℝ) (u i)).contDiff.contDiffAt.comp (f:=fun z:Fin r→EdgeRead G d=> logo (z i)) _ ((logo_smooth G d).comp (0:Fin r→EdgeRead G d) (f:=fun v => v i) (contDiffAt_apply ..))

lemma seat_ink (p: Loc G 1) (v:chain (edgeL G) r)(i):size (v i).1≤herb (fame _) (0,p) v:= by
   have he:=reached (fame _) (Fin.cons (0,p) v: chain (edgeL G) (r+1)) i.succ 0; simpa only [fame,capD,herb,Fin.cons_succ, Fin.cons_zero,sub_zero] using he
lemma sheet_cost (p : Loc G 1)(v:chain (edgeL G) r)(x:Snap G d): ‖tileCons v d x‖ ≤ (1+(herb (fame _) (0,p) v:ℝ))^d * ‖x‖:= by
   refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i=>?_
   let k:= bearing (v i); let r:=road (Place.seat (v i).1) k (G:=G) (d:=d)
   have h := r.le_opNorm x
   have he : liftCost d (v i).1≤ (1+(herb (fame _) (0,p) v:ℝ))^d:= by unfold liftCost; gcongr; apply seat_ink
   have hh := h.trans (mul_le_mul_of_nonneg_right ((road_cap (G:=G) (d:=d) _ _).trans he) (norm_nonneg _)); change ‖(((0:G.Color),((0:G.Color), (r x))): EdgeRead G d)‖ ≤ _; simpa using! hh
lemma tier_quote (p : Loc G 1)(r d n:ℕ)(hs:0<η):∃ C:ℝ,0≤C ∧ ∀ (x : Fin n→Snap G d) (v:chain (edgeL G) r),
     ‖Tensor.coeff (tier (d:=d) v) n 0 x‖ ≤ C * Real.exp (η*herb (fame _) (0,p) v) *∏ i,‖x i‖ := by
   let u t:= ‖iteratedFDeriv ℝ n (nacre (r:=r) (G:=G) (d:=d) t) 0‖
   let c:=∑ t,u t;have hc:0≤c:=by unfold c; exact Finset.sum_nonneg (fun i _=>norm_nonneg _)
   let b:= widthCost η (d*n); have hb:0≤b:=zero_le_one.trans (widthCost_ge hs _); let a:ℝ:=(n.factorial:ℝ)⁻¹
   refine ⟨a*c*b,mul_nonneg (mul_nonneg (by unfold a; positivity) hc) hb,fun Y v=>?_⟩
   let w:=fun i=>(v i).2.2; let L := tileCons v d
   have he : tier (d:=d) v=nacre w ∘ L:=rfl
   have hv : iteratedFDeriv ℝ n (tier (d:=d) v) 0=(iteratedFDeriv ℝ n (nacre (d:=d) w) 0).compContinuousLinearMap fun _=>L:= by rw [he]; exact jets_linear L ((nacre_diff w).of_le le_top)
   let x:ℝ:=herb (fame _) (0,p) v; have hx:0≤x:=Nat.cast_nonneg _
   rw [Tensor.coeff,hv, _root_.smul_apply,norm_smul, Real.norm_of_nonneg (by positivity)]
   have he' : ‖(iteratedFDeriv ℝ n (nacre (d:=d) w) 0) (L ∘ Y)‖≤c*(Real.exp (η*x) * b * ∏ i,‖Y i‖):= by
      apply ((iteratedFDeriv ℝ n (nacre w) 0).le_opNorm _).trans
      apply mul_le_mul (show u w ≤ _ from Finset.single_le_sum (f:=u) (fun i _=>norm_nonneg _) (Finset.mem_univ _)) _ (by positivity) hc
      apply (Finset.prod_le_prod (g:=fun i : Fin n=> (1+x)^d* ‖Y i‖) (fun _ _=>norm_nonneg _) (fun i _=>sheet_cost p v (Y i))).trans;rw [Finset.prod_mul_distrib,Finset.prod_const, Finset.card_univ,Fintype.card_fin, ←pow_mul]; exact mul_le_mul_of_nonneg_right ((widthBill η hs _ _ hx).trans_eq (mul_comm b _)) (by positivity)
   apply (mul_le_mul_of_nonneg_left he' (show 0≤a by unfold a; positivity)).trans_eq;unfold a x; ac_rfl

lemma slate_bill (a:Loc G 1)(r d n:ℕ)(hs:0<η):∃ C:ℝ,0≤C ∧ ∀ T:Tile (edgeL G) r,∀ A:ℝ, Knoxville (fame _) η (0,a) T A→∀ x:Fin n→Snap G d,
    let f v:= T v*(Tensor.coeff (tier (d:=d) v) n 0 x); Summable (fun v=> ‖f v‖) ∧ ‖∑' v,f v‖ ≤ C*A*∏ i,‖x i‖:= by
   obtain ⟨C,hC,H⟩:=tier_quote a r d n hs; refine ⟨C,hC,fun T A h x=>?_⟩; intro f; let z:= ∏ i,‖x i‖; have hz:0≤z:=by unfold z; positivity
   obtain ⟨hp,he⟩:=penn_amount h
   have ht v:‖f v‖≤C*z*(Real.exp (η*herb (fame _) (0,a) v)*‖T v‖):= by unfold f; rw [_root_.norm_mul];refine (mul_le_mul_of_nonneg_left (H x v) (norm_nonneg _)).trans_eq ?_; unfold z; ring
   have hh:=Summable.of_nonneg_of_le  (fun _=>norm_nonneg _) ht (hp.mul_left (C*z))
   refine ⟨hh,(norm_tsum_le_tsum_norm hh).trans ((hh.tsum_le_tsum ht (hp.mul_left _)).trans ?_)⟩
   rw [tsum_mul_left]; exact (mul_le_mul_of_nonneg_left he (mul_nonneg hC hz)).trans_eq (mul_right_comm ..)
lemma slate_wind (a: Loc G 1) (T:Tile (edgeL G) r) (x:Fin n → Snap G d) (hs:0<η)(ht: Knoxville (fame _) η (0,a) T A):
    Summable (fun v=> T v * Tensor.coeff (tier (d:=d) v) n 0 x):=((slate_bill a r d n hs).choose_spec.2 T A ht x).1.of_norm
lemma seal_sum {E X:Type*} [NormedAddCommGroup E][NormedSpace ℝ E](n:ℕ)(P:X→Tensor.T E ℝ n)(κ: X→ℝ)(C:ℝ)
    (h : ∀ x: Fin n→E,Summable fun v=> κ v*P v x)(he : ∀ x:Fin n→E, ‖∑' v,κ v*P v x‖ ≤ C*∏ i,‖x i‖) : ∃ Q:Tensor.T E ℝ n,∀ x,Q x=∑' v, κ v * P v x:= by
    let Q:MultilinearMap ℝ (fun _ : Fin n=>E) ℝ := {
      toFun := fun x=> ∑' v,κ v * P v x
      map_update_add' := fun x i u v=> by
          rw [← Summable.tsum_add (h (update x i u)) (h (update x i v))]; refine tsum_congr fun z=>?_ ;rw [(P z).map_update_add,mul_add]
      map_update_smul' := fun x i c v=>by
          rw [smul_eq_mul, ←tsum_mul_left]; refine tsum_congr fun z=>?_ ; rw [(P z).map_update_smul, smul_eq_mul,mul_left_comm]
    }
    exact ⟨Q.mkContinuous C he,fun _=>rfl⟩
lemma poem_found (a: Loc G 1) (T:Tile (edgeL G) r)(d n:ℕ)(hs:0<η)(ht:Knoxville (fame _) η (0,a) T A):
    ∃ P:Slate G d n,∀ x,P x=∑' v,T v*(Tensor.coeff (tier (d:=d) v) n 0 x):= by
   obtain ⟨C,hC,H⟩:= slate_bill a r d n hs; exact seal_sum n _ _ (C*A) (fun v=> (H T A ht v).1.of_norm) fun v=>(H T A ht v).2
-- Definition on marked grade; arbitrary for unreadable tensors not exported.
def slate (T:Tile (edgeL G) r)(d n:ℕ) : Slate G d n:= if h:∃ P :Slate G d n,∀ x,P x=∑' v,T v*(Tensor.coeff (tier (d:=d) v) n 0 x) then Classical.choose h else 0
lemma slate_read (p : Loc G 1) (T:Tile (edgeL G) r)(x: Fin n→Snap G d)(hs:0<η)(ht:Knoxville (fame _) η (0,p) T A): slate T d n x=∑' v,T v*(Tensor.coeff (tier (d:=d) v) n 0 x):= by rw [slate,dif_pos (poem_found p T d n hs ht)]; exact Classical.choose_spec (poem_found p T d n hs ht) x
lemma slate_symm (p:Loc G 1)(T:Tile (edgeL G) r)(d n:ℕ)(hs:0<η)(ht:Knoxville (fame _) η (0,p) T A):Tensor.Sym (slate T d n):= by intro x s; rw [slate_read p T _ hs ht,slate_read p T _ hs ht]; exact tsum_congr fun v=>congr_arg (T v*·) (Tensor.coeff_symm ((tier_diff v).of_le le_top) x s)
end YM.FormalBulk08.Pose
