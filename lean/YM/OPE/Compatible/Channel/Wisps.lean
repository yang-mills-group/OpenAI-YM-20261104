import YM.OPE.Compatible.Channel.Slide
/-! Tort sym and uniqueness from evaluations. Tag offsets arbitrary on torus. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Set Lattice Laurent MeasureTheory RG Finset ContinuousMultilinearMap
open scoped Topology BigOperators Classical
variable {r n d m:ℕ}{T:Type*}[Fintype T] {u:ℝ}
namespace Script
open Page
abbrev deck (T:Type*) (n: Side) := (Site n × T) →ℝ
def render {n:Side}(x : Site n)(p : Page T r)(v: Fin r→deck T n):ℝ:= ∏ i,v i (x+wrap n (p i).1,(p i).2)
def scribe {n:Side}(x:Site n)(w : Script T r)(v:Fin r→ deck T n) := ∑' i,w i*render x i v
def value {n:Side}(x:Site n)(p:Script T r)(v:deck T n) := scribe x p fun _=>v
def library (n:Side)(p:Script T r)(v:Fin r→deck T n) := ∑ x:Site n,scribe x p v
def narrate (n:Side)(p:Script T r)(v:deck T n):= library n p fun _ => v
section
variable {N:Side}
def each_line (j:Site N)(p: Page T r) :Tensor.T (deck T N) ℝ r:= (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap fun i=> ContinuousLinearMap.proj (R:=ℝ) (j+wrap N (p i).1,(p i).2)
lemma rendered (j:Site N)(p:Page T r) (v:Fin r→deck T N): each_line j p v=render j p v:=rfl
lemma easily (j:Site N)(p:Page T r) : ‖each_line j p‖ ≤ 1:= by
    refine opNorm_le_bound zero_le_one fun x=> ?_
    rw [one_mul, rendered]; unfold render; rw [norm_prod]; exact prod_le_prod (fun _ _=> norm_nonneg _) (fun i _=> norm_le_pi_norm (x i) _)
def orchestra (p:Script T r)(j:Site N): Tensor.T (deck T N) ℝ r:= ∑' i,p i • each_line j i
lemma instruments (p:Script T r)(h:Summable p)(j:Site N)(v:Fin r→deck T N): HasSum (fun i=>p i*render j i v) (orchestra p j v):=by
    let H(i):Tensor.T (deck T N) ℝ r := p i • each_line j i
    have he:Summable H := h.norm.of_norm_bounded fun i=> by unfold H; rw [norm_smul]; exact mul_le_of_le_one_right (norm_nonneg _) (easily ..)
    exact (ContinuousMultilinearMap.apply ℝ _ ℝ v).hasSum he.hasSum
lemma silt_read {p:Script T r}(h:Summable p)(v:Fin r→deck T N): library N p v=library N (silt p) v:=by
    unfold library; unfold scribe; let d (i:Page T r):= ∑ x:Site N,render x i v
    have hx(i): d i = d (steady i):=by
        let q:= wrap N (-(primary i)); calc
           _ = ∑ x:Site N,render (x+q) i v:= (Equiv.sum_comp (Equiv.addRight q) _).symm
           _ = _:= sum_congr rfl fun j _=> by unfold render; exact prod_congr rfl fun k _=> by
                                                      simp only [steady, slide, Equiv.coe_fn_mk, _root_.map_add]; rw [add_assoc]
    have hz(s : Script T r)(hs:Summable s):library N s v= ∑' i,s i*d i:=by
       unfold library scribe; rw [← Summable.tsum_finsetSum]; exact tsum_congr fun i=> (mul_sum ..).symm
       exact fun i _=> (instruments s hs i v).summable
    change library N p _=library N _ _; have hs: Sack (figure 0) p (∑' i, ‖p i‖):= by unfold Sack figure poise; simp only [pow_zero,one_mul]; exact ⟨fun _=>norm_nonneg _,h.norm,le_rfl⟩
    have ht':= sootS (silt_cost hs)
    rw [hz p h,hz _ ht',show (fun i=> p i * d i)=(fun i=>p i*d (steady i)) from funext fun i=>by rw [← hx]]
    apply (Sack.cart_bill _ d ?_).symm
    simp_rw [← hx]; unfold d; simp_rw [mul_sum]; exact summable_sum fun j _=> (instruments p h j v).summable
omit [Fintype T] in
lemma rotateValue {p:Script T r}(a:Equiv.Perm (Fin r)) (j:Site N)(v:deck T N) : value j (swing a p) v=value j p v:=by
   unfold value scribe; let E:Page T r≃Page T r:=Equiv.arrowCongr a (Equiv.refl _); rw [← E.tsum_eq]
   refine tsum_congr fun i=>?_ ; unfold swing; change p (E.symm (E i))*_= _; rw [E.symm_apply_apply]; apply congr_arg (fun v:ℝ=>p i*v); unfold render; change (∏ x, v (j+wrap _ (i (a.symm x)).1, (i (a.symm x)).2))=_; exact Equiv.prod_comp a.symm (fun x=> v (j+wrap N (i x).1,(i x).2))
end
end Script
end YM.OPE.Flume
