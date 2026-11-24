import YM.RegulatorIR.Quadratic.Finish
import YM.RegulatorIR.Geometry.Pay

/-! Ellipt lower only on full periodic arrays (cover hypothesis incl. W1,
precisely calibrated to Wilson energy). Restrict not an input. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.StopB
open Function Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory MvPolynomial Cluster Diagram Quadratic Lattice Wilson Geometry Geometry.Field Chart Gauge RG Orb Laplace Tree Forest Step Matrix Prim Binding.Last GaussianScore Uniform
open scoped Topology ENNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius Matrix
variable {G:Gauge}{I J X:Type} {f:Side} {P l:ℝ}
section Able
variable {A:Deck P I X}{B:Deck P J I}
lemma row_times [Fintype X](N:Layer I I)(h : Billed N) (H:Sym A A N) (w:X→ℝ) x:
 (∑' y,N x y*bridge A w y)=bridge A (fmat A A N*ᵥ w) x:=by
 let f(y:I):=paint A A N x y*w (A.orbit y)
 have hf : Summable f:=by
    let M:= Finset.univ.sup fun u:X=> ‖w u‖ₑ
    apply quota_summable (w:=1) (fun _=>le_rfl); rw [quota_base];
    have ht := h.rows x; rw [quota_base] at ht
    apply ne_top_of_le_ne_top (ENNReal.mul_ne_top ht (show M≠⊤ from lt_top_iff_ne_top.mp (Finset.sup_lt_iff (by simp)|>.mpr (fun i _=>enorm_lt_top))))
    rw [← ENNReal.tsum_mul_right]; apply ENNReal.tsum_le_tsum;intro i; rw [show f i=_ from rfl]; unfold f;rw [enorm_mul, Layer.shade]; exact mul_le_mul_right (Finset.le_sup (f:=fun i:X=> ‖w i‖ₑ) (Finset.mem_univ _)) _
 have he y : N x y*bridge A w y=A.orient x*f y:=by unfold bridge f paint; calc
     _ = (A.orient x*A.orient x)*(N x y*(A.orient y*w (A.orbit y))):=by rw [A.sign_sq,one_mul]
     _ = _:=by ring
 rw [tsum_congr he,tsum_mul_left];unfold bridge;apply congr_arg; rw [← Stalk.collected_sum A.orbit hf, tsum_fintype];apply Finset.sum_congr rfl;intro p _; unfold Stalk.collect; simp_rw [f,show ∀ v:Stalk A.orbit p,A.orbit v.val=p from fun i=>i.property,tsum_mul_right, show (∑'v:Stalk A.orbit p, paint A A N x v.val) = _ from from_proj A A N H x p]; rfl
end Able

variable (N:Layer (Foot G) (Foot G))
def lifted (G:Gauge)(u: Edge (Site f)→ G.Color)(x:Foot G):= (u (around f x.1)) x.2 -- issue G shadow

def evenQ (u: Edge (Site f) →G.Color) : ℝ:= (∑ p:Edge (Site f), ∑ i:G.ColorIndex, u p i * ∑'k: Foot G,N ((Lattice.lift p.1,p.2),i) k * lifted G u k)/2
def Ellipt (e:ℝ)(f:Side): Prop:= ∀ u : Edge (Site f) → G.Color,e*((∑ i:Face (Per f), ‖Curl u i.1 i.2.val.1 i.2.val.2‖^2)/2) ≤ evenQ N u

variable (h : Even f.val)(he:l*f.val=P)
local notation "Q" => Carto G l P h he
local notation "K" => fmat Q Q N

lemma strengthened (u:Horizon G f)(HP:Sym Q Q N)(hs:Billed N): evenQ N (fire u)=2*beneath K u:=by
 let A:=Q;let T:=K;let z:=u; let y: Horizon G f:= (paper G f).symm (K *ᵥ paper G f u)
 have hg : lifted G (fire u)=bridge A (paper G f u):=by ext1 x; exact (firebrand h he u x.2 x.1).symm
 have hx (p:Edge (Site f))(i:G.ColorIndex) : (∑' k:Foot G,N ((Lattice.lift p.1,p.2),i) k*lifted G (fire u) k) = fire y p i:=by
    rw [hg,row_times N hs HP]; rw [show fmat A A N*ᵥ paper G f u= _ from (paper G f).apply_symm_apply _|>.symm]; let j:Edge Cover:=(Lattice.lift p.1,p.2)
    change bridge A (paper G f y) (j,i)= _; rw [firebrand,show around f j=p from (by simp [j,around])]
 have hp: paper G f y=T *ᵥ paper G f u := (paper G f).apply_symm_apply _
 unfold evenQ; simp_rw [hx]; rw [Quadratic.doubles h]
 · unfold beneath phase; change _= 2*(paper G f u ⬝ᵥ (T*ᵥ _) / 2); rw [← hp, dotProduct,Fintype.sum_prod_type]; simp_rw [fire_at]; ring_nf; rfl
 intro i; simp_rw [fire_swaps _ h,PiLp.neg_apply, neg_mul_neg]

lemma muscle {e:ℝ}(H:Ellipt N e f)(Hp:Sym Q Q N)(hs:Billed N) (x:Horizon G f): e*costO x ≤ beneath K x:=by
 specialize H (fire x);rw [strengthened N h he x Hp hs] at H
 have he : costO x= ((∑ i:Face (Per f), ‖Curl (fire x) i.1 i.2.val.1 i.2.val.2‖^2)/2)/2:=by unfold costO plume; rw [← Finset.sum_div]
 rw [he];linarith
end YM.RegulatorIR.StopB
