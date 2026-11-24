import YM.MS.Garment.Masks
import YangMills.WilsonProof.NativeSupport.YM.MS.City.Lines
import YM.MS.Wilson.ColorLinks
/-!
# Actual free Landau kernels for all p, lengths and dimensions

Normalize Γ_Ξ separately. `bare K` uses $√ε modes color; scales positive; no wave.
 Before master & matching. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Garment.Wick
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps
open Momentum Metric City Color
open scoped Topology ContDiff
variable {G:Gauge}{b c: Bool}{m n:ℕ}{A C:Type}[Fintype A][DecidableEq A] [Fintype C][DecidableEq C]
variable (G)
def A0 (s:ℝ): Rip G:= fun _=> Landau.choir (line (exp s)) id
def B0 (s:ℝ): Rip G:= fun _=> Landau.choir (laplace (Landau.low (exp s))) id
def L0' (s:ℝ): Rip G:= fun _=> Landau.choir (laplace (dotLow (exp s))) id
def D0 : Rip G:= fun n=> Landau.choir (laplace fun _:SectorP n=>1) id
def Q : Shade G:= fun _=> Landau.send id
lemma cue (s:ℝ)(m:ℕ): (Q G m).change (A0 G s m)= L0' G s m:= Eq.trans (land_charge (K:=line (exp s)) (A:=G.ColorIndex) id (fun x=>rfl)) (by unfold L0'; simp_rw [funext (fun a=>funext (fun e=> funext (identity (A:=Arts.L m) (exp s) a e)))])
-- Elementary currency
variable (s:ℝ)
lemma cl_a : closedF (A0 G s) false:= fun _=> City.closure id (by
   intro i j x h; rw [← brushed (exp s)] at h; exact L_cl (exp s) _ _ _ (right_ne_zero_of_mul h))
lemma cl_b : closedF (B0 G s) true:= fun _=> City.closure id (laplace_cl _)
lemma cl_c : closedF (L0' G s) true:= fun _=> City.closure id (laplace_cl _)
lemma reverse_a : reverseF (A0 G s):= fun m=> reverse_one id (fun i j p=>by rw [← brushed, ←brushed,L_rev]; ring) (fun _=>rfl)
lemma reverse_b : reverseF (B0 G s):= fun _=> reverse_one id (X_rev _) (fun _=>rfl)
lemma trigger (t:ℝ): speedR (B0 G) (L0' G t) t:= by
    intro m i j p; simp only [B0,L0',Landau.choir]; split
    · convert! (lap_der (exp t) _ _ p).scomp t (Real.hasDerivAt_exp t) using 1; rw [Complex.real_smul,lap1]; rfl
    exact hasDerivAt_const t _
lemma reverse_c : reverseF (L0' G s):= by
    intro m i j q; obtain h:= trigger G s m i j (-q); rw [show (fun i':ℝ=> B0 G i' _ _ _ (-q))=fun t=> cross (Landau.parity i) (Landau.parity j)*B0 G t m j i q from funext fun t=> reverse_b G t m i j q] at h; exact h.unique ((trigger G s m j i q).const_mul _)
lemma reverse_d : reverseF (D0 G):= by
    intro m; unfold D0; refine reverse_one id ?_ (fun _=>rfl); intro i j q; rw [← χ0  _ _ (-q),← χ0 _ _ q]; exact X_rev 0 i j q
lemma Aone (t:ℝ): amount 1 t=Complex.exp t:= by simp [amount]
lemma Atwo (t:ℝ): amount 2 t=Complex.exp t^2:= by rw [show (2:ℂ)=1+1 by ring, amount_add,Aone]; ring
lemma Aneg (t:ℝ)(a:ℂ): amount (-a) t=(amount a t)⁻¹:=(amount_inv _ _).symm
lemma Azero (t:ℝ): amount 0 t=1:= by simp [amount]
lemma lawQ : RawQ (Q G):= by
   intro m a b p t; simp only [Q,Landau.send,Landau.choir,id_eq]; by_cases he:a.2=b.2; swap; · simp only [if_neg he,mul_zero,zero_mul];
   simp_rw [if_pos he]; rcases a with ⟨⟨_|a,_|_⟩,x⟩ <;> rcases b with ⟨⟨_|b,_|_⟩,y⟩ <;> norm_num [wfield, dim,Landau.bare,Aneg, Atwo,Aone, k_scale] <;> rw [← Complex.ofReal_exp] <;> field_simp
lemma pA (t:ℝ): pulse 4 t (A0 G 0)= A0 G t:= by
   funext m i j p; simp only [pulse,A0,Landau.choir,exp_zero,id_eq]; split_ifs with he; · rcases i with ⟨⟨_|a,_|_⟩,i⟩ <;> rcases j with ⟨⟨_|u,_|_⟩,j⟩ <;> norm_num [line,coat,dim,wfield,Aone,Atwo, scaling] <;> ring -- assess
   exact mul_zero _
lemma pB (t:ℝ): pulse 3 t (B0 G 0)= B0 G t:= by
   funext m i j p; simp only [pulse,B0,Landau.choir,exp_zero,id_eq]; split_ifs with he; · rcases i with ⟨⟨_|a,_|_⟩,i⟩ <;> rcases j with ⟨⟨_|u,_|_⟩,j⟩ <;> norm_num [laplace,coat,Landau.low,dim,wfield,Azero]
   exact mul_zero _
end YM.MS.Garment.Wick
