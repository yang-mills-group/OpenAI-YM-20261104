import YM.Pert.Kinetic.Combine
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Kinetic
open Function Filter Set Lattice Wilson Exterior RG Precision
open Work.F03
open scoped Topology BigOperators Classical ContDiff InnerProductSpace
variable {n : Side} {G : Gauge} {σ C Λ : ℝ} {p : Clip} {R : PathData G} (hR : R.Bounds p σ C Λ) (hn : 4≤n.val)

def windPrice (σ C Λ β : ℝ) := 2*(|β|/2 * (Fintype.card PlaqAxes:ℝ) * (2*rowCost σ C)+Λ/σ)
include hR hn
set_option maxRecDepth 3000
lemma rate_branch {c : Bool → G.Color} (hc : ∀ b, ‖c b‖=1) (β:ℝ) {i j : Axis} (hij : i ≠ j) (s : Signed)
    (v : Bool → Directions G n) (he : ∀ b,Bid.pulled (lift1 (v b)) s=lift1 (wave (c b) b i j)) :
    |(∑ b:Bool, ∑ x : Site n, costPath p R β (Bid.pulled (lift1 (v b)) s) x) - β/2 * (Fintype.card (Site n))*(4*Real.sin (Full.mesh n/2)^2)| ≤ Fintype.card (Site n)*(Full.mesh n)^3*windPrice σ C Λ β := by
    simp_rw [he]
    have H(b:Bool)(x:Site n):= cost_error hR β (wave_slow (hc b) b hn i j) x
    have e(x:Face (Per n))(b): ‖faceCurl x (lift1 (wave (c b) b i j))‖^2=‖faceCurl x (lift1 (wave (c true) b i j))‖^2 := by rw [curl_wave (c b) (hc b) b hn, curl_wave (c true) (hc true) b hn, norm_smul,norm_smul,hc,hc]
    have ht : β/2*Fintype.card (Site n) * (4*Real.sin (Full.mesh n /2)^2)= ∑ b : Bool,∑ x:Site n, β/2 * ∑ y:PlaqAxes, ‖faceCurl (x,y) (lift1 (wave (c b) b i j))‖^2 := by
      rw [mul_assoc (β/2),← all_energy (hc true) hn i j hij,Finset.sum_comm]
      simp_rw [Fintype.sum_prod_type,Finset.mul_sum,e]
    rw [ht,←Finset.sum_sub_distrib]; simp_rw [←Finset.sum_sub_distrib]
    let w := |β|/2 * (Fintype.card PlaqAxes:ℝ)*(2*rowCost σ C)+ Λ/σ
    calc _ ≤ ∑ b:Bool, ∑ x:Site n, (Full.mesh n)^3*w := (Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum fun b _=> (Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum fun x _=> H b x))
         _ = _ := by simp_rw [Fintype.sum_bool,Finset.sum_const, nsmul_eq_mul]; unfold windPrice w; rw [Finset.card_univ]; ring
lemma sum_rates {c:G.Color} (hc : ‖c‖=1) (β:ℝ) :
    |(∑ b:Bool, actualPath (p:=p) R β (rowWave (n:=n) c b)) - β/2 * (Fintype.card (Site n))*(4*Real.sin (Full.mesh n/2)^2)| ≤ Fintype.card (Site n)*(Full.mesh n)^3 * windPrice σ C Λ β := by
    let K := (β / 2) * ↑(Fintype.card (Site n)) * (4 * Real.sin (Full.mesh n / 2)^2)
    let P(s:Signed):= ∑ b:Bool, ∑ x:Site n, costPath p R β (Bid.pulled (lift1 (rowWave c b)) s) x
    let w := (Fintype.card (Site n) : ℝ) *(Full.mesh n)^3*windPrice σ C Λ β
    suffices he : ∀ s : Signed,|P s-K| ≤ w by
      unfold actualPath Patch.average; rw [←Finset.mul_sum, Finset.sum_comm]
      let q := (Fintype.card Signed:ℝ); have hq : 0<q:= by dsimp only [q]; exact_mod_cast Fintype.card_pos (α:=Signed)
      change |q⁻¹ * (∑ s:Signed,P s) - K| ≤ w
      rw [show q⁻¹*(∑ s:Signed,P s)-K=q⁻¹*(∑ s:Signed,(P s-K)) by simp [Finset.sum_sub_distrib,q] at *; field_simp,abs_mul,abs_of_pos (inv_pos.mpr hq)]
      refine (mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum fun s _=> he s)) (by positivity)).trans_eq ?_
      rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; change q⁻¹*(q*w)=w; field_simp
    intro s
    obtain ⟨a,h,h'⟩ := waves_turn c 0 1 s hn (by decide)
    exact rate_branch hR hn (i:=s.perm.symm 0) (j:=s.perm.symm 1) (c:=a) (fun b=> (h b).trans hc) β (s.perm.symm.injective.ne (show (0:Axis) ≠ 1 by decide)) s (rowWave c) (fun b=>(converts_dir s hn ..).symm.trans (congrArg _ (h' b)))
end YM.Pert.Kinetic
