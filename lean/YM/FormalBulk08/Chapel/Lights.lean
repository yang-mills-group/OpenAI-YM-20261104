import YM.FormalBulk08.Chapel.Arch
import YM.Pert.Bulk.Crossing

/-! Rows on installed resolution in absolute positions & displacements. Foot algebra from baseline. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Chapel
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 PowerSeries Next.Free RG Precision
open Lotus Shore Mesa Gorge City Cork Rift Lava
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G : Gauge}{σ η C : ℝ}{m r:ℕ}{L : Side}{I J : Type}

def merit (S : Cross L I J)(u:Biglot I):= lands S (Bank.scroll L I u)
lemma merit_eq (S: Cross L I J) : merit S= Pert.Bulk.install S:= rfl

def piz (L: Side)(x: Biglot I)(b : J) : Biglot J:= (Stationary.rent L x.1,b)
lemma parent_less (x y : Biglot I): capD (Stationary.rent L x.1) (Stationary.rent L y.1) * (L.val:ℝ) ≤ (capD x.1 y.1: ℝ) + (8:ℝ)* L.val:= by
    have ht := Bank.extent_ray (Bank.scroll L I x) (Bank.scroll L I y); rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply] at ht; rw [mul_comm]; exact_mod_cast ht
lemma cloak (S: Cross L I J) (h : Odd L.val) (x: Biglot I)(a:Axis) : merit S (x.1+step a,x.2)-merit S x=merit (forwardC L S a) x:= by
    exact congr_fun (Pert.Bulk.install_step h a S) x

variable [Fintype I] [Fintype J]
lemma rayon (x:Biglot I)(U : Cross L I J)(h:U.strip η C)(hc:0≤C)(a:J):
    (∑' v,Gorge.shine η ((fame J).d (piz L x a) v) * ‖merit U x v‖ₑ) ≤ ENNReal.ofReal ((Fintype.card J:ℝ)*C) := by
    let w:=piz L x a
    simp_rw [show ∀ v:Biglot J, (fame J).d (piz L x a) v = size (v.1-w.1) from fun v=>cap_turn ..]
    exact (grad_line U h hc).rows (Bank.scroll L I x) -- implicit
lemma radix (U : Cross L I J)(h:U.strip η C)(hc:0≤C)(u:Biglot J):
    (∑' v,Gorge.shine η ((fame J).d u (piz L v u.2))* ‖merit U v u‖ₑ)≤ ENNReal.ofReal ((L.val:ℝ)^4*((Fintype.card I)*C)) := by
    let q:= grad_line U h hc; rw [←Equiv.tsum_eq (Bank.scroll L I).symm];
    rw [show (L.val:ℝ)^4*(Fintype.card I*C)=(Fintype.card (Site L × I):ℝ)*C by simp [mul_assoc]]
    have H(w:Biglot (Co L I)) : piz L ((Bank.scroll L I).symm w) u.2=(w.1,u.2):= Prod.ext (show (Bank.scroll L I ((Bank.scroll L I).symm w)).1=w.1 by rw [Equiv.apply_symm_apply]) rfl
    simp_rw [H,merit,Equiv.apply_symm_apply]; exact q.columns u
lemma tilt_path (x:Biglot I)(r: Biglot I)(u:Biglot J) (k : ℕ)(he: capD r.1 x.1≤ k)(S: Cross L I J)(h: S.strip η C)(hc:0≤C)(hs:0≤η):
   (∑' v,Gorge.shine η ((fame J).d v (piz L r u.2))* ‖merit S x v‖ₑ)≤ ENNReal.ofReal (Real.exp (η*(k/(L.val:ℝ)+8))* (Fintype.card J*C)):= by
   rw [ENNReal.ofReal_mul (Real.exp_pos _).le]; apply le_trans (b:=ENNReal.ofReal (Real.exp (η*(k/(L.val:ℝ)+8)))*(∑' v,Gorge.shine η ((fame J).d (piz L x u.2) v)*‖merit S x v‖ₑ)) _ (mul_le_mul_right (rayon x S h hc u.2) _)
   rw [← ENNReal.tsum_mul_left]; apply ENNReal.tsum_le_tsum;intro v; rw [←mul_assoc];apply mul_le_mul_left; rw [Gorge.shine,Gorge.shine,←ENNReal.ofReal_mul (Real.exp_pos _).le,←Real.exp_add]; apply ENNReal.ofReal_le_ofReal;apply Real.exp_monotone
   rw [(fame J).turn v,←mul_add]; apply mul_le_mul_of_nonneg_left _ hs
   let d:ℕ := (fame J).d (piz L r u.2) (piz L x u.2); refine le_trans (b:= (d:ℝ) +(fame J).d (piz L x u.2) v) (by exact_mod_cast (fame J).tri (piz L r u.2) (piz L x u.2) v) (add_le_add_left ?_ _); let l:ℝ:=L.val; have hl:0<l:= by unfold l; positivity
   have hx : d*l ≤ (k:ℝ)+8*l:= (parent_less r x).trans (add_le_add_left (by exact_mod_cast he) _); change (d:ℝ)≤ k/l+8; exact ((le_div_iff₀ hl).mpr hx).trans_eq (by rw [add_div,mul_div_cancel_right₀ _ hl.ne'])

abbrev cloud (r:ℕ) := Wand (Fin r× Axis)
def rack (w:cloud m)(i:Fin m):Cover:=fun k=>w (i,k)
lemma real_size (w:cloud m): size w= ∑ i:Fin m,size (rack w i):=Fintype.sum_prod_type ..
lemma atom_size (w:cloud m)(i:Fin m): size (rack w i) ≤ size w:= by rw [real_size];exact Finset.single_le_sum (f:= fun j=>size (rack w j)) (fun i _=> Nat.zero_le _) (Finset.mem_univ i)

omit [Fintype I][Fintype J] in
lemma rack_plus (w:cloud m)(i:Fin m)(u:Axis)(j: Fin m): rack (w+buzz (i,u)) j=if i=j then rack w j+step u else rack w j:= by ext k;by_cases h:i=j <;> simp [Ne.symm,h,rack,buzz]
end YM.FormalBulk08.Chapel
