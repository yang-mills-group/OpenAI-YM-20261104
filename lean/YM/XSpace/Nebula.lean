import YM.XSpace.Aura
import YM.XSpace.Fertile
/-!
# Clearance and shell overhead happen automatically in Point sensors
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Cirrus
open Filter Set Function Metric Lattice Expense Further.FreeCovariance.KP Stall Playpen
open Comets Probes Outline Asymptotics
open scoped Topology BigOperators Classical
variable {n:ℕ} (v: Sample n)
def focus : E4 := WithLp.toLp 2 v.center
def home := mark (unit v) (focus v)
def charts (j: Fin n) := v.layout j-home v
def near (j:Fin n):= Playpen.actual (unit v) (charts v j)
variable (z: Points n)
lemma sprawl : Stretched (Gate z) grab:= frontier.wider (liftG z)
lemma unit_pos : 0<unit v:= v.F.positive
lemma near_point (j:Fin n): dist (near v j) (familiar v j) ≤ 2*unit v:=by
  rw [dist_eq_norm]; change ‖unit v • rcast (v.layout j-home v)-(unit v • rcast (v.layout j)-focus v)‖ ≤ _; rw [Cross.rcast_sub,smul_sub,sub_sub_sub_cancel_left,norm_sub_rev]; exact current (unit v) v.F.positive (focus v)
lemma matched (j:Fin n) : Tendsto (fun i=> near i j) (Gate z) (𝓝 (z j)):=by
  have ht: Tendsto (fun i=> familiar i j) (Gate z) (𝓝 (z j)):= ((PiLp.proj (𝕜:=ℝ) 2 (fun _:Fin n=> E4) j).continuous.tendsto z).comp (senseG z); apply ht.congr_dist; exact squeeze_zero (fun i=>dist_nonneg) (fun i=> (dist_comm (familiar i j) (near i j)) ▸ near_point i j) (mul_zero (2:ℝ) ▸ (stepG z).const_mul 2)
lemma aims (h:z∈conf n): Poses (Gate z) unit (fun j i=> charts i j) z.ofLp Finset.univ:=⟨fun i _=> matched z i,(show Injective z.ofLp from h).injOn⟩
lemma foundation : ∀ᶠ i in Gate z,Tall (grab i).p (home i):=by
  filter_upwards [(sprawl z).horizon.eventually_ge_atTop (32:ℝ), welcomeG z] with i hi hw
  let p:=grab i; let n:= p.p.side; let t:=unit i; let r:=i.center 0; let a:= ((home i) 0:ℝ); have h:t>0:=i.F.positive
  have h1:p.size/8 ≤ r ∧ r ≤ p.size/4:= ⟨hw.1 0, hw.2 0⟩; have h2 : p.size=t*n.val :=rfl
  have hu : 32≤ (n.val:ℝ):= hi; have hh: -t ≤ t*a-r ∧ t*a-r ≤ t:= abs_le.mp (marked_bound h (focus i) 0)
  have hm : (n.val:ℝ)≤16*a∧16*a ≤ 5*n.val:=by
    rw [h2] at h1; constructor
    · apply le_of_mul_le_mul_left _ h; nlinarith [h1.1, hh.1,mul_nonneg (sub_nonneg.mpr hu) h.le]
    apply le_of_mul_le_mul_left _ h; nlinarith [h1.2,hh.2,mul_nonneg (sub_nonneg.mpr hu) h.le]
  unfold a at hm; exact seams _ _ (by exact_mod_cast hm.1) (by exact_mod_cast hm.2)
abbrev border (v:Sample n):ℕ:= Finset.univ.sup fun j=> Sail.reach (charts v j)
lemma bordered : ∃ C:ℝ,1≤C∧ ∀ᶠ i in Gate z, (border i:ℝ) ≤ C* (unit i)⁻¹:=by
  have he (j:Fin n):∀ᶠ i in Gate z, (Sail.reach (charts i j):ℝ) ≤ (1+‖z‖)*(unit i)⁻¹:=by
    filter_upwards [(matched z j).norm.eventually (ge_mem_nhds (show ‖z j‖<1+‖z‖ from lt_of_le_of_lt (PiLp.norm_apply_le ..) (by linarith)))] with i hi
    rw [← div_eq_mul_inv,le_div_iff₀ (unit_pos _)]; unfold near Playpen.actual at hi; rw [norm_smul,Real.norm_of_nonneg (unit_pos i).le] at hi; rw [mul_comm]; exact (mul_le_mul_of_nonneg_left (Sail.west _).1 (unit_pos _).le).trans hi
  refine ⟨1+‖z‖,le_add_of_nonneg_right (norm_nonneg _),?_⟩; filter_upwards [eventually_all.mpr he] with i hi
  classical
  cases n with
  | zero=> simp only [border]; have he: Finset.univ= (∅ : Finset (Fin 0)):=by simp
           rw [he, Finset.sup_empty, show (↑(⊥:ℕ):ℝ)=0 from Nat.cast_zero]; positivity [unit_pos i]
  | succ n=>
    obtain ⟨k,hk,H⟩:= Finset.exists_max_image Finset.univ (fun j=> Sail.reach (charts i j)) Finset.univ_nonempty; apply le_trans _ (hi k); exact_mod_cast (Finset.sup_le H)
lemma overhang : Overhead (Gate z) grab home Sample.layout:=by obtain ⟨C,hC,H⟩:= bordered z; refine ⟨C,1,hC,?_⟩; filter_upwards [H,foundation z] with i hi hv; refine ⟨hv,fun j=>?_⟩; push_cast; rw [zpow_neg, zpow_one]; apply le_trans _ hi; exact_mod_cast (Finset.le_sup (s:=Finset.univ) (f:=fun j=>Sail.reach (charts i j)) (Finset.mem_univ j))
end YM.XSpace.Cirrus
