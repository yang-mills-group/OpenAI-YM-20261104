import YM.FormalBulk08.Lotus.Fans
import YM.CellFourier.Circulant
import Mathlib.Analysis.Normed.Group.Tannery

noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Lotus
open Lava Gorge Lattice Laurent Bloch Filter Set Function
open scoped BigOperators Classical ENNReal Topology
variable {I J : Type*} {η C : ℝ}

def lands (R : Row I J) (x : Biglot I) (y : Biglot J) := R x.2 y.2 (y.1-x.1)

def Wind (R : Biglot I→ Biglot J → ℝ) (T : (n : Side) → Tor n I → Tor n J →ℝ) := ∀ x y, Tendsto (fun n=> T n (drip n x) (drip n y)) atTop (𝓝 (R x y))
lemma landing_row (R : Row I J) (h : R.safe) : Wind (lands R) (R.acts) := by
   intro x y
   let f n (u : Cover) := if wrap n (y.1-x.1)=wrap n u then R x.2 y.2 u else 0
   have hh : (fun n=>R.acts n (drip n x) (drip n y))=(fun n=>∑' u,f n u) := by funext n; change (∑' u,if (wrap n y.1)= (wrap n x.1)+wrap n u then R x.2 y.2 u else 0)= _; unfold f; exact tsum_congr fun u=> by simp only [map_sub, sub_eq_iff_eq_add,add_comm]
   let g (u : Cover) := if y.1-x.1=u then R x.2 y.2 u else 0
   have hg : (∑' u,g u)=lands R x y := by simp [g,lands,eq_comm]
   have ha (u) : Tendsto (fun n=>f n u) atTop (𝓝 (g u)) := tendsto_const_nhds.congr' (by
      filter_upwards [effect (y.1-x.1),effect u] with n hn hi; unfold f g; split_ifs with e ht ht
      · rfl
      · exact False.elim (ht (congr_arg (wrap n) e))
      · exact False.elim (e (hn.symm.trans ((congr_arg Lattice.lift ht).trans hi)))
      rfl)
   change Tendsto (fun n=>R.acts n (drip n x) (drip n y)) _ _; rw [hh,←hg]; refine tendsto_tsum_of_dominated_convergence (h x.2 y.2) ha (.of_forall fun n u=>?_); unfold f; split_ifs <;> simp

def linkshine (η : ℝ) (x : Biglot I) (y : Biglot J) : ℝ≥0∞:= shine η (size (y.1-x.1))
def rinkshine (η : ℝ) (n : Side) (x : Tor n I) (y : Tor n J) : ℝ≥0∞:= shine η (skit n (y.1-x.1))
lemma strip_count (R : Row I J) (h : R.strip η C) (i:I) (j:J) :
      (∑' v, shine η (size v) * ‖R i j v‖ₑ)≤ ENNReal.ofReal C:= by
   have he:= h i j; unfold shine;simp_rw [← ofReal_norm,←ENNReal.ofReal_mul (Real.exp_pos _).le,←ENNReal.ofReal_tsum_of_nonneg he.1 he.2.1]; exact ENNReal.ofReal_le_ofReal he.2.2
lemma dust_cost (H : Type*) [Fintype H] (C : ℝ) : (∑' _ : H, ENNReal.ofReal C) = ENNReal.ofReal ((Fintype.card H)*C):= by rw [tsum_fintype]; simp [ENNReal.ofReal_mul (Nat.cast_nonneg _ : 0 ≤ (Fintype.card H:ℝ))]
lemma grad_line [Fintype I] [Fintype J] (R : Row I J) (h : R.strip η C) (hc : 0≤C) :
      Hill (linkshine η) (lands R) ((Fintype.card J)*C) ((Fintype.card I)*C) := by
   refine ⟨by positivity,by positivity,fun x=>?_,fun y=>?_⟩
   · rw [ENNReal.tsum_prod', ENNReal.tsum_comm,←dust_cost J C]; refine ENNReal.tsum_le_tsum fun a=> ?_
     let e:=Equiv.addRight (-x.1); change (∑' u : Cover,shine η (size (u-x.1))*‖R x.2 a (u-x.1)‖ₑ) ≤ _
     simp_rw [sub_eq_add_neg]; exact (Equiv.tsum_eq e (fun v=>shine η (size v)*‖R x.2 a v‖ₑ)).le.trans (strip_count R h x.2 a)
   rw [ENNReal.tsum_prod',ENNReal.tsum_comm,←dust_cost I C];refine ENNReal.tsum_le_tsum fun a=>?_; let e:= (Equiv.neg Cover).trans (Equiv.addLeft y.1);change (∑' u:Cover,shine η (size (y.1-u))*‖R a y.2 (y.1-u)‖ₑ)≤_
   simp_rw [sub_eq_add_neg]; exact (Equiv.tsum_eq e (fun v=>shine η (size v)* ‖R a y.2 v‖ₑ)).le.trans (strip_count R h a y.2)
end YM.FormalBulk08.Lotus
