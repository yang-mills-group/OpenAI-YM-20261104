import YM.FormalOPE.RG10.GaugeGear.Chime
/-!
 # Homogeneous prices exact at our saturated grades, decapitation of scalar columns
 before or after Episode. Effort proof uses no coincidence of fluctuation fields or zeroth-term physical
 axioms. This preserves ALL guards & Tier weight estimates. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.GaugeGear
open Function Route PowerSeries HStein Transit Finset
open scoped Topology BigOperators Classical
open MvPolynomial (homogeneousComponent homogeneousComponent_isHomogeneous)
variable {I:Type} (F:Tier)(w:I→ℝ) (hw:0≤w) (P: Packet I) (p: Channel I)
local notation "H" => MvPolynomial.homogeneousComponent
variable {r d i:ℕ} {j:Letters I}
local notation "l" => Primitives.GCC.LocalPolynomial.length
include hw
lemma weight_piece (P:Packet I)(i:ℕ) : F.valueOf w (H i P)=∑ j∈P.support.filter (fun m=> l m=i),F.face w j*‖MvPolynomial.coeff j P‖:= by
 -- unused j. needs hw included
 rw [F.capital _ hw,MvPolynomial.support_homogeneousComponent]; apply sum_congr ?_; · intro m hm; rw [MvPolynomial.coeff_homogeneousComponent, large,if_pos (mem_filter.mp hm).2]
 ext; simp_rw [←large] -- inspect
lemma all_slices (D:ℕ)(hp:P.totalDegree ≤ D) : (∑ y∈range (D+1), F.valueOf w (H y P))= F.valueOf w P := by
 rw [F.capital _ hw];
 simp_rw [weight_piece F w hw P _,sum_filter]; rw [sum_comm]; apply sum_congr rfl;intro j hj; have he : l j ≤ D:= le_trans (MvPolynomial.le_totalDegree hj) hp; simp [he]
lemma grains (hp:Guard p r d) : (∑ x∈items r d,F.valueOf w (cargo p x))= F.gain w p r:= by
 rw [items,sum_product, F.all_gain]; apply sum_congr rfl; intro i hi; have hh : i≤ r:=Nat.le_of_lt_succ (mem_range.mp hi); unfold cargo; simp only; have he := hp i hh; exact all_slices F w hw _ _ (he.trans (by omega))

omit hw
def decap (p: Channel I) := PowerSeries.mk (fun i=> PowerSeries.coeff i p - H 0 (coeff i p))
lemma degree_decap (hh: Guard p r d) : Guard (decap p) r d := by
 intro i hi; rw [decap, coeff_mk]; exact (MvPolynomial.totalDegree_sub _ _).trans (max_le (hh i hi) ((covered_h _ _).trans (hh i hi)))
lemma shelled (x:Grade): cargo (decap p) x= if 0<x.2 then cargo p x else 0 := by
 unfold cargo decap; rw [coeff_mk,map_sub,MvPolynomial.homogeneousComponent_of_mem ((MvPolynomial.mem_homogeneousSubmodule ..).mpr (homogeneousComponent_isHomogeneous ..))]; split_ifs with ha hb hb <;> first | omega | simp [ha] -- inspect ha orientation
include hw
lemma grains_non (hp:Guard p r d): (∑ x∈upstairs r d,F.valueOf w (cargo p x))= F.gain w (decap p) r := by
 rw [←grains F w hw _ (degree_decap p hp)]; unfold upstairs; rw [sum_filter]; apply sum_congr rfl; intro x _; rw [shelled]; split_ifs with h; · rfl
 rw [Tier.zero]
end YM.FormalOPE.RG10.GaugeGear
