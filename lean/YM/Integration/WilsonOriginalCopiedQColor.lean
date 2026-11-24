import YM.Integration.WilsonOriginalCopiedCurvatureStencil

/-! Every copied formal input from the true planted source is the independently declared
translated curvature packet, including its unmasked finite group functions at every coupling. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalCopiedQColor
open Finset Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn PhysicalNext PhysicalNext.Repeat Legato
open QuadraticLocal.Sunrise
open Comparison.Density.RenderM FVA1Physical.TwoReset Comparison.RG02
open LocalComparison ComparisonDensity.Address WilsonOriginalProjectedCurvatureCredits
open ActualOriginalQPackets ActualOriginalQReaders WilsonOriginalProjectedCurvatureRoster
open WilsonOriginalProjectedCurvatureSalary WilsonOriginalProjectedCurvatureBudget
open WilsonOriginalProjectedCurvaturePassport WilsonOriginalProjectedCurvatureLamps
open WilsonOriginalCopiedCurvatureStencil AllOrder.Floe
open private workAt from YM.Integration.WilsonOriginalCopiedCurvatureStencil
open scoped Classical BigOperators

variable {G : Gauge} {R : Run G} {B : MS.Local.Physical.Deck G}
  {p L n : ℕ} {hn : n ≤ L} {V : Type} [DecidableEq V] [Fintype V]
  (Q : MS.Land.Prescription B) (D : ActualRunQlocalNativeTuple.Datum R p L n hn V)
  (u : V → MS.Rake.Label B) (μ : ℝ) (orders : V → ℕ) (N : ℕ)
  (σ : ℝ) (extra : V → ℕ) {f : Side} (h : (R.family.side L p).val ∣ f.val)
  (x : tastes D) (layout : Layout G) (tape : Finset Age)
local notation "Rows" => ActualOriginalQPackets.Row (R:=R) u
local notation "test" => testInclusion (ActualRunQlocalNativeTuple.orbit D) x
local notation "T" s:max => ActualOriginalQPackets.token Q D u μ orders N s
local notation "Y" => cohort Q D u μ orders N σ extra
local notation "toll" => WilsonOriginalProjectedCurvatureLoan.toll (R:=R) u
local notation "grades" => (fun _ : V => toll)
local notation "C" => Stock.census V

omit [DecidableEq V] [Fintype V] in
private theorem missing {s : Rows} (unpaid : ¬0 < wallet Q D u μ orders N s σ)
    (b : Fin (Pages (R.family.side L p) f)) (U : Config G f) :
    (lift h b (T s)).read test U = 0 := by
  by_cases live : 0 < (placed u s).budget σ
  · rw [←workAt Q D u μ orders N σ h b x U s live]
    have off := norm_le_zero_iff.mp ((bound Q D u μ orders N s σ x).trans (not_lt.mp unpaid))
    simp only [off, mul_zero]
  · rw [WilsonOriginalCopiedCurvatureStencil.token]
    have hz := (not_lt.mp live).antisymm (amount _ _)
    have hm := (mul_eq_zero.mp hz).resolve_right (Real.exp_ne_zero _)
    have hc (j) : (placed u s).coeff j = 0 := by
      apply abs_eq_zero.mp
      apply le_antisymm _ (abs_nonneg _)
      rw [←hm]
      exact Finset.single_le_sum (fun k _ => abs_nonneg ((placed u s).coeff k)) (mem_univ j)
    simp [Atom.unmasked, Atom.poly, hc]

/-- The named input uses only the lifted published tokens and their own true powers. -/
def color : Bulk.Colors C G f where
  vac := QuadraticLocal.Fk.money layout tape
  power v := Launch.index C grades v.val + 1
  mark v g U := ∑ b : Fin (Pages (R.family.side L p) f), ∑ s : Rows,
    if (C).fire s.1.1 = v.val then ((g ^ (toll+1-ActualRunKernelPackets.fieldRank R (degree u) s):ℝ):ℂ) *
      (lift h b (T s)).read test U else 0

local notation "pageRows" b:max => (fun i : Funded Q D u μ orders N σ => FVA1Physical.TwoReset.copy h (Y i) b)
local notation "probe" => (fun i => (Y i).paint x)
local notation "copied" => FVA1Physical.TwoReset.copyColor h Y grades probe layout tape
local notation "named" => color Q D u μ orders N h x layout tape

private theorem page_mark (b : Fin (Pages (R.family.side L p) f)) (v : Multi.Hot C) (g : ℝ)
    (U : Config G f) :
    (Air.craft (pageRows b) probe grades layout tape).mark v g U =
      ∑ s : Rows, if (C).fire s.1.1 = v.val then
        ((g ^ (toll+1-ActualRunKernelPackets.fieldRank R (degree u) s):ℝ):ℂ) *
          (lift h b (T s)).read test U else 0 := by
  let value (s:Rows) := ((g ^ (toll+1-ActualRunKernelPackets.fieldRank R (degree u) s):ℝ):ℂ) *
    (lift h b (T s)).read test U
  let fee (s:Rows) := if (C).fire s.1.1 = v.val then value s else 0
  simp only [Air.craft, QuadraticLocal.Fk.grant, Air.sums, tsum_fintype]
  have bought (i : Funded Q D u μ orders N σ) :
      ScatterR.familyAt (pageRows b) probe i g U = value i.val := by
    let s := i.val
    have rank := ActualRunKernelPackets.term_grade R (degree u) s
    have bound := WilsonOriginalProjectedCurvatureBudget.limit (R:=R) u s
    have stamp : (WilsonOriginalProjectedCurvatureLoan.filed u s).stamp =
        toll+1-ActualRunKernelPackets.fieldRank R (degree u) s := by
      simp only [QuadraticLocal.Sunrise.Loan.stamp, WilsonOriginalProjectedCurvatureLoan.filed,
        WilsonOriginalProjectedCurvatureBudget.grade, WilsonOriginalProjectedCurvatureLoan.toll]
      omega
    change paint Q D u μ orders N s σ x * (↑(g ^ (WilsonOriginalProjectedCurvatureLoan.filed u s).stamp *
      (divided (placed u s) σ).unmasked U (page h (ActualRunQlocalNativeTuple.root D s.1.1) b).val) : ℂ)
        = value s
    unfold value
    rw [stamp, Complex.ofReal_mul, ←workAt Q D u μ orders N σ h b x U s
      (substantial Q D u μ orders N s σ i.property)]
    ring
  calc
    _ = ∑ i : Funded Q D u μ orders N σ, fee i.val := by
      apply Finset.sum_congr rfl
      intro j _
      have mode : (ScatterR.actor (pageRows b) j).val = (C).fire j.val.1.1 :=
        (WilsonOriginalProjectedCurvatureRender.geometry Q D u μ orders N j.val σ (extra j.val.1.1) j.property).1
      by_cases hit : (C).fire j.val.1.1 = v.val
      · simp only [if_pos (mode.trans hit), fee, if_pos hit, bought]
      · simp only [if_neg (fun h => hit (mode.symm.trans h)), fee, if_neg hit]
    _ = ∑ j : Rows, fee j := by
      rw [← Finset.sum_subtype (p:=fun s : Rows => 0 < wallet Q D u μ orders N s σ)
        (univ.filter (fun i : Rows => 0 < wallet Q D u μ orders N i σ)) (fun i=> by simp) fee]
      apply Finset.sum_subset (Finset.filter_subset ..)
      intro s _ hz
      have h0 : ¬ 0 < wallet Q D u μ orders N s σ := by simpa using hz
      simp only [fee, value, missing Q D u μ orders N σ h x h0 b U, mul_zero, ite_self]

theorem original : copied = named := by
  have marks : (copied).mark=(named).mark := by
    funext v g U
    change (∑ b : Fin (Pages (R.family.side L p) f), _ : ℝ → Config G f → ℂ) g U = _
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl (fun b _ => page_mark Q D u μ orders N σ extra h x layout tape b v g U)
  have eq_of {A B : Bulk.Colors C G f} (vac : A.vac=B.vac) (mark : A.mark=B.mark)
      (power : A.power=B.power) : A=B := by
    cases A
    cases B
    cases vac
    cases mark
    cases power
    rfl
  exact eq_of rfl marks rfl

end YM.Integration.WilsonOriginalCopiedQColor
