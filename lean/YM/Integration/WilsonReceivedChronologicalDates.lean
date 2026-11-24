import YM.Integration.WilsonOriginalPhysicalCorridorLength
import YM.Integration.WilsonOriginalOccupiedDateShare

/-! Finite-date counting and allocation on the measured physical aperture. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalDates
open Finset Filter Lattice Wilson RG Multi Tree Marker Org AllOrder AllOrder.Transit
open PhysicalNext.Repeat.Legato Pert.Asymptotics
open scoped Classical BigOperators
open WilsonOriginalOccupiedDateShare (total)
local notation "wgt" => WilsonOriginalOccupiedDateShare.weight

theorem distribution (b L:ℕ)(days:Finset ℕ)(earlier:∀ i ∈ days, b ≤ i + 1)
    (before:∀ i ∈ days, i + 1 < b + L)(fare:days→ℝ)(K:ℝ)(kp:0≤K)(paid:∀i,fare i≤K):
    days.card≤L ∧ (∑i:days,fare i/wgt (i.val+1-b))≤K:=by
  let slot:days→ℕ:=fun i=>i.val+1-b
  have owned (i:days):slot i < L:=by have hb:=earlier i i.property;have ht:=before i i.property;dsimp [slot];omega
  have unique:Function.Injective slot:=by
    rintro ⟨i,hi⟩ ⟨j,hj⟩ h
    have h₁:=earlier i hi;have h₂:=earlier j hj
    apply Subtype.ext
    dsimp [slot] at h ⊢
    omega
  have cost (r:ℕ):0<wgt r:=by unfold WilsonOriginalOccupiedDateShare.weight;positivity
  have lodged:univ.image slot⊆range L:=by
    intro r hr
    obtain ⟨i,_,rfl⟩:=mem_image.mp hr
    exact mem_range.mpr (owned i)
  have size:=Finset.card_le_card lodged
  rw [Finset.card_image_of_injective _ unique,card_univ,Fintype.card_coe,card_range] at size
  refine ⟨size,?_⟩
  have wages:(∑i:days,1/wgt (slot i))≤1:=by
    calc
      _ = ∑r∈univ.image slot,1/wgt r:=(sum_image (fun _ _ _ _ hij=>unique hij)).symm
      _ ≤ ∑r∈range L,1/wgt r:=sum_le_sum_of_subset_of_nonneg lodged fun r _ _=>by positivity [cost r]
      _ ≤ 1:=by rw [total];exact sub_le_self _ (by positivity)
  calc
    _ ≤ ∑i:days,K*(1/wgt (slot i)):=sum_le_sum fun i _=>by
      rw [mul_one_div];exact div_le_div_of_nonneg_right (paid i) (cost _).le
    _ = K*∑i:days,1/wgt (slot i):=(Finset.mul_sum ..).symm
    _ ≤ K:=by simpa using mul_le_mul_of_nonneg_left wages kp

variable {G:Gauge}(R:Run G)(simple:G.Simple)
local notation "H" i:max => R.family.path.levels.clock.hatBeta i
include simple in
theorem stages (d:ℕ):∃start:ℕ,∀{b L N per:ℕ},start≤b → b+L≤N →
    R.family.S.a b/R.family.S.a (b+L)≤(H b)^d → ∀(days:Finset ℕ)
      (_earlier:∀ i ∈ days, b ≤ i + 1)(_before:∀ i ∈ days, i + 1 < b + L),
      let g:=regulatorRun R.family N per b
      (0<g ∧ 3*g≤1 ∧ (days.card:ℝ)*g≤4*(d:ℝ)/Real.log 3) ∧
        ∀ i ∈ days, ((i+1-b:ℕ):ℝ)≤((d:ℝ)/Real.log 3)*(1+Real.log (H (i+1)))^1:=by
  obtain ⟨start,clock⟩:=eventually_atTop.mp (WilsonOriginalPhysicalCorridorLength.original R simple d)
  refine ⟨start,?_⟩
  intro b L N per bb active re days earlier before g
  obtain ⟨gp,small,bound⟩:=clock b bb (per:=per) active re
  have size:days.card≤L:=(distribution b L days earlier before (fun _=>0) 0 (by norm_num) (fun _=>le_rfl)).1
  refine ⟨⟨gp,small,(mul_le_mul_of_nonneg_right (Nat.cast_le.mpr size) gp.le).trans bound⟩,?_⟩
  intro i hi
  have hb:=earlier i hi
  let off:Fin L:=⟨i+1-b,by have h:=before i hi;omega⟩
  have span:=WilsonOriginalPhysicalCorridorLength.span R simple d b L off re
  have eq:b+off.val=i+1:=by dsimp [off];omega
  rw [eq] at span
  exact span
end YM.Integration.WilsonReceivedChronologicalDates
end
