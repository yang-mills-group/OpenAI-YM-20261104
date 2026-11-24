import YM.Integration.WilsonOlderFreshSoftSocketRose
import YM.Integration.WilsonOriginalPublicNodalStencils

/-! The undated finite stencil cost of the entire measured q roster, including the unit and every proper face. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketCensus
open Function Finset Lattice Laurent Wilson RG Precision Tree Exterior Bloch Matrix PowerSeries
open PhysicalNext.Repeat.Legato FreeResolvent WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Motion WilsonCoeffUV.Embroider WilsonCoeffUV.Soil Stationary WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank.Mosaic.Near
open OriginalMarkedSourceComet IndependentSourcePathFamily
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner

open WilsonThermometerDeclaredSeeds (Choice entry)
open WilsonReceivedCanonicalVerseBasis (dose)
open WilsonReceivedCanonicalVersePortfolio (Selection)
open WilsonOlderFreshSoftSocketMeasuredCash (ticket packet seats)
open WilsonOlderFreshSoftSocketInitial (charge)
open WilsonOlderFreshSoftSocketFaces (cash)
open WilsonThermometerPositionTunedSlope (Columns)
open WilsonOriginalPublicNodalCanonical (request)
open WilsonOlderFreshSoftRoseCourse (grade seat)
open Pert.Asymptotics
open private softened from YM.Integration.WilsonOriginalPublicNodalStencils
variable {G:Gauge}{I:Type}[Fintype I][LinearOrder I](R:Run G)(d:I→ℕ)
local notation "F" i:max => R.family.labels.level (d i)

def token (i:I)(b:(F i).Index):Choice R d i→ℂ
  | .inl _=>(Pi.single b 1:(F i).Coeff) 0
  | .inr s=>((F i).core (Pi.single b 1)) s.1*WilsonOriginalStarLaurentWallet.shape R (d i) s

def ceiling (i:I)(q:Choice R d i):ℝ:=∑b:(F i).Index,‖token R d i b q‖
def fee (S:Finset I):ℝ:=∑q:Selection R d S,∏i:S,ceiling R d i (q i)

omit [Fintype I] [LinearOrder I] in
theorem actual (b:Columns R d)(N per K:ℕ)(live:K≤N)(i:I)(q:Choice R d i):
    charge R d b N per K i q=token R d i (b i) q:=by
  cases q with
  | inl q =>
    change (F i).scaled (R.family.path.rep N per K).p.threshold (Pi.single (b i) 1) 0 *
      (regulatorRun R.family N per K:ℂ)^(-(0:ℤ))=_
    simp [token,Labels.Frame.scaled_apply,(F i).zero_degree]
  | inr s =>
    rw [WilsonOlderFreshSoftSocketInitial.charge,mul_comm]
    exact softened R d b (p:=per) live i s

omit [Fintype I] [LinearOrder I] in
theorem rank (S:Finset I)(q:(i:I)→Choice R d i):
    2*WilsonOlderFreshSoftSocketRestored.degree R d S q≤WilsonCoeffUV.Wheel.Mark.mass d S:=by
  rw [WilsonOlderFreshSoftSocketRestored.degree,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h:=WilsonThermometerInversionMaxwell.twice R d (entry R d i (q i))
  rw [WilsonThermometerDeclaredSeeds.site] at h
  exact h

theorem seven (S:Finset (Fin 3))(q:(i:S)→Choice R (grade ∘ seat S) i):
    WilsonOlderFreshSoftSocketRestored.degree R (grade ∘ seat S) univ q≤7:=by
  have bound:=rank R (grade ∘ seat S) univ q
  have parent:WilsonCoeffUV.Wheel.Mark.mass (grade ∘ seat S) (univ:Finset S)=
      WilsonCoeffUV.Wheel.Mark.mass grade S:=Finset.sum_coe_sort S grade
  have upper:WilsonCoeffUV.Wheel.Mark.mass grade S≤WilsonCoeffUV.Wheel.Mark.mass grade univ:=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _=>Nat.zero_le _
  have full:WilsonCoeffUV.Wheel.Mark.mass grade univ=14:=by decide
  omega

theorem original (N per K:ℕ)(live:K≤N)(narrow:regulatorRun R.family N per K≤1)
    (S:Finset I)(w:(i:I)→R.family.label (d i)):
    (∑q:Selection R d S,‖WilsonReceivedCanonicalVersePortfolio.weight R d N per K w S q‖)≤
      (∑b:Columns R (fun i:S=>d i),‖packet R d S w N per K b‖)*fee R d S:=by
  classical
  have gt:=ActualRunKernelPackets.regulator_pos R N per K live
  have term (q:Selection R d S):‖WilsonReceivedCanonicalVersePortfolio.weight R d N per K w S q‖≤
      ∑b:Columns R (fun i:S=>d i),‖packet R d S w N per K b‖*∏i:S,ceiling R d i (q i):=by
    apply le_trans (b:=‖ticket R d S w N per K q‖)
    · rw [WilsonOlderFreshSoftSocketTotal.priced,norm_mul,norm_inv,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos gt]
      exact le_mul_of_one_le_right (norm_nonneg _) ((one_le_inv₀ (pow_pos gt _)).2 (pow_le_one₀ gt.le narrow))
    rw [←WilsonOlderFreshSoftSocketMeasuredCash.original R d S w (per:=per) live q]
    apply (norm_sum_le ..).trans
    apply Finset.sum_le_sum
    intro b _
    rw [norm_mul]
    simp only [WilsonOlderFreshSoftSocketFaces.cash, norm_prod]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply prod_le_prod (fun _ _=>norm_nonneg _)
    intro i _
    rw [actual R d _ _ _ _ live i (q i)]
    exact single_le_sum (f:=fun j=>‖token R d i j (q i)‖) (fun _ _=>norm_nonneg _) (mem_univ _)
  calc _≤∑q:Selection R d S,∑b:Columns R (fun i:S=>d i),‖packet R d S w N per K b‖*
          ∏i:S,ceiling R d i (q i):=sum_le_sum fun q _=>term q
       _=_:=by rw [Finset.sum_comm,fee,Finset.sum_mul];exact sum_congr rfl fun b _=>(Finset.mul_sum ..).symm

end YM.Integration.WilsonOlderFreshSoftSocketCensus
end
