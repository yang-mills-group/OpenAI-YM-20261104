import YM.Integration.WilsonIndependentMatchedOpeningComposite
import YM.Integration.WilsonIndependentRawRosterBudget
/-! The genuine aperture used in the inversion schedule for each visited field. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedOpeningExtent
open Function Filter Finset PowerSeries Lattice RG Wilson Tree Source Labels
open Laurent Bloch Metric FreeResolvent Work.F08 Precision Exterior Gauge XSpace XSpace.Rose PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Soil WilsonCoeffUV.Mer WilsonCoeffUV.Blue WilsonCoeffUV.Shard WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Embroider WilsonCoeffUV.Power WilsonCoeffUV.Bank
open WilsonCoeffUV.Wheel.Flooring PertExtension RegulatorIR RegulatorIR.Budget
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonIndependentMatchedFiledIncome (plate)
open WilsonIndependentMatchedSectionIncome (leaf)
open WilsonIndependentMatchedOrdinarySeat (here received)
open WilsonIndependentSpoutOrdinaryPlate (sample)
open scoped Classical BigOperators
open WilsonIndependentMatchedTopReceipt (realDose)
open WilsonIndependentMatchedOpeningColumn (column)
open WilsonIndependentMatchedOpeningRoster (seat)
open WilsonIndependentMatchedOpeningPayment (affiled)
open WilsonIndependentMatchedCoverProfile (word)
open WilsonIndependentMatchedOpeningFiled (terms planted)
open WilsonCoeffUV.StableStrip
open WilsonIndependentMatchedCensusReceipt (Filed)
open WilsonIndependentMatchedFittedSeat (receiving)
open WilsonIndependentMatchedOpeningPorts (Port submitted)
open WilsonIndependentMatchedOpeningColumn (column)
open WilsonIndependentMatchedOpeningRoster (field seat)
open WilsonIndependentMatchedOpeningPayment (affiled)
open RegulatorIR.Cluster
open WilsonIndependentMatchedOpeningCensus (entry pace Sites)
open WilsonIndependentRawRosterWord (degree)
open RegulatorIR RegulatorIR.Motion WilsonCoeffUV.Mer.Patrol
open WilsonIndependentMatchedOpeningComposite (branch points)
open WilsonIndependentRawRosterBudget (span)
theorem one {d D:ℕ}{G:Gauge}{F:Frame G d}{φ:Rarity D}{x y:ℝ}{o:CellR}
    (u:Port F φ x y o)(xx:0<x)(ρ:Room):
    dist ρ (slide 1 u.1.val)≤‖ρ‖ + (φ.radius+|y|+x)/x:=by
  have code:slide 1 u.1.val=actualW u.1.val:=by ext i; simp [slide,actualW]
  have keep:wheelC x y u.1.val φ.ψ o ≠0:=(visiting xx).1 u.1.property
  rw [code]
  apply (dist_le_norm_add_norm ρ (actualW u.1.val)).trans
  apply add_le_add le_rfl
  apply (le_div_iff₀ xx).2
  simpa [abs_of_pos xx,mul_comm] using hall_fit φ x y o u.1.val keep

theorem near {d D:ℕ}{G:Gauge}{F:Frame G d}{φ:Rarity D}{x y:ℝ}{o:CellR}
    (u:Port F φ x y o)(xx:0<x):
    dist ((y/x) • o.val) (slide 1 u.1.val)≤(φ.radius+x)/x:=by
  have code:slide 1 u.1.val=actualW u.1.val:=by ext i; simp [slide,actualW]
  have keep:wheelC x y u.1.val φ.ψ o ≠0:=(visiting xx).1 u.1.property
  obtain ⟨v,hv⟩:=featureV φ x y o u.1.val keep
  have atSupport:‖address x y o u.1.val v.val‖≤φ.radius:=by
    exact (dist_zero_right (address x y o u.1.val v.val)).symm ▸ φ.support hv
  have cell:‖v.val‖≤1:=(c_norm v).trans (by norm_num)
  have origin:x*(y/x)=y:=by field_simp
  rw [dist_comm,code,dist_eq_norm]
  apply (le_div_iff₀ xx).2
  calc
    ‖actualW u.1.val -(y/x) • o.val‖ * x = ‖x • (actualW u.1.val -(y/x) • o.val)‖:=by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos xx,mul_comm]
    _ = ‖address x y o u.1.val v.val - x • v.val‖:=by
      simp only [address,WilsonCoeffUV.Mer.position,smul_sub,smul_smul,origin,add_sub_cancel_right]
    _ ≤ _:= (norm_sub_le ..).trans (add_le_add atSupport (by rw [norm_smul,Real.norm_eq_abs,abs_of_pos xx];exact mul_le_of_le_one_right xx.le cell))

theorem gather {I:Type}(n:ℕ)(sel:Fin (n+1)→I)(ρ:Room)(o:I→ Cover):
    span ρ o (branch n sel)=∑i,dist ρ (slide 1 (o (sel i))):=by
  induction n with
  | zero=>simp [span,branch]
  | succ n ih=>rw [Fin.sum_univ_succ];exact congrArg (_ + ·) (ih (Fin.tail sel))

variable {G:Gauge}{H:Hol G}{n h D k u e:ℕ}{p:h<D}{native:Labels.Frame G h}
  {T:SectionData native}{v:Rails h k u e}{E A K U:Credit}
variable (R:PhysicalNext.Repeat.Legato.Run G)(d:Fin (n+1)→ℕ)(φ:Fin (n+1)→Rarity D)
    (y:ℝ)(o:Fin (n+1)→ CellR)(X:Fin (n+1)→ CutsP H T p v E A K U)

theorem original (z:(i:Fin (n+1))→Sites R d φ y o X i)(ρ:Room)(live:∀i,0<pace X i):
    span ρ (WilsonIndependentMatchedOpeningComposite.points R d φ y o X z) (branch n id) ≤
      ∑i,(‖ρ‖ + ((φ i).radius+|y|+pace X i)/(pace X i)):=by
  rw [gather]
  exact Finset.sum_le_sum fun i _=>one (z i) (live i) ρ
theorem located (z:(i:Fin (n+1))→Sites R d φ y o X i)(ρ:Room)(live:∀i,0<pace X i):
    span ρ (WilsonIndependentMatchedOpeningComposite.points R d φ y o X z) (branch n id) ≤
      ∑i,(dist ρ ((y/(pace X i)) • (o i).val) + ((φ i).radius+pace X i)/(pace X i)):=by
  rw [gather]
  apply Finset.sum_le_sum
  intro i hi
  exact (dist_triangle ρ _ (slide 1 (z i).1.val)).trans (add_le_add le_rfl (near (z i) (live i)))
end YM.Integration.WilsonIndependentMatchedOpeningExtent
