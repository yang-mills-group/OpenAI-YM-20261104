import YM.Integration.QLocalRequestedSectorSale
import YM.RGLocalTaylor.Retain.Hero
import YM.RG12.Burst.Wardrobe

/-! Preselect the physical Gaussian cost of each finite signed source roster.
The purchased radius is common to all finite source truncations and fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalMarkedSourceCalendar
open Function Filter Finset Lattice Wilson RG Pressure Pressure.Tube Tree Precision Marker
open Push Push.SectorMeasure PhysicalNext PhysicalNext.Repeat Daisy Charity.RG12
open ConnectedActivityE6 ConnectedActivityE6.SliceRows Blaze Blaze.March Merge MergeProof RGLocalTaylor Retain Laminate
open PhysicalNext.JointLoad.Heir PhysicalNext.JointLoad.Heir.Suite PhysicalNext.JointLoad.Psalm
open scoped Classical BigOperators

def schedule (G : Gauge) : Decal G :=
  (garment10 G).paired ((Hero.decal G).paired (Gala.decal G))

variable {G : Gauge} {c f L : Side} {S : StepData c f} {P : Teller G} {T : Tube G S}
    {R : Rep G f} {W μ t C : ℝ} {Q : ConnectedActivityE6.Target G P} {O : Target.Order G W}
    {D : Stage} {Γ₀ : Target.Expense Q} {j : ℕ}

structure Shipping (Y : Cash W t μ L Q O C T R) : Prop where
  positive : 0<Mallow.station (betaF G t L)
  foam : Daisy.foam Q L
  cover : R.p.B≤2*radiusB t
  rim : 1≤Gala.mantle_rim G L t
  plain : Palette.shipPrice L Q t (j+1) (Mallow.station (betaF G t L))
  raised : Palette.shipPrice L Q t (j+1) (Gala.mantle_rim G L t*Mallow.station (betaF G t L))

theorem shipping (Y : Cash W t μ L Q O C T R) (stamp : Stamp T)
    (paid : (schedule G).rub P Q Γ₀ L W μ O D j t) : Shipping (j:=j) Y := by
  have attic : Attic Q Γ₀ L W μ O D j t := paid.1
  have pos : 0<Mallow.station (betaF G t L) := Real.rpow_pos_of_pos attic.2.1 _
  have top : 1≤Gala.mantle_rim G L t := paid.2.2.1.heft
  have ship : Palette.shipPrice L Q t (j+1) (Gala.mantle_rim G L t*Mallow.station (betaF G t L)) := paid.2.1
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,bikes,_,_,_⟩ := attic.2.2.2.2.2 c f S T stamp R C Y
  refine ⟨pos,attic.2.2.1,?_,top,?_,ship⟩
  · rw [Y.laws.intake.sizes,Y.laws.data.funds.length_eq]
    exact bikes.covers
  have site : 0≤Extra.Multi.siteFactor (radiusB t) := by unfold Extra.Multi.siteFactor; positivity
  exact (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left pos.le top) (Real.exp_pos _).le)
    (mul_nonneg (Nat.cast_nonneg _) site)).trans ship

theorem requested {V : Type} (J : FullQLocal.RenderedStep.Request V) (Q : ConnectedActivityE6.Target G P) :
    4≤(QLocalRequestedSectorSale.target J Q).relative := by
  change 4 ≤ max (J.outputSupport+5) (P.below.supportExponent+3)+2*min Q.ε (J.inputSupport/8)+Q.δ
  linarith [le_max_left (J.outputSupport+5) (P.below.supportExponent+3),J.output_support_pos,
    lt_min Q.usable (div_pos J.input_support_pos (by norm_num : (0:ℝ)<8)),Q.pos]

end YM.Integration.QLocalMarkedSourceCalendar
end
