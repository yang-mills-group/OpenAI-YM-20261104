import YM.Integration.WilsonMatrixTicketLanesReportedCoupon
import YM.Integration.ActualOriginalCalibratedColumns

/-! Finite source coordinates of the original full Q input on the bare terminal block. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesTerminalQWords
open FVA2 OPE RG12 RG17 Extraction Spec Wilson Table RG Lattice MeasureTheory Pert.Asymptotics
open Function Filter Finset Precision Lattice RG Wilson Source Labels Tree
open MS MS.Land MS.Menus MS.Rake MS.Local.Physical MS.Native.Wilsonian
open PhysicalNext.Repeat.Legato RGComparison.Core16 RGComparison.Core16.Spool
open WilsonMatrixTicketLanesReportedOneBlock
open private linear from YM.Integration.WilsonMatrixTicketLanesReportedOneBlock
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){B:Deck G}(Q:Land.Prescription B)

abbrev Piece (l:Label B):Type:=Sigma fun a:Glyph B l.h=>(R.family.labels.level a.size).Index

def weight (l:Label B)(μ:ℝ)(k:ℕ)(t:Piece R l):ℂ:=
  oil (Q.fees l.h l.item) t.1 k μ * ActualOriginalDictionary.coordinates R B t.1.size t.1.grade t.1.2.2 t.2

def lamp {l:Label B}(t:Piece R l):Lamp G:=WilsonCoherentTerminalFrame.lamp R t.1.size t.2

theorem one (l:Label B)(μ:ℝ)(k:ℕ)(n:Side)(o:Site n)(U:Config G n):
    ActualOriginalCalibratedColumns.weightedObservable R B Q l μ n o U k=
      ∑t:Piece R l,weight R Q l μ k t*Light (lamp R t) n o U:=by
  rw [ActualOriginalCalibratedColumns.weighted_observable_original]
  conv_rhs => rw [Fintype.sum_sigma]
  apply sum_congr rfl
  intro a _
  let v:=ActualOriginalDictionary.coordinates R B a.size a.grade a.2.2
  have same:=ActualStencilCylinder.section_expansion (R.family.localSection a.size) (R.makes.sections a.size) v n o U
  change _*(R.family.localSection a.size).places v o U=_
  rw [same,mul_sum]
  apply sum_congr rfl
  intro j _
  rw [ActualStencilCylinder.observed_complex (R.family.localSection a.size) (R.makes.sections a.size) j n o U]
  change _*(_*(R.family.localSection a.size).places (Pi.single j 1) o U)=
    (_*_)*(R.family.localSection a.size).places (Pi.single j 1) o U
  exact (mul_assoc ..).symm

variable {I:Type}[Fintype I](l:I→Label B)(μ:ℝ)(k:I→ℕ)(reader:I→ℂ)

def coefficient (t:∀i,Piece R (l i)):ℂ:=∏i,reader i*weight R Q (l i) μ (k i) (t i)

def word (t:∀i,Piece R (l i)):I→Lamp G:=fun i=>lamp R (t i)

def marked {n:Side}(o:I→Site n)(U:Config G n):ℂ:=
  ∏i,reader i*ActualOriginalCalibratedColumns.weightedObservable R B Q (l i) μ n (o i) U (k i)

theorem expanded {n:Side}(o:I→Site n)(U:Config G n):
    marked R Q l μ k reader o U=∑t:∀i,Piece R (l i),coefficient R Q l μ k reader t*tally (word R l t) o U:=by
  unfold marked coefficient tally
  simp_rw [one R Q _ μ _ n _ U,mul_sum,←mul_assoc]
  rw [prod_univ_sum]
  apply sum_congr rfl
  intro t _
  rw [←prod_mul_distrib]
  rfl

/-- A normalized actual Wilson Haar measurement, before any Taylor truncation.
Each principal receives its own exact engineering power. -/
theorem pinned {f c:Side}(D:StepData c f)(u:FVA2.CityHistory.Pins G c)(o:I→Site f)(g:ℝ)(pg:0<g)
    (kernel:D.IsKernel (g⁻¹^2) G):
    (spinVac D u g)⁻¹ • D.push (g⁻¹^2) (fun V=>bare (g⁻¹^2) V • marked R Q l μ k reader o V) (Parcel.Oven.slice u g)=
      ∑t:∀i,Piece R (l i),coefficient R Q l μ k reader t*
        ((g:ℂ)^power (word R l t))*reads (word R l t) D u o g:=by
  let β:=g⁻¹^2
  let X(t:∀i,Piece R (l i)):=fun V:Config G f=>bare β V • tally (word R l t) o V
  let c₀:=coefficient R Q l μ k reader
  have good t:Integrable (X t) (prior G f):=((bare_cont β).smul (tally_cont (word R l t) o)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have common:(fun V:Config G f=>bare β V • marked R Q l μ k reader o V)=fun V=>∑t,c₀ t*X t V:=by
    funext V
    rw [expanded,Finset.smul_sum]
    apply sum_congr rfl
    intro t _
    dsimp only [X,c₀]
    rw [Complex.real_smul,Complex.real_smul]
    ring
  have moved:=linear D β kernel (Parcel.Oven.slice u g) c₀ X good
  change (spinVac D u g)⁻¹ • D.push β _ (Parcel.Oven.slice u g)=_
  rw [common,moved,Finset.smul_sum]
  apply sum_congr rfl
  intro t _
  change (spinVac D u g)⁻¹ • (c₀ t*survey (word R l t) D u o g)=
    c₀ t*(g:ℂ)^power (word R l t)*(g⁻¹^(power (word R l t)) • ((spinVac D u g)⁻¹ • survey (word R l t) D u o g))
  simp only [Complex.real_smul,Complex.ofReal_pow,Complex.ofReal_inv]
  have cancel:(g:ℂ)^power (word R l t)*((g:ℂ)⁻¹)^power (word R l t)=1:=by
    rw [←mul_pow,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr pg.ne'),one_pow]
  linear_combination -((spinVac D u g:ℂ)⁻¹*c₀ t*survey (word R l t) D u o g)*cancel

end YM.Integration.WilsonMatrixTicketLanesTerminalQWords
