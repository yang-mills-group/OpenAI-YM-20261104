import YM.Integration.FundedOriginalVacuumPaths
import YM.Integration.WilsonConditionalTaylorWindingField

/-! The positive-rank old upper winding action as an explicitly purchased,
signed finite polynomial on the kinetic path of the same original Run;
one correction per cutoff, in one spatial strip, works for all finite sides. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelVacuum
open Function Filter PowerSeries Lattice RG Wilson Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Physical WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Bloom
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Blue
open WilsonCoeffUV.Power WilsonCoeffUV.Embroider WilsonCoeffUV.Soil WilsonCoeffUV.Fk
open WilsonLimitConstruction
open scoped Classical BigOperators Topology
variable {G:Gauge}

def signed (R:Run G) (N j:ℕ) (n:Side) : Blue.Ink (Woods G n) :=
    -flash (Winding.emera (actionW R.family.path.levels R.metals.O N j) n)

def filed (R:Run G) (N j:ℕ) (n:Side) (X:SeriesA G) : Blue.Ink (Woods G n) :=
    -flash (lop (front (R.alloy.B.kin.path N j) (R.family.path.levels.params j).clip n+sands X n))

private theorem complete {R:Run G} {N j i:ℕ} {X:SeriesA G} (n:Side)
    (h:∀r,(front (R.alloy.B.kin.path N j) (R.family.path.levels.params j).clip n+sands X n) i (r+1)=
      lagoon (actionW R.family.path.levels R.metals.O N j i (r+1)) n):
    coeff i (signed R N j n)=coeff i (filed R N j n X):=by
  have bank : Winding.emera (actionW R.family.path.levels R.metals.O N j) n i =
      (lop (front (R.alloy.B.kin.path N j) (R.family.path.levels.params j).clip n+sands X n)) i := by
    funext r
    cases r with
    | zero=>rfl
    | succ r=>simpa only [Winding.emera,lop,Nat.succ_ne_zero,if_false] using (h r).symm
  simp only [signed,filed,map_neg,flash,coeff_mk,bank]

theorem original (R:Run G) (simple:G.Simple)
    (cover:WilsonConditionalTaylorSeparatedPurchase.Extra R.kit)
    (bought:FundedOriginalVacuumPaths.prices R.kit) (p:ℕ):
    ∃W:Credit,∀ᶠ j:ℕ in atTop,∃s:ℝ,0<s∧s⁻¹≤zz R.family.path.levels j∧∀N,j≤N→
      ∃X:SeriesA G,(∀a∈X,3≤a.grade)∧fromBefore X (3+p)∧X.length ≤ meterPre (3+p)∧
        Draw X s (W.buy (zz R.family.path.levels j)+zz R.family.path.levels j*R.family.path.levels.clock.loopCap j)∧
        ∀ n:Side,∀i<3+p,coeff i (signed R N j n)=coeff i (filed R N j n X):=by
  obtain ⟨W,paid⟩:=FundedOriginalVacuumPaths.corrections R simple (fun _ _=>1) cover bought p
  refine ⟨W,?_⟩
  filter_upwards [paid] with j hj
  obtain ⟨_,pos,width,next⟩:=hj
  refine ⟨_,pos,width,?_⟩
  intro N top
  obtain ⟨X,age,cut,number,draw,row⟩:=next N top
  exact ⟨X,age,cut,number,draw,fun n i hi=>complete n ((row i hi).2 n)⟩

end YM.Integration.WilsonConditionalTaylorWheelVacuum
end

