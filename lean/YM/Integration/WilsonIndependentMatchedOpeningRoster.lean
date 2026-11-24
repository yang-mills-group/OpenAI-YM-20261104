import YM.Integration.WilsonIndependentMatchedOpeningColumn
import YM.Integration.WilsonIndependentRawRosterWord
/-! The complete unweighted opening in the canonical finite R/W stencil basis, with every ordinary product and constant. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedOpeningRoster
open Function Filter Finset PowerSeries Lattice RG Wilson Tree Source Labels XSpace XSpace.Rose Gauge
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Blue WilsonCoeffUV.Shard WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Embroider WilsonCoeffUV.Power WilsonCoeffUV.Bank
open PertExtension RegulatorIR RegulatorIR.Geometry RegulatorIR.Budget RegulatorIR.Budget.Packet
open RegulatorIR.Prim RegulatorIR.Diagram RegulatorIR.Halo RegulatorIR.Oracle RegulatorIR.Cluster
open RegulatorIR.Profiles
open WilsonIndependentRawRosterWord (bank degree)
open WilsonIndependentMatchedOpeningColumn (column)
open WilsonIndependentMatchedOrdinarySeat (here)
open WilsonIndependentSpoutOrdinaryPlate (sample)
open scoped Classical
variable {G:Gauge}{I:Type}(R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)
    (σ:I→Bool)(d:I→ℕ)(key:∀i,(R.family.labels.level (d i)).Index)
    {D:I→ℕ}(cut:∀i,d i<D i)
def seat {h:ℕ}(F:Frame G h)(a:F.Index):Alma F:=
  ⟨(a,⟨0,by simp⟩),by simpa [WilsonCoeffUV.Embroider.rankS] using F.bound a⟩

def field (o:I→ Cover):Composite I → Era G ℝ
  | .atom i=>column R W (σ i) (cut i) (seat (R.family.labels.level (d i)) (key i)) (o i)
  | .pair A B=>agateV (field o A) (field o B)

theorem enrolled (o:I→ Cover)(J:Composite I):
    Auth (J.accounts (degree R d key)) (field R W σ d key cut o J):=by
  induction J with
  | atom i=>exact WilsonIndependentMatchedOpeningColumn.enrolled R W (σ i) (cut i) (seat (R.family.labels.level (d i)) (key i)) (o i)
  | pair A B ha hb=>exact ha.manor hb

theorem ray (J:Composite I)(o:I→ Cover)(n:Side)(v:TreeVars G n):
    here n v (Blue.flash ((field R W σ d key cut o J).1 n))=
      shelter (J.accounts (degree R d key)) (bank R W σ d key J o) (sample v):=by
  induction J with
  | atom i=>exact WilsonIndependentMatchedOpeningColumn.ray R W _ _ _ _ n v
  | pair A B ha hb=>
    have ea:=enrolled R W σ d key cut o A
    have eb:=enrolled R W σ d key cut o B
    have ta:=WilsonIndependentRawRosterWord.enrolled R W σ d key A o
    have tb:=WilsonIndependentRawRosterWord.enrolled R W σ d key B o
    change here n v (Blue.flash (woad _ _))=shelter (_+_) (accord _ _) (sample v)
    rw [woadap _ _ (finite_shell (ea.span n)) (finite_shell (eb.span n)),map_mul,ha,hb]
    exact (shelter_pair (sample v) ta.1.canopy tb.1.canopy ta.2 tb.2).symm
end YM.Integration.WilsonIndependentMatchedOpeningRoster
