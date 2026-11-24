import YM.Integration.WilsonPositionProgramTrialPublicSticker
import YM.Integration.WilsonIndependentRawPhysicalFaces
import YM.Integration.WilsonIndependentMatchedOpeningMass

/-! Complete finite and infinite-cover products of test-valued public K fields on their
declared original rooted tree. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicGather
open Function Finset Lattice RG Source Labels FVA2 XSpace XSpace.Rose Wilson Tree
open WilsonCoeffUV WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider WilsonCoeffUV.Blue WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open RegulatorIR RegulatorIR.Cluster
open WilsonIndependentMatchedOrdinarySeat (here)
open WilsonIndependentRawRosterWord (fold)
open WilsonOriginalPublicNodalPlainSensor (sensor)
open scoped Classical BigOperators
variable {G:Gauge}{I:Type}

def gather (P:I→Era G ℝ):Composite I→Era G ℝ
  | .atom i=>P i
  | .pair A B=>agateV (gather P A) (gather P B)

theorem funded (P:I→Era G ℝ)(d:I→ℕ)(paid:∀i,Auth (d i) (P i))(J:Composite I):
    Auth (J.accounts d) (gather P J):=by
  induction J with
  | atom i=>exact paid i
  | pair A B ha hb=>exact ha.manor hb

theorem read (P:I→Era G ℝ)(d:I→ℕ)(paid:∀i,Auth (d i) (P i))(n:Side)(v:TreeVars G n)(J:Composite I):
    here n v (flash ((gather P J).1 n))=fold (fun i=>here n v (flash ((P i).1 n))) J:=by
  induction J with
  | atom i=>rfl
  | pair A B ha hb=>
    change here n v (flash (woad _ _))=_*_
    rw [woadap _ _ (finite_shell ((funded P d paid A).span n)) (finite_shell ((funded P d paid B).span n)),
      map_mul,ha,hb]

theorem extent {d u:I→ℕ}(less:∀i,d i≤u i)(J:Composite I):J.accounts d≤J.accounts u:=by
  induction J with
  | atom i=>exact less i
  | pair A B ha hb=>exact Nat.add_le_add ha hb

def ear (D:ℕ)(m:ℝ):Volume D:=m • page D (WilsonReceivedCanonicalSocketSeed.sheet D)

@[simp] theorem heard (D:ℕ)(m:ℝ):sensor D (ear D m)=m:=by
  simp [ear,map_smul,WilsonOriginalPublicNodalPlainSensor.unit]

end YM.Integration.WilsonPositionProgramTrialPublicGather
end
