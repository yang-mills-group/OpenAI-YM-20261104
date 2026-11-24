import YM.Integration.WilsonThermometerPositionTunedChange
import YM.Integration.WilsonMaxwellThermometerPublicGalop

/-! The Galop field at its requested point in the original Wilson basis. Each
engineering component has its physical mesh power and its own complete Wick
correction. The same normalized vacuum tests every factor of a proper face. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerPositionTunedObserved
open Function Lattice Wilson Labels Source Source.Drops XSpace PhysicalNext.Repeat.Legato
open XSpace.Normalize XSpace.Cirrus XSpace.Rose XSpace.Structure1
open WilsonThermometerPositionTunedSurvey
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) (W:Initialize G)
def projected (k:ℕ) (v:On.Grade G k) : Labels.Label G k :=
  On.sectionMap k (Submodule.inclusion (show On.Grade G k ≤ Maxwell.shellSector G k from inf_le_left) v)

def fee (m:Mesh) (k:ℕ) (v:On.Grade G k) (b:(R.family.labels.level k).Index) : ℂ :=
  ((m.spacing:ℂ)^k)⁻¹ * rates R W k (projected k v) b

theorem one (m:Mesh) (k:ℕ) (o:m.Sites) (v:On.Grade G k) :
    W.atSite m k o v = ∑ b:(R.family.labels.level k).Index,
      fee R W m k v b • row R W k m.p (W.tree m.p) o b := by
  change ((m.spacing:ℂ)^k)⁻¹ • Bare.column _ (W.surveys k) o (projected k v) = _
  rw [corrected R W k, Finset.smul_sum]
  simp only [smul_smul,fee]

variable {n:ℕ} (x:Sample n) (d:ℕ)
def point (o:x.F.Sites) (v:Sec G d) : Bare.Series (W.tree x.F.p) G :=
  ∑ k:Fin (d+1), ∑ b:(R.family.labels.level k).Index,
    fee R W x.F k (part d k v) b • row R W k x.F.p (W.tree x.F.p) o b

theorem regal (o:x.F.Sites) (v:Sec G d) :
    Rose.regal W d x o v = point R W x d o v := by
  rw [Rose.regal,LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  exact one R W x.F k o (part d k v)

theorem ordinary (p:Tags G d n) (S:Finset (Fin n)) :
    Rose.numberA W d x p S =
      Bare.normalized (W.tree x.F.p) G (∏i∈S,point R W x d (chartV x i) (p i)) := by
  unfold Rose.numberA
  simp_rw [regal R W]

end YM.Integration.WilsonThermometerPositionTunedObserved
end
