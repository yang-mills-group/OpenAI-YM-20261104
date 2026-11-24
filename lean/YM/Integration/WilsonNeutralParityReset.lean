import YM.Integration.WilsonNeutralParityWick
/-! Genuine bare sections, the common kinetic reset, and the marked
primary projection preserve total thermal and field parity. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonNeutralParityReset
open FormalBulk08 Reef Lava Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series
open Jets Work.F03 Work.F05 PowerSeries Bank Stationary Lotus Shore Mesa Gorge City Cork Rift Next.Free Flat RG Precision Tree
open Kemp Pose Glide Palm Wine Rial Roof
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical

open WilsonNeutralParityWick
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels

variable {G:Gauge} {d D l k j t:ℕ} {K:KernelChoices}
theorem bare {F:Frame G d}(T:SectionData F)(hf:d+1≤D)(u:Letter F)(f:Dawn.Studio D):
    Parity (Pose.slots F u) (Rial.sectionY T hf u f):=by
  intro e r live;by_contra wrong
  have ne:r≠(F.grades (mint F u)).2+e:=by
    change r ≠ Pose.slots F u+e; exact fun h=>wrong (congrArg (·%2) h)
  change (_:ℝ) • Rial.hymn (rancho (Rial.dabs T (mint F u)) e r) ≠0 at live
  rw [Rial.pinpaths T (mint _ _) e r ne,Rial.hymn_vanish,smul_zero] at live
  exact live rfl

private theorem even_bill (H U:Pence)(a:Still H)(b:Still U)(e j r:ℕ)
    (odd:(e-j)%2=1):Wine.bill H U e j r=0:=by
  apply (show Still (H^j*U^r) from ?_) (e-j) odd
  rw [Wine.still_flip] at a b ⊢
  unfold Wine.flipN at *
  rw [map_mul,map_pow,map_pow,a,b]

theorem reset {V:Type}{Z:OrbitV V}(hz:Parity l Z)(H U:Pence)(he:Still H)(ue:Still U):
    Parity l (Wine.stamp H U Z):=by
  intro e r diff;by_contra wrong
  apply diff;unfold Wine.stamp;apply Finset.sum_eq_zero;intro j hj
  have le:j≤e:=by simpa using hj
  by_cases hj':(e-j)%2=1
  · rw [even_bill H U he ue _ _ _ hj',zero_smul]
  · have zero: Z j r=0:=by by_contra live;have eq:=hz j r live;omega
    rw [zero,smul_zero]

theorem block (a:hue G)(P:Flight j t)(V:Lodge P.patch)(W:Pot G)(ρ:ChartRatio G)
    (h:P.patch.Branches K G)(hL:2≤P.L.val)(hv:Story W (Next.Free.pink K.penalty P.wing))
    (hr:LocalRatio ρ)(ht:4≤t)(d u:ℕ)(Y:Anthem D G)(hp:∀ f,Parity l (Y f))(f:Dawn.Studio D):
    Parity l (Roof.migrates a P V K W ρ h hL d u Y f):=by
  have fresh:=Wine.sig_mat a _ (Bank.creed P V W ρ h hv ht hr) K.penalty_pos ht
  exact reset (WilsonNeutralParityWick.average P V W ρ h Y hL hp hv.toVivid hr d u f)
    _ _ (Wine.even_book _ fresh.1 fresh.2) (Wine.even_coupon _ fresh.1 fresh.2)

theorem entry {F:Frame G d}{Y:Anthem D G}(p:∀ f,Parity l (Y f))(x:Letter F)(e:ℕ)
    (wrong:(Pose.slots F x)%2≠(l+e)%2):coeff e (Pose.echo F Y x)=0:=by
  rw [Pose.echoline];apply Finset.sum_eq_zero;intro r hr
  split
  next use =>
    have bound:r≤Pose.slots F x:=by simpa using hr
    have gone:Y (Pose.inside F x D) (e-(Pose.slots F x-r)) r=0:=by
      by_contra live;have h:=p _ _ _ live;omega
    rw [gone,Pose.chalk_void]
  rfl

end YM.Integration.WilsonNeutralParityReset
end
