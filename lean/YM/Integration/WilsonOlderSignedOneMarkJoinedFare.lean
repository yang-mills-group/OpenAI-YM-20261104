import YM.Integration.WilsonOlderSignedOneMarkTariff
import YM.Integration.WilsonOlderFreshReversionStore

/-! In the signed one-source return, the regular error of the measured
restamp adds to the original regular debt. Its failed masks keep their
own compulsory fee at the same root. -/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderSignedOneMarkJoinedFare
open Filter Finset Lattice Wilson RG QuadraticLocal Marker Planned.GuardedAtom Push.Local
open Source Labels Extra.Histories WilsonCenteredFiledAtoms WilsonCenteredLampCapture
open scoped Classical BigOperators
variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {n : Side} {d : ℕ} {F : Frame G d}

theorem original (p : BudgetPoint) (S : SectionData F) (Y : Hol G) (w : V→ℝ) (v : V) (Z : Support n)
    {r κ μ η K a b h f : ℝ} (wp : 0 < w v) (rp : 0 < r) :
    let s:=(Stock.census V).fire v
    let t:=Poly.toll w s
    let regular (e:ℝ):=WilsonOlderSignedSingletonFare.fare p S Y (Stoop.radius w r) s 1 Z 0
      (r⁻¹*e) (K*κ) κ η μ
    let mask (full:ℝ):=WilsonOlderSignedOneMarkMasks.fare p Z η t full κ
    let pair:=WilsonOlderFreshReversionStore.price p S Y Z 0 μ η κ t b f
    t*((regular a+mask h)+pair)=t*(regular (a+b))+t*(mask h+mask f) := by
  intro s t regular mask pair
  dsimp only [regular,mask,pair]
  unfold WilsonOlderFreshReversionStore.price WilsonOlderSignedSingletonFare.fare cartage
  simp only [t,s,Poly.solo_toll,Stoop.radius,norm_one,one_mul]
  field_simp [rp.ne',wp.ne']
  ring

end YM.Integration.WilsonOlderSignedOneMarkJoinedFare
