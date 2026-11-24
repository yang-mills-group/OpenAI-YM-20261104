import YM.Integration.WilsonIndependentGroupedShelves

/-! The same auxiliary flat program funds the orbit and the cover at
logarithmic structural age. Top mesh units have fine spacing one. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentGroupedOrbitBills
open RegulatorIR Lattice RG RegulatorIR.Oracle RegulatorIR.Epoch
open RegulatorIR.Epoch.League RegulatorIR.Atlas RegulatorIR.Uniform
open RegulatorIR.Ledger RegulatorIR.Profiles RegulatorIR.Taping
open RegulatorIR.Calibration RegulatorIR.Momentum
open scoped ENNReal NNReal Classical

variable {X:Type}{M:X→ℕ}{n:Page M→Side}{K:KernelChoices}
  (G:Gauge)(Y:Program K)(Z:∀ P:Patch,P.Branches K G)(S:Circuit M n)
  (z:X→ℝ)(hz:∀ w,0≤z w)

def meter : Meter X where
  val w:= ENNReal.ofReal (1+z w)+ENNReal.ofReal (Real.log (S.P w))
  above w:= le_trans (by rw [←ENNReal.ofReal_one]
                         exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (hz w)))
                       le_self_add
  below _:=ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,ENNReal.ofReal_ne_top⟩

def top (M:X→ℕ) : Choice M:=⟨fun _=>0,fun _=>Nat.zero_le _⟩

theorem ports (start:∀ w,S.l (Page.opening M w)=1) :
    Ports S (top M) (stampE S z hz) (meter S z hz) where
  rail _:=rfl
  photo:=start
  fundZ := (Poly.roof (meter S z hz)).mono fun _=>le_self_add
  fundV := (Poly.roof (meter S z hz)).mono fun _=>le_add_self
  fundU := by
    suffices h : (fun w=>ENNReal.ofReal (-Real.log (S.l (Page.opening M w))))=0
      by rw [h]; exact Poly.zeroQ _
    funext w; simp [start]

variable {p b u:ℕ}{γ:ℝ}(t:Tent M)(g:G.ColorIndex)(simple:G.Simple)
    (pre:SatisfiesQ G Y S Z (stampE S z hz) p (quantum b u) γ)
    (start:∀ w,S.l (Page.opening M w)=1)
    (N:Notebook S Y G Z g (top M) t p)

include pre start simple N
theorem original (rate:0<b)(last:ℕ)(lastSide:∀ w,(n (Page.finallyW M w)).val≤last) :
    let L:=meter S z hz
    let c:=S.leadA Y G (quantum b u)
    let R:=S.lane Y G Z (sheet t)
    Cylinder R (S.payroll Y G Z (sheet t)) (S.pushP Y G) (S.takeP Y G) L c p b u ∧
      Lantern (S.dialect Y G Z (sheet t)) (top M) L c γ ∧ R.Endings L := by
  intro L c R
  have point:=ports S z hz start
  have age:=co_age S G Y Z point t
  have paid:=reservations S G Y Z (port_ref S point) age pre g N simple start
  exact ⟨paid.1.emits rate le_rfl,paid.2,closures S G Y Z age pre last lastSide t⟩

end YM.Integration.WilsonIndependentGroupedOrbitBills
