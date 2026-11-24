import YM.Integration.WilsonOriginalNullStored

/-! A field with zero raw seed has the same value at every enrolled output
horizon. Its physical derivatives, masks and exceptional owner are unchanged. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalNullReframe
open Labels Source Wilson RG Lattice Push.Local Planned.GuardedAtom
variable {G:Gauge} {e d:ℕ} {n:Side} {F:Frame G e} (J:Frame G d)

def restore (M:Raw F n) : Raw J n := ⟨0,M.bulk,M.forced⟩

theorem format (M:Raw F n) {o:Site n} {X:ℕ→Support n} {R:Rep G n}
    (h:M.Format o X R) : (restore J M).Format o X R := ⟨h.origin,h.regular,h.force⟩

theorem budget (M:Raw F n) {o:Site n} {X:ℕ→Support n} {R:Rep G n} {κ b c:ℝ}
    (h:Deck M o X R κ b c) : Deck (restore J M) o X R κ b c := ⟨h.bulk,h.packets⟩

theorem physical (M:Raw F n) (zero:M.seed=0) (o:Site n) (X:ℕ→Support n) (R:Rep G n)
    (T:SectionData F) (B:SectionData J) (U:Config G n) :
    (restore J M).eval o X B R U=M.eval o X T R U := by
  simp only [Raw.eval,restore,zero,map_zero,Pi.zero_apply]

end YM.Integration.WilsonOriginalNullReframe
