import YM.Integration.WilsonOriginalStarFlagMerger
import YM.Extra.SOURCE_HISTORIES.Birth

/-! The real masked-to-unmasked supplement of one enrolled bare column on its
own original second hard merger. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerSameWalkBirthShift
open Function Finset Lattice Wilson RG Source Marker QuadraticLocal Earn Sunrise
open Push Push.Corrected Push.AbsoluteSums Push.Local Animals MeasureTheory
open PhysicalNext.Repeat.Legato Extra.Trajectories ActualRunPhysicalPages
open Extra.Histories Labels
open scoped Classical BigOperators
variable {G:Gauge} {n:Side} {d:ℕ} {F:Frame G d} {A:Hol G}
  (P:Rep G n) (S:SectionData F) (sound:S.Sound A) (o:Site n) (v:F.Coeff)
local notation "J" => Stock.census Unit
local notation "home" => (fun _:Unit=>o)
local notation "X" => S.footprint o
local notation "f" => supplement S P o v

include sound in
theorem anchor : o∈X:=Finset.mem_image.mpr ⟨0,sound.anchored,by simp⟩

def sheet : Canopy.ShiftRows Unit Unit G P.p home J where
  place _ := ⟨X,⟨o,anchor S sound o⟩⟩
  soap _ _ U:=Poly.send ((J).fire ()) (f U)
  cost _ _:=by
    let C:ℂ→ₗ[ℂ] Poly J:={
      toFun:=Poly.send ((J).fire ())
      map_add':=send_add _
      map_smul':=by
        intro a b
        change Poly.send _ (a*b)=a • Poly.send _ b
        ext u;rw [Poly.part_smul,Poly.part_send,Poly.part_send]
        split <;> simp }
    refine ⟨fun z U=>congrArg C (supplement_gauge S P o sound v z U),
      C.toContinuousLinearMap.continuous.measurable.comp (supplement_meas S P o v),
      fun U W eq flags=>congrArg C (supplement_read S P o v U W eq flags),
      fun _ _ _ _ _=>anchor S sound o⟩
  clean _ _ U live clear:=live (by rw [healthy_supplement S P o sound v U clear,Poly.send_zero])
  skip _ _ _:=by rw [Poly.part_send,if_neg ((J).fire_hot ()).symm]
  single _ _ _:=Classical.byContradiction fun h=>disjoint_left.mp ((merges_of_tagged_mul h).choose_spec.1) (mem_singleton_self ()) (mem_singleton_self ())

local notation "W" => sheet P S sound o v
theorem log (U:Config G n):(W).log () U=Poly.send ((J).fire ()) (f U):=by
  simp only [Canopy.ShiftRows.log,sheet,tsum_fintype,Finset.univ_unique,Finset.sum_singleton]

theorem paid {w a B:ℝ} (hw:0<w) (nonneg:0≤B) (full:∀ U,‖f U‖≤B) :
    (W).Budget (fun _=>w) P.p.B a (w*B*Real.exp (a*coverNumber P.p.B X)):=by
  let Y:=Poly.send ((J).fire ()) (B:ℂ)
  refine ⟨fun _=>Y,?_,?_⟩
  · intro _ _ U c
    change ‖(Poly.send ((J).fire ()) _).part c‖≤(Poly.send ((J).fire ()) (B:ℂ)|>.part c).re ∧ (Poly.send ((J).fire ()) (B:ℂ)|>.part c).im=0
    simp only [Poly.part_send]
    split
    · simpa only [Complex.ofReal_re,Complex.ofReal_im, and_true] using full U
    · simp
  · have cost:Poly.price (fun _:Unit=>w) Y=w*B:=by
      dsimp only [Y]
      rw [Poly.solo,Complex.norm_real,Real.norm_of_nonneg nonneg]
      simp only [Poly.toll,Census.fire,prod_singleton]
    intro z
    let l:=if z∈X then Poly.price (fun _:Unit=>w) Y*Real.exp (a*coverNumber P.p.B X) else 0
    have lp:0≤l:=by unfold l;split;exact mul_nonneg (Poly.nonnegative (fun _=>hw) _) (Real.exp_pos _).le;exact le_rfl
    refine ⟨fun _=>lp,Summable.of_finite,?_⟩
    change ∑' _:Unit,l ≤ _
    rw [tsum_fintype,Finset.univ_unique,Finset.sum_singleton]
    unfold l
    split
    · rw [cost]
    · exact mul_nonneg (mul_nonneg hw.le nonneg) (Real.exp_pos _).le

end YM.Integration.WilsonThermometerSameWalkBirthShift
end
