import YM.Integration.WilsonIndependentFittedExteriorWheel
import YM.Integration.WilsonIndependentMatchedCoverProfile

/-! Changing a report's length unit on the literal placed test.  The active
visits are equal before the finite sum and every test derivative is retained. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentMatchedOwnHomeProfile
open Function Lattice Wilson RG
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Embroider WilsonCoeffUV.Shard
open WilsonIndependentFittedExteriorProfile (home)
open WilsonIndependentMatchedCoverProfile (word)
open scoped Classical BigOperators
variable {G:Gauge}{D:ℕ}

def scaled (φ:Rarity D)(T:ℝ)(pos:0<T):Rarity D:=home φ T⁻¹ (inv_pos.mpr pos) 0

theorem wheel (φ:Rarity D)(T:ℝ)(pos:0<T)(x y:ℝ)(o:CellR)(z:Cover):
    wheelC (x/T) (y/T) z (scaled φ T pos).ψ o=T^4 • wheelC x y z φ.ψ o:=by
  apply Subtype.ext
  funext w
  apply ContinuousMap.ext
  intro c
  change crease (sonal _ _ _ _ _) w.2 c.val=T^4*crease (sonal _ _ _ _ _) w.2 c.val
  have degree:=Nat.le_of_lt_succ w.1.isLt
  rw [currentP _ _ _ _ _ _ degree,currentP _ _ _ _ _ _ degree,
    scaled,WilsonIndependentFittedExteriorProfile.jet _ _ _ _ _ degree,
    WilsonIndependentFittedExteriorWheel.address_at,neg_zero,zero_add,inv_inv,
    smul_smul,mul_inv_cancel₀ pos.ne',one_smul]
  rw [div_pow]
  field_simp

theorem active (φ:Rarity D)(T:ℝ)(pos:0<T)(x y:ℝ)(xp:0<x)(o:CellR):
    VisitsT (scaled φ T pos) (x/T) (y/T) o=VisitsT φ x y o:=by
  ext z
  rw [visiting (div_pos xp pos),visiting xp,wheel,smul_ne_zero_iff]
  simp [pow_ne_zero 4 pos.ne']

private theorem tile (P:TowerS G D)(φ:Rarity D)(T:ℝ)(pos:0<T)(x y:ℝ)(o:CellR)(z:Cover):
    locale o (shoe P (scaled φ T pos) (x/T) (y/T) z)=T^4 • locale o (shoe P φ x y z):=by
  refine Prod.ext (funext fun n=>funext fun i=>funext fun r=>funext fun w=>?_)
    (funext fun i=>funext fun r=>funext fun w=>?_)
  · change P.1 n i r _ (wheelC _ _ _ _ o)=T^4*P.1 n i r _ (wheelC _ _ _ _ o)
    rw [wheel,map_smul];rfl
  change P.2 i r _ (wheelC _ _ _ _ o)=T^4*P.2 i r _ (wheelC _ _ _ _ o)
  rw [wheel,map_smul];rfl

theorem original (P:TowerS G D)(φ:Rarity D)(T:ℝ)(pos:0<T)(x y:ℝ)(xp:0<x)(o:CellR)(h:ℕ):
    word P (scaled φ T pos) (x/T) (y/T) o h=T^h • word P φ x y o h:=by
  unfold word
  rw [pupil_eye _ _ _ _ _ _ (div_pos xp pos),pupil_eye _ _ _ _ _ _ xp,active _ _ _ _ _ xp,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [tile,smul_smul,smul_smul]
  congr 1
  unfold drumB
  simp only [div_pow]
  field_simp

end YM.Integration.WilsonIndependentMatchedOwnHomeProfile
end
