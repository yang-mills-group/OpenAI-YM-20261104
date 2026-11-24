import YM.Integration.WilsonIndependentConditionedBankRankedPorts

/-! Put the whole finite original fitted group field in an earlier reporting ruler on the same funded course. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedBankRulerPorts
open Function Filter Finset Lattice RG Wilson Source Labels XSpace XSpace.Rose XSpace.Cirrus
open PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Cosmos WilsonCoeffUV.Embroider
open WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Fountain PowerSeries
open WilsonIndependentConditionedBankSeats (Resident raw restored submitted)
open WilsonIndependentNotebookConstantSeat (issue)
open WilsonIndependentMatchedFiledIncome (plate charge)
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonIndependentNotebookRawSeat (component)
open WilsonOriginalPhysicalFruitVerse (written)
open scoped BigOperators Classical
variable {G:Gauge}{R:Run G}{d f K N per target:ℕ}{up:f ≤ K}{live:K ≤ N}{η:ℝ}

open WilsonIndependentConditionedBankRankedPorts (offered incoming)
local notation "a" => R.family.S.a

def rehome (r:Resident R d f K N per target up live η)(m:ℕ)(plain im:Bool):Verse (R.family.labels.level d):=
  ((a f/a m)^d) • incoming r plain im

theorem pace (m f K:ℕ):a f/a m*(a K/a f)=a K/a m:=by
  field_simp [(R.family.S.a_pos m).ne',(R.family.S.a_pos f).ne']

theorem original (r:Resident R d f K N per target up live η)(m:ℕ)(I₀:Initialize G)(survey plain im:Bool)
    {D e:ℕ}(fit:d<D)(A:Alma (R.family.labels.level d)→ℝ)(non:∀i,0 ≤ A i):
    let δ:=a K/a m;let F:=R.family.labels.level d;let X:=plate (sectionAt R I₀ survey d) fit
    let raw:=offered F plain im (WilsonIndependentConditionedBankSeats.raw r)
    Shrine X (rehome r m plain im)=δ^d • Shrine X raw ∧ charge e (rehome r m plain im) A=δ^d*charge e raw A:=by
  intro δ F X raw
  have n:0 ≤ (a f/a m)^d:=pow_nonneg (div_nonneg (R.family.S.a_pos f).le (R.family.S.a_pos m).le) _
  have eq:=WilsonIndependentConditionedBankRankedPorts.original (e:=e) r I₀ survey plain im fit A non
  have merge:(a f/a m)^d*(a K/a f)^d=δ^d:=by rw [←mul_pow,pace]
  refine ⟨?_,?_⟩
  · rw [rehome,StableStrip.shrine_μ,eq.1,smul_smul,merge]
  · rw [rehome,WilsonIndependentNotebookRawSeat.wages _ _ _ n,eq.2.1,←mul_assoc,merge]

theorem received (r:Resident R d f K N per target up live η){m:ℕ}(before:m ≤ f)(et:0 ≤ η)
    (plain im:Bool)(e:ℕ)(A:Alma (R.family.labels.level d)→ℝ)(non:∀i,0 ≤ A i){M:ℝ}
    (fare:charge e (submitted r im) A ≤ M*(a K/a f)^(-η)):
    charge e (rehome r m plain im) A ≤ M*(a K/a m)^(-η):=by
  have rp:0<a f/a m:=div_pos (R.family.S.a_pos f) (R.family.S.a_pos m)
  have r1:a f/a m ≤ 1:=(div_le_one (R.family.S.a_pos m)).mpr (R.family.S.strictAnti.antitone before)
  have fp:0<a K/a f:=div_pos (R.family.S.a_pos K) (R.family.S.a_pos f)
  have mp:0<a K/a m:=div_pos (R.family.S.a_pos K) (R.family.S.a_pos m)
  have shrink:a K/a m ≤ a K/a f:=by
    rw [←pace m f K]
    exact mul_le_of_le_one_left fp.le r1
  have salary (v:Verse (R.family.labels.level d)):0 ≤ charge e v A:=
    Finset.sum_nonneg fun i _=>WilsonIndependentMatchedFiledIncome.nonneg (non i) _ _
  have kept:=WilsonIndependentConditionedBankRankedPorts.budget r plain im e A non
  have mn:0 ≤ M:=nonneg_of_mul_nonneg_left ((salary _).trans fare) (Real.rpow_pos_of_pos fp _)
  have power:(a K/a f)^(-η) ≤ (a K/a m)^(-η):=by
    rw [Real.rpow_neg fp.le,Real.rpow_neg mp.le]
    exact (inv_le_inv₀ (Real.rpow_pos_of_pos fp _) (Real.rpow_pos_of_pos mp _)).2 (Real.rpow_le_rpow mp.le shrink et)
  rw [rehome,WilsonIndependentNotebookRawSeat.wages _ _ _ (pow_nonneg rp.le _)]
  exact (mul_le_of_le_one_left (salary _) (pow_le_one₀ rp.le r1)).trans
    (kept.trans (fare.trans (mul_le_mul_of_nonneg_left power mn)))

end YM.Integration.WilsonIndependentConditionedBankRulerPorts
