import YM.Integration.WilsonOriginalMicroscopicEntranceResidualStock

/-! No connected conditional deposit can be incident to a vacuum or a
single original seat. Its two ordered companion factors read only quiet. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntrancePureModes
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Extra.Histories.Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open RG05Readout RG05Readout.Address RG05Readout.Records WilsonOriginalNullCorridor MergeProof MergeProof.Accent Marker
open WilsonPositionProgramOriginalBlockedTrial WilsonAddressedRestartedColumn
open WilsonOriginalMicroscopicGuardedTrial (guarded)
open WilsonOriginalMicroscopicEntranceDeposits (mean reading funded)
open WilsonOriginalMicroscopicEntranceEarlier (face salary)
open WilsonOriginalMicroscopicEntranceFiling (units supplied)
open WilsonOriginalMicroscopicEntranceGridRow (pin factor entered old signed)
open WilsonThermometerSolitaryExchange (share)
open WilsonOriginalMicroscopicEntranceGridStock (debt peer Filed account old_paid entered_paid panel)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(d:Fin 3→ℕ){N p f n:ℕ}
local notation "J" => Stock.census (Fin 3)
local notation "X" i:max => Config G (R.family.side i p)
local notation "K" => f+n
local notation "k₀" => Nat.le_add_right f n

def Basic (s:(J).Mode):Prop:=s=(J).quiet ∨ ∃a:Fin 3,s=(J).fire a

private theorem phase (x y g h:Fin 3→ℂ)(a:Fin 3)(s:(J).Mode)(low:Basic s):
    share x y a s=share g h a s:=by
  open WilsonThermometerSolitaryExchange in
  have free:(WilsonThermometerSolitaryExchange.token a).part (J).quiet=0:=by
    simp [WilsonThermometerSolitaryExchange.token,Ne.symm ((J).fire_hot a)]
  open WilsonThermometerSolitaryExchange in
  have base (z z':Fin 3→ℂ): (WilsonThermometerSolitaryExchange.peer z z' a).part (J).quiet=1:=by
    have one (i:Fin 3)(v:ℂ):(WilsonThermometerSolitaryExchange.factor i v).part (J).quiet=1:=by
      simp [WilsonThermometerSolitaryExchange.factor,Ne.symm ((J).fire_hot i)]
    fin_cases a <;> simp [WilsonThermometerSolitaryExchange.peer,one]
  rcases low with rfl|⟨i,rfl⟩
  · simp only [share,Poly.quiet_mul,free,mul_zero]
  · simp only [share,WardBin.Crest.fire_mul,base,free,mul_zero,one_mul,add_zero]

private theorem zero_dated {k:ℕ}(F:Fin 3→X k→ℂ)(available:∀a,funded (F a))(live:k≤N)(before:f≤k)
    (s:(J).Mode)(low:Basic s)(U:X f):
    ∑i∈Ico f k,reading R.family N F s.val f i U=0:=by
  rw [←WilsonOriginalMicroscopicEntranceDeposits.original R.family N F s.val R.makes available live before U]
  rcases low with rfl|⟨a,rfl⟩
  · simp only [Census.quiet,Finset.prod_empty,WilsonOriginalMicroscopicEntranceDeposits.singles]
    exact sub_eq_zero.mpr (actualTransport_const R.family R.makes live (1:ℂ) before U)
  · simp [Census.fire,WilsonOriginalMicroscopicEntranceDeposits.singles,mean,before]

theorem original (live:f+n≤N)(Y:∀a:Fin 3,R.family.label (d a))(o:Fin 3→Site (R.family.side f p))
    (v:∀a:Fin 3,R.family.label (d a))(Z:∀a:Fin 3,store R.family (d a) p f)
    (s:(J).Mode)(low:Basic s)(first second:X f→Fin 3→ℂ):
    WilsonOriginalMicroscopicEntranceResidualStock.remainder R d live Y o v Z s
        (fun a U=>share (first U) (second U) a s)=0:=by
  funext U
  have before:f≤f+n:=Nat.le_add_right f n
  have gone:debt R d live Y o v s U=0:=by
    unfold debt
    rw [zero_dated R _ (old_paid R d live Y o) (le_refl N) (before.trans live) s low U,
      zero_dated R _ (entered_paid R d (N:=N) (n:=n) o v) live before s low U,sub_self]
  simp only [WilsonOriginalMicroscopicEntranceResidualStock.remainder,gone,zero_add,Pi.zero_apply]
  apply Finset.sum_eq_zero
  intro a _
  rw [show peer R d live Y o v s a U=share (first U) (second U) a s from phase _ _ _ _ a s low,sub_self,mul_zero]

end YM.Integration.WilsonOriginalMicroscopicEntrancePureModes
end
