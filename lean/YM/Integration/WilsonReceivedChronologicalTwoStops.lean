import YM.Integration.WilsonReceivedChronologicalPlant
import YM.Integration.WilsonOriginalTwoFlatRoseUpper

/-! A physical microscopic entrance and two earlier normalized sums on the same dated filings. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalTwoStops
open Function Finset MeasureTheory Lattice RG Wilson Marker Source Labels
open Extra.Histories Extra.Histories.Relay MergeProof Extra.Trajectories Extra.Multi
open PhysicalNext.Repeat.Legato
open WilsonThermometerUnitFilingFlatTelescope (numerator feeAt)
open WilsonOriginalTwoFlatGridScaling (gap)
open WilsonOriginalTwoFlatRoseIdentity (cross)
open WilsonOriginalMicroscopicEntranceDoseBoard (Board source)
open WilsonOriginalMicroscopicEntranceDoseGrid (mass)
open WilsonOriginalMicroscopicEntranceTwoExits (originalRead)
open WilsonOriginalMicroscopicEntrancePooledBoard (actual)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(d:Fin 3→ℕ){N per f n t:ℕ}
local notation "J" => Stock.census (Fin 3)
local notation "K" => f+n
local notation "fk" => Nat.le_add_right f n
local notation "X" j:max => Config G (R.family.side j per)
variable {o:Fin 3→Site (R.family.side f per)}(B:Board R d N per f o t)
  (active:f+n≤N)(v:∀a:Fin 3,R.family.label (d a))(c:Fin 3→ℂ)
  (past:∀j:ℕ,Config G (R.family.side j per)→Poly (Stock.census (Fin 3)))
local notation "table" => WilsonReceivedChronologicalPlant.rows R d (n:=n) (N:=N) o v c past
local notation "M" s:max => WilsonReceivedChronologicalReadout.face R N per (table) s
local notation "Y" s:max => actual R d B s c
local notation "due" b:max => WilsonOriginalJointTrialHearing.fee R N per (1:X b) (table)

theorem original {u b a:ℕ}(uf:u≤f)(ua:u≤a)(ba:b≤a)(aK:a≤K)
    (income:∀j,min u b≤j→j<K→Integrable (past j) (prior G _))(s:(J).Mode)(target:ℂ):
    R.family.omega N per (Y s)-target =
      gap R N per u ((ua.trans aK).trans active) (Y s)+
      mass c s*originalRead R d (p:=per) (f:=f) (n:=n) active (source R B) o v s uf 1+
      (∑j∈Ico a K,(due u) j s)+cross R (N:=N) ua ba (M s)+
      (∑j∈Ico b a,(due b) j s)+((M s) b 1-target):=by
  have paid (j:ℕ)(lower:min u b≤j)(upper:j≤K):Integrable ((table) j) (prior G _):=by
    rcases upper.eq_or_lt with eq | ht
    · subst j
      simpa only [WilsonReceivedChronologicalPlant.rows,Function.update_self] using
        WilsonReceivedChronologicalPlant.live R d o v c active
    · rw [WilsonReceivedChronologicalPlant.lower R d o v c past ht]
      exact income j lower ht
  have smooth:Continuous (Y s):=continuous_finsetProd _ fun i _=>continuous_const.mul
    (R.family.continuousO N per _ (source R B i) (WilsonThermometerReflectedTrajectory.anchorAt R (o i) N))
  have h:=WilsonOriginalTwoFlatRoseIdentity.figure R ua ba aK active (Y s) smooth (M s)
    (fun j hj jk=>by
      rw [WilsonReceivedChronologicalReadout.density R N per (table) s (jk.trans active)]
      exact ((Poly.get s).restrictScalars ℝ).integrable_comp (paid j hj jk)) target
  have birth:=WilsonOriginalMicroscopicEntrancePooledBoard.joined R d B active v s c uf (1:X u)
  rw [WilsonOriginalTwoFlatRoseUpper.law R (ua.trans aK) active (Y s) smooth (M s),
    WilsonReceivedChronologicalPlant.filed R d o v c active past s,←birth] at h
  have convert (b' l r:ℕ)(ib:b'≤l)(lb:min u b≤l)(rk:r≤K):
      (∑j∈Ico l r,feeAt R N per b' (M s) j)=∑j∈Ico l r,(due b') j s:=by
    refine sum_congr rfl fun j hj=>?_
    obtain ⟨lo,hi⟩:=mem_Ico.mp hj
    have jt:j+1≤K:=hi.trans_le rk
    exact WilsonReceivedChronologicalReadout.original R N per (table) s (ib.trans lo) (jt.trans active)
      (paid (j+1) ((lb.trans lo).trans (Nat.le_succ j)) jt) (paid j (lb.trans lo) (Nat.le_of_succ_le jt))
  rw [convert u a K ua ((min_le_left u b).trans ua) le_rfl,convert b b a le_rfl (min_le_right u b) aK] at h
  exact h

end YM.Integration.WilsonReceivedChronologicalTwoStops
end
