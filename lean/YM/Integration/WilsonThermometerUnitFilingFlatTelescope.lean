import YM.Integration.WilsonThermometerUnitFilingRaw
import YM.Integration.WilsonThermometerOriginalScalarTelescope

/-! Chronological signed returns under the original Wilson law conditioned
at one declared older flat field. Every edge divides by its genuine common
vacuum only after assembling the complete unnormalized field. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingFlatTelescope
open Filter Function Finset MeasureTheory Lattice Wilson RG RG16 Overlay
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonThermometerUnitFilingCoarse
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) (N per:ℕ)
local notation "C" => R.family
local notation "X" j:max => Config G ((C).side j per)
local notation "W" j:max => (C).path.rep N per j

def numerator (j:ℕ) (f:(X j)→ℂ): (X j)→ℂ:=fun U=>((W j).eval U:ℂ)*f U

private theorem normalized {b j:ℕ} (f:(X b)→ℂ) (jb:j ≤ b):
    reading R (N:=N) (numerator R N per b f) j jb = actualTransport (C) (N:=N) f jb 1 :=
  WilsonThermometerUnitFilingPosterior.weighted R f jb

def debit (rows:∀j:ℕ,(X j)→ℂ) (j:ℕ): (X j)→ℂ :=
  fun U=> ((W j).eval U:ℂ)*(actualAverage C (N:=N) (rows (j+1)) U-rows j U)

def feeAt (v:ℕ) (rows:∀j:ℕ,(X j)→ℂ) (j:ℕ):ℂ:=
  if vj:v ≤ j then reading R (N:=N) (debit R N per rows j) v vj else 0

theorem edge {v j:ℕ} (vj:v ≤ j) (top:j+1 ≤ N) (rows:∀j:ℕ,(X j)→ℂ)
    (old:Integrable (numerator R N per j (rows j)) (prior G _))
    (young:Integrable (numerator R N per (j+1) (rows (j+1))) (prior G _)) :
    reading R (N:=N) (debit R N per rows j) v vj =
      reading R (N:=N) (numerator R N per (j+1) (rows (j+1))) v (vj.trans (Nat.le_succ j))-
      reading R (N:=N) (numerator R N per j (rows j)) v vj:=by
  let a:=actualAverage C (N:=N) (rows (j+1))
  have one:actualTransport C (N:=N) (rows (j+1)) (Nat.le_succ j)=a:=by
    rw [actualTransport_step C R.makes top _ (Nat.lt_succ_self j),actualTransport_base C R.makes top]
  have paid:Integrable (numerator R N per j a) (prior G _):=by
    have y:Integrable (fun U=>(W (j+1)).eval U • rows (j+1) U) (prior G _):=by
      rw [show (fun U=>(W (j+1)).eval U • rows (j+1) U)=numerator R N per (j+1) (rows (j+1)) by
        funext U;simp only [numerator,Complex.real_smul]]
      exact young
    have b:=actualTransport_weighted_integrable_of_integrable C R.makes top y (Nat.le_succ j)
    rw [one] at b
    rwa [show numerator R N per j a=(fun U=>(W j).eval U • a U) by
      funext U;simp only [numerator,Complex.real_smul]]
  have change:debit R N per rows j=numerator R N per j a-numerator R N per j (rows j):=by
    funext U;simp only [debit,numerator,Pi.sub_apply,mul_sub,a]
  have compose:reading R (N:=N) (numerator R N per j a) v vj =
      reading R (N:=N) (numerator R N per (j+1) (rows (j+1))) v (vj.trans (Nat.le_succ j)):=by
    have equal:=congrFun (actualTransport_tower C R.makes top (rows (j+1)) (Nat.le_succ j) vj) 1
    rw [one] at equal
    rwa [normalized,normalized]
  have sum:=WilsonThermometerUnitFilingRaw.add R (N:=N) (debit R N per rows j) (numerator R N per j (rows j))
    (change ▸ paid.sub old) old vj
  rw [show debit R N per rows j+numerator R N per j (rows j)=numerator R N per j a by rw [change,sub_add_cancel],compose] at sum
  exact eq_sub_iff_add_eq.mpr sum.symm

theorem original {v b:ℕ} (stop:v ≤ b) (top:b ≤ N) (rows:∀j:ℕ,(X j)→ℂ)
    (offered:∀j,v ≤ j → j ≤ b → Integrable (numerator R N per j (rows j)) (prior G _)):
    reading R (N:=N) (numerator R N per b (rows b)) v stop-rows v 1 =
      ∑j ∈ Ico v b,feeAt R N per v rows j:=by
  let f:=fun j=>if vj:v ≤ j then reading R (N:=N) (numerator R N per j (rows j)) v vj else 0
  have first:f v=rows v 1:=by
    rw [show f v=reading R (N:=N) (numerator R N per v (rows v)) v le_rfl by simp only [f,dif_pos le_rfl]]
    rw [normalized,actualTransport_base C R.makes (stop.trans top)]
  have last:f b=reading R (N:=N) (numerator R N per b (rows b)) v stop:=by simp [f,stop]
  have changes:(∑j ∈ Ico v b,feeAt R N per v rows j)=∑j ∈ Ico v b,(f (j+1)-f j):=by
    refine sum_congr rfl fun j hj=>?_
    have fwd:=mem_Ico.mp hj
    have jtop:j+1 ≤ b:=Nat.succ_le_of_lt fwd.2
    have grow:v ≤ j+1:=fwd.1.trans (Nat.le_succ j)
    rw [feeAt,dif_pos fwd.1];simp only [f,dif_pos fwd.1,dif_pos grow]
    exact edge R N per fwd.1 (jtop.trans top) rows (offered j fwd.1 fwd.2.le) (offered _ grow jtop)
  rw [changes,sum_Ico_eq_sub _ stop]
  simp_rw [sum_range_sub]
  rw [last,first]
  abel

end YM.Integration.WilsonThermometerUnitFilingFlatTelescope
