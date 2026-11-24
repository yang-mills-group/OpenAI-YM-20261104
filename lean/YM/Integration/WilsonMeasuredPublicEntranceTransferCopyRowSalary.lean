import YM.Integration.WilsonOriginalPublicTrialPhaseRowRun
import YM.Integration.WilsonMeasuredPublicEntranceTransferCopySpineCash

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceTransferCopyRowSalary
open Filter Real Lattice Wilson RG PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Bandage
open WilsonOriginalPublicTrialPhaseRowRun (width upper lower)
open WilsonOriginalPublicTrialPhaseLanding (first limits)
open WilsonOriginalPublicTrialPhaseSpine (capital)
open WilsonMeasuredPublicEntranceTransferCopySpineCash (stock)
open scoped Classical
variable {G:Gauge}(R:Run G)(simple:G.Simple)
local notation "S" => R.family.S
local notation "H" i:arg => R.family.path.levels.clock.hatBeta i
local notation "δ" => renal R.family.path.levels

theorem positive {V:Type} (w:V→ℝ)(pos:∀v,0<w v)(l:ℕ→V→ℝ)(K i:ℕ)(ik:i≤K)(v:V):
    0<width δ w l K i ik v:=by
  have back:∀n j:ℕ,∀hi:j≤K,j+n=K→0<width δ w l K j hi v:=by
    intro n
    induction n with
    | zero=>
      intro j _ eqn
      have eq:j=K:=by omega
      subst j
      rw [upper]
      exact pos v
    | succ n ih=>
      intro j _ eqn
      have step:j<K:=by omega
      have previous:=ih (j+1) (by omega) (by omega)
      rw [lower _ _ _ _ _ step]
      have hot:0<H (j+1):=zero_lt_one.trans_le (R.family.path.levels.fits.delayed (j+1)).le
      exact mul_pos (Real.rpow_pos_of_pos hot _) (limits previous _).1
  exact back (K-i) i ik (by omega)

include simple in
theorem original {V:Type} {c K:ℕ} (ck:c+1≤K) (d:V→ℕ) (D A e:ℕ) (C:ℝ) (cp:0≤C)
    (ds:∀v,d v≤D)(B w:V→ℝ)(bp:∀v,0≤B v)(pos:∀v,0<w v)
    (cut:∀v,(w v)⁻¹≤B v)(funded:∀v,B v≤C*(H K)^e)
    (heat:H K≤2*H c)(span:(S).a c/(S).a K≤(H c)^A):
    let l:=fun j v=>capital (S) (d v) K j (B v)
    ∀v,0<width δ w l K (c+1) ck v ∧
      (width δ w l K (c+1) ck v)⁻¹≤(4*(H c)^2)^(K-(c+1))*(stock C e*(H c)^(A*(D+4)+e)):=by
  intro l v
  let w₀(j:ℕ):ℝ:=if h:j≤K then width δ w l K j h v else 1
  have hp j (jh:j≤K):w₀ j=width δ w l K j jh v:=dif_pos jh
  have head:w₀ K=w v:=by rw [hp K le_rfl,upper]
  have fundedwidth:=WilsonMeasuredPublicEntranceTransferCopySpineCash.original R simple ck (d v) D A e (ds v) C (B v)
    cp (bp v) heat span (funded v) w₀ (head ▸ cut v)
    (fun j _ live=>hp j live ▸ positive R w pos l K j live v) (by
      intro j _ live
      rw [hp j live.le,hp (j+1) live,lower _ _ _ _ _ live])
  exact ⟨positive R w pos l K (c+1) ck v,hp (c+1) ck ▸ fundedwidth⟩
end YM.Integration.WilsonMeasuredPublicEntranceTransferCopyRowSalary
end
