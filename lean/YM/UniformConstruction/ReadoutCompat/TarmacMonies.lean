import YM.RG17.Tarmac
set_option autoImplicit false
noncomputable section
namespace YM.RG17.ReadoutCompat
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Marker Source Overlay
open FullVolume.Sever MergeProof MergeProof.Accent Extra.Histories Extra.Trajectories Extra.Multi Next.Rank Edition Spindle SharpGram Trace RG12 Next.UVStress
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Bandage
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
set_option quotPrecheck false
variable {G:Gauge}(R:Run G)(h:Flick R.family.path.levels){f:Extraction.Order} {S:Table R.family.book}{F:Spec.Final R.family f S} (L:Layout F)(W:OPE.Services R.family f S)
variable {m p N k n:ℕ}{Γ:Census (Fin n)}
local notation "C"=> R.family
local notation "A"=> R.family.path
local notation "Gx"=> Pert.Asymptotics.regulatorRun R.family
local notation "ρ"=> R.family.path.rep
local notation "ι"=> R.family.path.levels
local notation "H"=> R.family.path.levels.clock.hatBeta
local notation "a"=> R.family.S.a
local notation "Λ"=> fun i=> Real.log (H i)

include h W
lemma monies {r:ℝ}(z x dα:ℕ) (k m:ℕ) (v:R.family.label z)(hm:m=L.level r)
    (hk:1≤ k) (he:R.family.ref z ≤ m)(ht:R.family.ref z≤k)(hx:k≤ N)(hy:m≤N) (hh: a m / a k ≤ (H k)^x) (hv: mass R.family z (L.shift z r v) ≤ (H k)^dα) :
    let y:= atRef L z r (N,p) v
    moneys R.family z k N p y ≤ (H k)^(1+x*(z+1)+dα):=by
   intro y; let b:=H k
   have hb :1 ≤b:= ((ι).fits.delayed k).le; have h₀: 0<b:= zero_lt_one.trans_le hb
   have hd: 1 ≤ b^x:= one_le_pow₀ hb
   have hf:=podQuota (i:=(N,p)) W hh hd F.room.cutoff y he ht hy hx
   have hpA : (0:ℝ)<a m:= (C).S.a_pos m
   have hpB : (0:ℝ)<a k:= (C).S.a_pos k
   have hp: quota C z m N p y= a m^z * mass C z ((L.shift z r) v):=by
      unfold y atRef; rw [← hm,quota_smul, quota_atK C F.room.cutoff _ _ (N,p) he hy,Complex.norm_real,Real.norm_of_nonneg (pow_pos hpA _).le]
      · exact R.makes
      · exact he
      exact hy
   let M:= mass C z (L.shift z r v)
   have hY:Spindle.paid C z k N p y= (a k^z)⁻¹ * quota C z k N p y:=by
      unfold Spindle.paid Price.awake; rw [Size.smul,norm_inv,norm_pow,Complex.norm_real,Real.norm_of_nonneg hpB.le]; rfl
   have ht: quota C z k N p y ≤ a k^z * (b^x)^(z+1) * b^dα:=by
      rw [hp] at hf
      exact hf.trans ((le_of_eq (show (a k/a m)^z*((b^x)^(z+1))*(a m^z*M) = a k^z*(b^x)^(z+1)*M from (by rw [div_pow]; field_simp))).trans (mul_le_mul_of_nonneg_left hv (by positivity))) -- hp pair inference m N p
   unfold moneys; apply le_trans (mul_le_mul (possibleOdds R h W hk) le_rfl (paid_pos ..) h₀.le); rw [hY]
   refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht (by positivity)) h₀.le).trans_eq ?_; change b * (_*_) = b^_; field_simp; ring

end YM.RG17.ReadoutCompat
