import YM.RG05Readout.Shadows.Skew
/-!
# True return invoice at fixed physical reference

Propagation of arbitrary birth projection; fix once on base product without
counter labels, on the SAME Spine as the final composite. Record exact receipt
for genuineness of accumulated inverse. Later merge alternative reps via null
at each contributing root. Specter calculations use real Q not an OPE estimate!
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Shadow
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Bid
open Extra.Histories Push Local Planned.GuardedAtom Guard MergeProof Extra.Histories.Relay Native
open PhysicalNext.Repeat Lotus Motion Trace.Physical Offsets Copper View Address
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G} {N m n b p d:ℕ}{D:Address.Rail C}{B:ℕ→ℕ→ℝ}{x e E:ℝ}
set_option quotPrecheck false
variable (h:C.Makes){V:Sight C d p}{S:Emblems C d}
local notation "Z!"=> C.path.levels
local notation "R"=> C.path.rep N p
local notation "Ω"=> C.path.levels.clock.op
local notation "ζ"=> C.S.block
local notation "F₀" => Palette C d
local notation "S₁" => C.S.scale
local notation "P"=> Address.Sight C d p
local notation "κ"=> kappa C.path
local notation "ℓ"=> Copper.ld C.path.levels
local notation "ν"=> C.path.levels.clock.J
variable (hw: Awake D B b d)
noncomputable def tab (C:Family G)(e:ℝ)(n i:ℕ):ℝ:= Real.exp (-(C.S.scale n-C.S.scale i)/3)*e
local notation "U"=> tab C e n
lemma tab_one : (U) n=e:= by simp [tab]
lemma tab_pos {i:ℕ} (he:0≤ e): 0≤ (U) i:= mul_nonneg (Real.exp_pos _).le he -- i undecl
lemma tab_step : (U) m= Copper.trim (ζ m) * U (m+1):=by
    unfold tab trim; rw [← mul_assoc,Real.rpow_def_of_pos (by positivity),← Real.exp_add,Schedule.scale_succ]; congr 2; ring
variable (hv: Spine D B h b p d N V S)
-- Receipt for annihilation at older output
structure Halo (D : Address.Rail C){eC:C.Makes} (b m n p N d:ℕ)(V:Sight C d p) (y:ℕ→ Palette C d) (X: ∀ i:ℕ,Tape G (C.side i p)) (e:ℝ) :Prop where
    empty i : m≤ i → i ≤ n → ∃ z:Palette C d, Printed C d (C.path.rep N p i) 0 (kappa C.path i) (X i) z 0 (tab C e n i)
    gate (i:ℕ): m≤ i → i<n→∀ hi:i<N, Train (D N p i hi) (keys0 eC hi) (d:=d) (X (i+1)) (X i+V i (y i)) (Copper.ld C.path.levels i*tab C e n (i+1))
    spends (i:ℕ): m≤ i → i<n → size (y i)≤tab C e n i
variable (F:Tape G (C.side n p))
local notation "a!"=> Halo D (eC:=h)
include hv hw
lemma liftH (hk:b ≤ m)(hm:m ≤ n)(hN:n≤N)(P₀:Tape G (C.side n p)) (y':Palette C d) (hy:∃ z,Printed C d (R n) 0 (κ n) P₀ z 0 e):
    ∃ (y:ℕ→ Palette C d)(X: ∀ i:ℕ,Tape G (C.side i p)), y n=y' ∧ X n=P₀∧ Halo D (eC:=h) b m n p N d V y X e:=by
    induction hm using Nat.decreasingInduction with
    | self=>
       let X:∀ i:ℕ,Tape G (C.side i p):= update (fun _=>0) n P₀; refine ⟨fun _=>y',X,rfl,update_self ..,fun i hi hq=>?_,by intro i hi hh; omega,by intro i hi hh; omega⟩; obtain rfl:i=n:=le_antisymm hq hi; unfold X; rw [update_self,tab_one]; exact hy
    | of_succ i hi ih=>
       obtain ⟨y,X,hF,hX,hR⟩:=ih (hk.trans i.le_succ); have hK: i<N:=hi.trans_le hN; have hM: (R i).p=(Z!).budget i:=(h.wilson.represents N p i hK.le).vac
       obtain ⟨z,hz⟩:= hR.empty (i+1) le_rfl hi
       obtain ⟨L,u,hL,hu,z',hZ⟩:= dark_step h hK (hw.toll p i N hk hK) (V i) (hv.legal i hk hK.le) (X (i+1)) z (U (i+1)) hz (u:=keys0 h hK)
       refine ⟨update y i u,update X i (L-V i u), (update_of_ne hi.ne' ..).trans hF, (update_of_ne hi.ne' ..).trans hX,fun m' hk hS =>?_,fun m' hP hp he=> ?_,fun m' hP hp=> ?_⟩
       · by_cases hx:m'=i; subst m'; rw [update_self,tab_step]; exact ⟨z',hZ⟩
         rw [update_of_ne hx]; exact hR.empty m' (by omega) hS
       · rw [update_of_ne (show m'+1 ≠ i from by omega)]; by_cases hx:m'=i; subst m'; rw [update_self,update_self,sub_add_cancel]; exact hL
         rw [update_of_ne hx,update_of_ne hx]; exact hR.gate _ (by omega) hp he
       by_cases hx:m'=i; subst m'; rw [update_self,tab_step]; exact hu
       rw [update_of_ne hx]; exact hR.spends _ (by omega) hp
section pay
omit hv hw
variable {i:ℕ}
lemma now_step (hp: 12 ≤ ν i) : (ℓ i)*trim (ζ i) ≤ 9/10:=by
    let x:ℝ:=(ζ i).val; let y:ℕ:=ν (i+1)
    have hx : 3≤x:= by unfold x; exact_mod_cast (show 3 ≤ (ζ i).val from C.S.block_large i) -- x defeq?
    have ht : 0<x:=(by linarith only [hx]); have hy: 12 ≤ (y:ℝ):=by unfold y; exact_mod_cast (hp.trans ((Z!).fits.mono i.le_succ))
    have he: ((ℓ i)*trim (ζ i)) ≤ x^(-(1:ℝ)/4):=by
       change x^((1:ℝ)/((y:ℝ)+1))*x^(-(1:ℝ)/3)≤_; rw [← Real.rpow_add ht]; apply Real.rpow_le_rpow_of_exponent_le (by linarith only [hx]); have hx' : 1/((y:ℝ)+1) ≤ 1/12:= (div_le_iff₀ (by positivity)).mpr (by linarith only [hy]); linarith only [hx']
    refine he.trans ((Real.rpow_le_rpow_of_nonpos (by norm_num : (0:ℝ)<3) hx (by norm_num : (-(1:ℝ)/4)≤0)).trans ?_)
    apply le_of_pow_le_pow_left₀ (n:=4) (by decide) (by norm_num : (0:ℝ) ≤ 9/10)
    rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤ 3),show ( -(1:ℝ)/4)*(4:ℕ)=-1 from by norm_num]
    norm_num -- check lemma
variable {Y:ℕ→ Palette C d}
noncomputable def advances (S:Emblems C d)(Y:ℕ→ Palette C d) (b:ℕ)(m:ℕ): Palette C d := if h:b ≤ m then Nat.leRec (motive:=fun _ _=>Palette C d) 0 (fun {i} _ z=> (S i).symm (z-Y i)) h else 0
local notation "Θ"=> advances S Y b
lemma adv_base : Θ b=0:=by rw [advances,dif_pos le_rfl,Nat.leRec_self]
lemma adv_next (h:b ≤ m): Θ (m+1)=(S m).symm (Θ m - Y m):=by rw [advances,dif_pos (h.trans m.le_succ),Nat.leRec_succ (h1:=h),advances,dif_pos h]
lemma adv_leans (h:b ≤ m) : S m (Θ (m+1))= Θ m - Y m:= by rw [adv_next h,LinearEquiv.apply_symm_apply]
include hv
lemma overture (hk:12 ≤ ν b)(hN:n ≤ N)(hy:0≤ e)(hp : ∀ i,b ≤ i→ i < n → size (Y i) ≤ U i)(hx:b≤ m)(he:m ≤ n):size (advances S Y b m)≤ 20*U m:=by
    induction m,hx using Nat.le_induction with
    | base=> rw [adv_base,size_zero]; exact mul_nonneg (by norm_num) (tab_pos hy)
    | succ i hx ih=>
       have ht:=ih (i.le_succ.trans he); have h:=hv.follows i hx (he.trans hN); have hB:= tab_pos (C:=C) (n:=n) (i:=i+1) hy
       apply (size_refund (ζ i) _).trans ((h.strength (Θ (i+1))).1.trans _); rw [adv_leans hx,sub_eq_add_neg]; refine (mul_le_mul_of_nonneg_left ((size_add (Θ i) (-(Y i))).trans ((size_neg _|> (congr_arg (size (Θ i)+ ·)))|>.trans_le (add_le_add ht (hp i hx he)))) (zero_le_one.trans (lamp_nn _))).trans ?_
       change ℓ i* (20* U i+ U i)≤ _; rw [tab_step (m:=i)]
       have hp: ((ℓ i)*trim (ζ i))≤9/10:=now_step (hk.trans ((Z!).fits.mono hx)); nlinarith only [mul_le_mul_of_nonneg_right hp hB,hB] -- size_sub add rewrite
end pay
end YM.RG05Readout.Shadow
