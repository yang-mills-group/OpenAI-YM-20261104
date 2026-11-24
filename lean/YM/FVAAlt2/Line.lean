import YM.MS.Swirl.Mill
import YM.FVAAlt2.Center

/-! range geometry, Fourier side. χᵢ−1=i qᵢ Uᵢ where U is
half-link phase (K shares A). Includes the high edge, midpoint sign, and
other order-two points exactly. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2
open Lattice Function MS MS.Koszul MS.Native MS.Plane MS.Landau MS.Cylinder MS.Tone
open MS.Momentum MS.Orbit MS.Orbit.Cog MS.Orbit.LogReal MS.Swirl MS.Swirl.Near Finset
open scoped Topology
variable {G:Gauge}{n:Side}

abbrev VacuumK (G:Gauge)(n:Side): Matrix (Mode G n) (Mode G n) ℂ:= Master G n false
abbrev QuotK (G:Gauge)(n:Side): Matrix (Mode G n) (Mode G n) ℂ:= Master G n true
abbrev vecBranch (k:G.ColorIndex)(i:Axis) : Branch G Axis := (Landau.gauge i,k)
abbrev kBranch (k:G.ColorIndex)(i:Axis) : Branch G Axis := (Landau.anti i,k)
abbrev cBranch (k:G.ColorIndex) : Branch G Axis := (Landau.ghost,k)
abbrev bBranch (k:G.ColorIndex) : Branch G Axis := (Landau.gaugeC,k)

local notation "S" => Site n
local notation "ℐ" => Complex.I
local notation "A" => Mode G n
local notation "p₀" => Draft.DotFlip
local notation "M" => VacuumK G n
open Matrix

abbrev Wave (p : Site n):= MS.Momentum.wave (Coord p)
abbrev kin (p : Site n)(i : Axis):ℂ:= Wave p i
abbrev ell (p:S):ℂ:= (Wave p).sq
abbrev amp (p:S)(i:Axis):ℂ:= bill (Coord p) (Tone.Frame.z i)
abbrev oprec(p:S)(i j:Axis):ℂ:= precision i j (Wave p)
abbrev normK(n: Side):ℂ:= scaleZ n /2

lemma normK_ne (n:Side) : normK n ≠0 := div_ne_zero (Complex.ofReal_ne_zero.mpr (ν_pos n).ne') (by norm_num)
lemma kn_amp (p:S)(i:Axis) : amp p i- (amp p i)⁻¹= ℐ * kin p i:= by simpa only [Tone.inverse] using Tone.Frame.s_wave (Coord p) i
lemma kn_G (p:S)(i:Axis): Bloch.cell p (Lattice.step i) = amp p i * amp p i:= by
  rw [← wrap_step n i, ←dual_cell, Tone.rights, Tone.Frame.centr, rightadd] -- check wrap_step
lemma kn_diff (p:S)(i:Axis): Bloch.cell p (Lattice.step i)-1=amp p i * (ℐ * kin p i):= by rw [← kn_amp, mul_sub,mul_inv_cancel₀ (nonz _ _),kn_G]
lemma kn_opp (p:S)(i:Axis): 1-Bloch.cell p (-Lattice.step i)=(amp p i)⁻¹ * (ℐ * kin p i):= by rw [←kn_amp,Bloch.cell_inverse,kn_G,_root_.mul_inv_rev,mul_sub,inv_mul_cancel₀ (nonz _ _)]
lemma Wave_zero (n:Side): Wave (0:Site n)=0:= by unfold Wave; rw [ξ_zero]; funext; simp [wave,theta]
lemma ell_sum (p:S): (∑ i, kin p i*kin p i)=ell p := by simp [kin,ell,Momentum.sq,Complex.ofReal_sum,pow_two]
lemma ell_live {p:S}(he:p≠0): ell p ≠ 0:= by
  intro ht; have hz:= NoWave (Wave p) (Complex.ofReal_eq_zero.mp ht)
  obtain ⟨i,hi⟩:= Bloch.step_picks p he
  apply hi; rw [← sub_eq_zero,kn_diff]
  unfold kin; simp only [hz,Pi.zero_apply,Complex.ofReal_zero,mul_zero]

lemma oprec_eq(p:S)(i j:Axis): oprec p i j=(if i=j then ell p else 0)-kin p i*kin p j:= by unfold oprec precision; split <;> simp [kin,delta,ell, *] -- comma star
lemma kn_vecProd (p:S)(f:Axis→ℂ)(i:Axis): (∑ j, oprec p i j * f j)=(ell p * f i-kin p i * ∑ j, kin p j*f j):= by simp_rw [oprec_eq,sub_mul,mul_assoc (kin p i), Finset.sum_sub_distrib,← Finset.mul_sum]; simp only [ite_mul,zero_mul,sum_ite_eq,mem_univ,if_true]
lemma kn_vecCancel (p:S)(f:Axis→ℂ): (∑ i:Axis, kin p i * (∑ j, oprec p i j*f j))=0:= by
  simp_rw [kn_vecProd,mul_sub,mul_left_comm _ (ell p), show ∀ (x:Axis) z, kin p x*(kin p x*z)=kin p x*kin p x*z from fun x z=> (mul_assoc ..).symm, Finset.sum_sub_distrib, ← Finset.mul_sum,← Finset.sum_mul,ell_sum,sub_self]

lemma flag_A (p:S)(k:G.ColorIndex)(i:Axis): Orbit.flag (vecBranch k i) (Coord p)=amp p i:=rfl
lemma flag_K (p:S)(k:G.ColorIndex)(i:Axis): Orbit.flag (kBranch k i) (Coord p)=amp p i:=rfl
lemma flag_c (q:QP)(k:G.ColorIndex): Orbit.flag (cBranch k) q=1:= right0 _
lemma flag_b (q:QP)(k:G.ColorIndex): Orbit.flag (bBranch k) q=1:= right0 _
lemma flag_op (q:QP)(b:Branch G Axis): Orbit.flag b (-q)=(Orbit.flag b q)⁻¹:=opp ..

lemma column_val (p:S)(k:G.ColorIndex) (a b : Atom Axis) :
    M ((a,k),p) ((b,k),-p)= normK n * Orbit.flag (a,k) (Coord p) * Orbit.flag (b,k) (-Coord p) * Tail a b (Wave p):= by
  change mat n _ _ _=_; unfold mat; rw [if_pos (show p= - - p from (neg_neg _).symm)]
  dsimp only; unfold EdgeV FinalK Bass Landau.choir normK; rw [if_pos (show k=k from rfl)]; ring
lemma row_vec (p:S)(k:G.ColorIndex)(a:Atom Axis)(f:A→ℂ):
    (M *ᵥ f) ((a,k),p) = ∑ i:Atom Axis,M ((a,k),p) ((i,k),-p)*f ((i,k),-p) := by -- syntax fix
  unfold Matrix.mulVec dotProduct
  simp_rw [Fintype.sum_prod_type (α₁:=Branch G Axis) (α₂:=Site n),Fintype.sum_prod_type (α₁:=Atom Axis) (α₂:=G.ColorIndex)]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_eq_single k, Finset.sum_eq_single (-p)]
  · intro x hx hv; change mat n _ _ _ * _ =_; unfold mat; rw [if_neg (show p≠ -x from fun h=> hv (by rw [h,neg_neg])),zero_mul]
  · simp
  · intro d _ hd; refine Finset.sum_eq_zero fun x _=>?_ ; change mat n _ _ _ * _ =_; unfold mat; split; unfold EdgeV FinalK Bass Landau.choir; rw [if_neg (show k≠ d from hd.symm)]; ring; exact zero_mul _
  simp
lemma row_A (p:S)(k:G.ColorIndex)(i:Axis)(f:A→ℂ) : (M *ᵥ f) (vecBranch k i,p)= normK n * amp p i / (ell p)^2 * ∑ j:Axis, oprec p i j * ((amp p j)⁻¹ * f (vecBranch k j,-p)):=by
  rw [row_vec]
  simp_rw [Fintype.sum_prod_type,Fintype.sum_option,Fintype.sum_bool,column_val]; simp only [vecBranch,Landau.gauge,Tail,mul_zero,zero_mul,add_zero,zero_add]; push_cast; rw [Finset.mul_sum]; refine sum_congr rfl fun j _=>?_ ; rw [flag_op, flag_A p k i,flag_A p k j]; unfold ell oprec; ring
lemma row_c (p:S)(k:G.ColorIndex)(f:A→ℂ):(M *ᵥ f) (cBranch k,p)= normK n *ℐ /ell p * ∑ i:Axis, kin p i * ((amp p i)⁻¹ * f (kBranch k i,-p)):= by
  rw [row_vec]; simp_rw [Fintype.sum_prod_type,Fintype.sum_option,Fintype.sum_bool,column_val]; simp only [ghost,Tail,mul_zero,zero_mul,add_zero,zero_add]; rw [Finset.mul_sum]; refine sum_congr rfl fun j _=>?_ ; rw [flag_c (Coord p) k,flag_op _ (kBranch k j),flag_K]; push_cast; unfold ell kin kBranch anti; ring
lemma row_K (p:S)(k:G.ColorIndex)(i:Axis)(f:A→ℂ) : (M *ᵥ f) (kBranch k i,p)= normK n * amp p i * (ℐ*kin p i/ell p) * f (cBranch k,-p):= by
  rw [row_vec]; simp_rw [Fintype.sum_prod_type,Fintype.sum_option,Fintype.sum_bool,column_val]; simp only [anti,Tail,mul_zero,zero_mul,add_zero,zero_add,Finset.sum_const_zero]; rw [flag_c _ k,flag_K]; push_cast; unfold ell kin cBranch ghost; ring
lemma row_b (p:S)(k:G.ColorIndex)(f:A→ℂ): (M *ᵥ f) (bBranch k,p)=0:= by
  rw [row_vec]; simp_rw [Fintype.sum_prod_type,Fintype.sum_option,Fintype.sum_bool,column_val]; simp [gaugeC,Tail]
end YM.FVAAlt2
