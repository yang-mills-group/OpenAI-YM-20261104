import YM.WilsonBridge.Blocks
/-!
# Spectral calculation for Landau resolution in exact MS propagator
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBridge.Full
open MS MS.Book MS.Book.Program MS.Swirl MS.Koszul MS.City MS.Native MS.Tone MS.Plane MS.Landau Lattice MS.Orbit MS.Orbit.Cog MS.Latch
open Function Finset FiniteDFT Tone.Frame Momentum
open scoped BigOperators Matrix
variable {G:Gauge}{n:Side}
local notation "J" => Glu G n
local notation "C" => Ghost G n
local notation "T₁" => Mode (StampA G) (Site n)
local notation "T₀" => Mode (StampC G) (Site n)
local notation "ϟ" => pictureA G n
local notation "Ϟ" => pictureC G n
variable (G n)
def Ns (t: Bool): Matrix J J ℂ:= (ChillP G n t).submatrix a a
def Ys (t: Bool): Matrix C J ℂ:= -( (ChillP G n t).submatrix c k )
abbrev harmonicC : Matrix C C ℂ:= FiniteDFT.mean (pictureC G n)
abbrev harmonicA : Matrix J J ℂ:= FiniteDFT.mean (pictureA G n)
namespace Spectra
abbrev bead (p: QP)(i:Axis):= Tone.bill p (Tone.Frame.z i)
variable {G n}
def bt (q:QP)(i j:Axis) : ℂ:= precision i j (wave q)
def legLen (q:QP):ℂ:= Momentum.sq (wave q)
abbrev ht (q:QP)(i j:Axis) : ℂ := bead q i * bead (-q) j * bt q i j
abbrev nt (q:QP)(i j:Axis) : ℂ:= ht q i j / legLen q ^ 2
abbrev xt (q:QP)(i:Axis) : ℂ:= bead q i * ( Complex.I*wave q i )
abbrev yt (q:QP)(i:Axis) : ℂ:= bead (-q) i * (-( Complex.I*wave q i )/ legLen q)
def Hz (q:QP) : Matrix (StampA G) (StampA G) ℂ:= fun i j=> if i.2=j.2 then ht q i.1 j.1 else 0
def Nz (q:QP) : Matrix (StampA G) (StampA G) ℂ:= fun i j=> if i.2=j.2 then nt q i.1 j.1 else 0
def Xz (q:QP) : Matrix (StampA G) (StampC G) ℂ:= fun i j=> if i.2=j then xt q i.1 else 0
def Yz (q:QP) : Matrix (StampC G) (StampA G) ℂ:= fun i j=> if i=j.2 then yt q j.1 else 0
private lemma beads (q:QP)(i:Axis): bead q i* bead (-q) i=1:= by unfold bead; rw [Tone.opp,mul_inv_cancel₀ (Tone.nonz q (z i))]
local notation "R₁" => F (StampA G) n
local notation "R₀" => F (StampC G) n
local notation "Aa"=> mid ( iA (G:=G) false ) (n:=n)
local notation "Cc"=> mid ( iC (G:=G) false ) (n:=n)
local notation "Kk"=> mid ( iA (G:=G) true ) (n:=n)
local notation "S"=> Near.flatH G n
private lemma spectrumH : R₁ * Matrix.reindex ϟ ϟ (H G n) * R₁ = -( ( at2 S ).submatrix Aa Aa ):= by
    rw [ up_kinetic,picture (iA false) (iA false) ]; change R₁ * (- _) * R₁ = _ -- defeq?
    rw [Matrix.mul_neg, Matrix.neg_mul]; rfl
private lemma spectrumX : R₁ * Matrix.reindex ϟ Ϟ (X G n) * R₀= (at2 S).submatrix Kk Cc:= by rw [up_kinetic,picture (iA true) (iC false) ]; rfl
private lemma spectrumN (t:Bool): Matrix.reindex ϟ ϟ (Ns G n t)= R₁ * ((ChillF G n t).submatrix Aa Aa) * R₁ := by unfold Ns; rw [voltF]; exact picture (iA false) (iA false) _
private lemma spectrumY (t:Bool): Matrix.reindex Ϟ ϟ (Ys G n t)= R₀ * ( -( (ChillF G n t).submatrix Cc Kk )) * R₁ := by
    rw [ Matrix.mul_neg,Matrix.neg_mul ]; unfold Ys; rw [voltF]; exact congr_arg Neg.neg (picture (iC false) (iA true) _ ) -- inference
@[simp] lemma laceA (i:StampA G)(v:Bool)(p:QP): lace (iA v i,p)=bead (-p) i.1:=rfl
@[simp] lemma flagA (i:StampA G)(v:Bool)(p:QP): Orbit.flag (iA v i) p=bead p i.1 :=rfl
@[simp] lemma flagC (i:StampC G)(v:Bool)(p:QP): Orbit.flag (iC v i) p=1 :=right0 p
@[simp] lemma laceC (i:StampC G)(v:Bool)(p:QP): lace (iC v i,p)=1:= flagC ..
-- new point identities
lemma FourierH : hats ϟ ϟ (H G n)=diagonalBlocks (Hz ∘ Coord):= by
    ext ⟨i,p⟩ ⟨j,q⟩:1; rw [measures_vertex,spectrumH,diagB]; dsimp only [Matrix.neg_apply,Matrix.submatrix_apply,mid,at2]; by_cases he:q=p; swap; · rw [ Near.S_hold _ _ _ _ he,neg_zero,mul_zero,if_neg (Ne.symm he)]
    subst q; rw [ Near.Neg_S, if_pos rfl,Near.oriented, laceA,laceA,neg_neg, mul_neg,← mul_assoc,lightW,one_mul ]; unfold Landau.choir; split_ifs with h; · rw [Function.comp_apply,Hz, if_pos (show i.2=j.2 from h)]; change -(bead _ _ * bead _ _ * -(bt (Coord p) i.1 j.1))=_; unfold ht; ring
    rw [Function.comp_apply,Hz, if_neg (show i.2≠j.2 from h),mul_zero,neg_zero]
lemma FourierX : hats ϟ Ϟ (X G n)=diagonalBlocks (Xz ∘ Coord):= by
    ext ⟨i,p⟩ ⟨j,q⟩:1; rw [measures_vertex,spectrumX,diagB]; dsimp only [Matrix.submatrix_apply,mid,at2]; by_cases he:q=p; swap; · rw [ Near.S_hold _ _ _ _ he,mul_zero,if_neg (Ne.symm he)]
    subst q; rw [ Near.Neg_S, if_pos rfl,Near.oriented,laceA,laceC,neg_neg, ← mul_assoc,lightW,one_mul ]; unfold Landau.choir; split_ifs with h; · rw [Function.comp_apply,Xz,if_pos (show i.2=j from h),mul_one]; rfl
    rw [Function.comp_apply,Xz, if_neg (show i.2≠j from h),mul_zero]
lemma FourierN : hats ϟ ϟ (Ns G n false)=diagonalBlocks (Nz ∘ Coord):= by
    ext ⟨i,p⟩ ⟨j,q⟩:1; rw [ measures_cov _ _ _ _ _ _ (spectrumN false), diagB ]; change vol n * Chill (mat n (Near.FinalK G)) (iA false i,p) (iA false j,-q)= if p=q then Nz (Coord p) i j else 0; by_cases he:p=q; swap; · rw [if_neg he, Near.chillOff _ _ _ _ (show -q≠-p from fun h=>he (neg_inj.mp h).symm ),mul_zero]
    subst q; rw [if_pos rfl, Near.ChillK,Near.Bass,← mul_assoc, scale_factor,mul_inv_cancel₀ (nonzero n),one_mul]; unfold Landau.choir; split_ifs with h; · rw [Nz, if_pos (show i.2=j.2 from h),flagA,flagA]; unfold nt ht legLen bt; unfold Near.Tail; rcases i with ⟨i,t⟩; rcases j with ⟨j,v⟩; simp [Landau.signA, mul_div_assoc] -- iA not syntactic
    rw [Nz,if_neg (show i.2≠j.2 from h),mul_zero]
lemma FourierY : hats Ϟ ϟ (Ys G n false)=diagonalBlocks (Yz ∘ Coord):= by
    ext ⟨i,p⟩ ⟨j,q⟩:1; rw [measures_cov _ _ _ _ _ _ (spectrumY false),diagB]; change vol n * (- Chill (mat n (Near.FinalK G)) (iC false i,p) (iA true j,-q))= if p=q then Yz (Coord p) i j else 0; by_cases he:p=q; swap; · rw [if_neg he, Near.chillOff _ _ _ _ (fun h=>he (neg_inj.mp h).symm ),neg_zero,mul_zero]
    subst q; rw [if_pos rfl,Near.ChillK,Near.Bass,mul_neg,← mul_assoc,scale_factor,mul_inv_cancel₀ (nonzero n),one_mul]; unfold Landau.choir; split_ifs with h; · rw [Yz,if_pos (show i=j.2 from h),flagC,flagA]; unfold yt Near.Tail legLen; rcases j with ⟨j,t⟩; simp [Landau.signA, neg_div, mul_div_assoc]
    rw [Yz,if_neg (show i≠j.2 from h),mul_zero,neg_zero]
local notation "Πp" => Hz (G:=G)
local notation "Φp" => Xz (G:=G)
local notation "Ψp" => Yz (G:=G)
lemma spectral_zero (p:Site n)(h:legLen (Coord p)=0): p=0:= by
    by_contra hp; obtain ⟨i,hi⟩:= Bloch.step_picks p hp
    have hz:= triangle i (-Coord p); rw [ neg_neg, wave_neg, Near.NoWave _ (show Momentum.sq (wave (Coord p))=0 from Complex.ofReal_eq_zero.mp h), neg_zero,Pi.zero_apply, Complex.ofReal_zero,mul_zero, neg_zero, mul_eq_zero,or_iff_right ( Tone.nonz _ _ ), sub_eq_zero, Tone.rights (Coord p), Orbit.dual_cell,Lattice.wrap_step ] at hz; exact hi hz
@[simp] lemma leg_zero : legLen ( Coord (0:Site n) )=0:= by simp [legLen,wave,ξ_zero,theta,Momentum.sq]
lemma hh_square (q:QP)(i j:Axis): (∑ k:Axis,ht q i k*ht q k j)=legLen q*ht q i j:= by
    have he k: ht q i k *ht q k j=(bead q i*bead (-q) j)*( bt q i k*bt q k j) := by unfold ht; linear_combination bead q i*bead (-q) j*(bt q i k*bt q k j)*(beads q k)
    have hu : (∑ k:Axis,bt q i k * bt q k j)= legLen q * bt q i j:= by unfold bt legLen; exact_mod_cast Landau.k_times i j ( wave q )
    simp_rw [ he, ← Finset.mul_sum,hu ]; unfold ht; ring
lemma fsq (q:QP): Πp q * Πp q= legLen q • Πp q:= by
    ext ⟨i,t⟩ ⟨j,u⟩:1; classical
    simp_rw [Matrix.mul_apply,Fintype.sum_prod_type,Matrix.smul_apply,Hz]; by_cases h:t=u
    · subst u; simpa [ite_mul,mul_ite] using hh_square q i j
    simp [h,ite_mul,mul_ite]
lemma nm_ratio (q:QP): Nz (G:=G) q=(legLen q)⁻¹^2 • Hz q:= by
    ext i j:1; simp_rw [ Matrix.smul_apply,Nz,Hz ]; split <;> simp [nt,div_eq_mul_inv,mul_comm]
lemma ht_xt (q:QP)(i:Axis): (∑ k:Axis, ht q i k * xt q k)=0:= by
    have he k: ht q i k*xt q k= bead q i*Complex.I*(bt q i k*wave q k):= by
        unfold ht xt
        linear_combination bead q i*bt q i k*(Complex.I*wave q k)*(beads q k)
    have hy (u: Momentum Axis): ∑ k:Axis, precision i k u*u k=0:= by simp_rw [ precision, delta, sub_mul,ite_mul,zero_mul,Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,mul_assoc, ← Finset.mul_sum,← pow_two ]; rw [← Momentum.sq,mul_comm (u i),sub_self]
    simp_rw [he,← Finset.mul_sum,show (∑ k:Axis, bt q i k*wave q k)=0 from (by unfold bt; exact_mod_cast hy (wave q)),mul_zero]
lemma fV_zero (q:QP) : Πp q * Φp q=0:= by
    ext ⟨i,t⟩ j:1; simp_rw [Matrix.mul_apply,Fintype.sum_prod_type,Hz,Xz]; by_cases h:t=j
    · subst j; simpa [ite_mul,mul_ite] using ht_xt q i
    simp [h,ite_mul,mul_ite]
private lemma cyc (q:QP)(i:Axis): yt q i * xt q i=(wave q i:ℂ)^2/(legLen q):= by
    unfold yt xt
    calc
      _= (bead q i *bead (-q) i)* (-(Complex.I^2) * ((wave q i:ℂ)^2/(legLen q))) := by ring
      _= _:= by rw [beads,Complex.I_sq]; ring
private lemma both (q:QP)(i j:Axis): xt q i *yt q j= bead q i*bead (-q) j*((wave q i:ℂ)*wave q j / legLen q):= by
    unfold xt yt; ring_nf; simp [Complex.I_sq] -- negative inversion
lemma Nhv (p:Site n)(h:p≠0) : Nz (Coord p) * Hz (Coord p) + Φp (Coord p)*Ψp (Coord p)=1:= by
    let q := Coord p; let L:= legLen q; have hl:legLen q≠0:= fun hc=> h (spectral_zero p hc)
    rw [nm_ratio,Matrix.smul_mul,fsq, smul_smul, show (legLen q)⁻¹^2*legLen q=(legLen q)⁻¹ from by field_simp ] -- rw maybe defeq fails. make q
    ext ⟨i,t⟩ ⟨j,u⟩:1; rw [show Coord p=q from rfl]; rw [Matrix.add_apply]; simp_rw [ Matrix.mul_apply,Matrix.smul_apply,Hz,Xz,Yz ]; -- order
    by_cases hc:t=u; swap; · simp [hc,ite_mul,mul_ite]
    subst u; simp only [ ite_mul,mul_ite, zero_mul, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,smul_eq_mul, both ]; unfold ht bt precision delta; by_cases h:i=j; · subst j; rw [beads q, if_pos rfl, Matrix.one_apply_eq]; unfold legLen; push_cast; unfold legLen at hl; field_simp; ring
    unfold legLen; unfold legLen at hl; simp [h]; ring -- no hl needed
lemma crossV (p:Site n)(h:p≠0): Ψp (Coord p)*Φp (Coord p)=1:= by
    let q:= Coord p; have hp: legLen q≠0:= fun hc=>h (spectral_zero p hc)
    ext i j:1; rw [show Coord p=q from rfl]; simp_rw [Matrix.mul_apply,Fintype.sum_prod_type,Yz,Xz]; by_cases he:i=j
    · subst j; simp [ite_mul,mul_ite,cyc, ← Finset.sum_div]; rw [show ∑ i:Axis,(wave q i:ℂ)^2=legLen q from (by simp [legLen,Momentum.sq]),div_self hp]
    simp [he,ite_mul,mul_ite]
lemma n0 : Nz (G:=G) 0=0:= by ext i j:1; simp [Nz,nt,legLen,wave,theta,Momentum.sq]
lemma Y0 : Ψp 0=0:= by ext i j:1; simp [Yz,yt,legLen,wave,theta]
lemma X0 : Φp 0=0:= by ext i j:1; simp [Xz,xt,wave,theta]
-- link homotopy on ambient blocks in actual positions
end Spectra
open Spectra
local notation "Pg" => Ys G n false
local notation "Pa" => Ns G n false
local notation "Λ" => Full.X G n
local notation "η" => Full.H G n
lemma transvers : Pa*Λ=0:= by
    apply (hats ϟ Ϟ).injective; rw [map_zero,hats_mul ϟ ϟ Ϟ,FourierN,FourierX]; ext i j:1; rw [diagX,diagB]; simp only [Function.comp_apply,nm_ratio, Matrix.smul_mul,Spectra.fV_zero,smul_zero]; simp
lemma project : Pa*η+Λ*Pg=1-harmonicA G n:= by
    apply (hats ϟ ϟ).injective; rw [map_add,hats_mul ϟ ϟ ϟ,hats_mul ϟ Ϟ ϟ,map_sub,FourierN,FourierH,FourierX,FourierY,hats_one,harmonicA, hats_mean ]; ext ⟨i,p⟩ ⟨j,q⟩:1; by_cases he:q=p; swap; · simp only [Matrix.add_apply,Matrix.sub_apply,diagX,diagB]; simp [Ne.symm he]
    subst q; simp only [ Matrix.add_apply, Matrix.sub_apply,diagX,diagB,if_true,Function.comp_apply ]; by_cases hp:p=0
    · subst p; rw [ξ_zero,n0,Y0,X0]; simp [constants,Matrix.one_apply]
    rw [← Matrix.add_apply,Nhv p hp]; simp [hp,constants,Matrix.one_apply]
lemma harmonicComm : Pa*η=η*Pa:= by
    apply (hats ϟ ϟ).injective; rw [ hats_mul ϟ ϟ ϟ, hats_mul ϟ ϟ ϟ,FourierH, FourierN ]; ext i j:1; rw [diagX,diagX,diagB,diagB]; split; · unfold Function.comp; rw [nm_ratio, Matrix.smul_mul,Matrix.mul_smul]
    rfl
lemma constants_d : Λ*harmonicC G n=0:= by
    apply (hats ϟ Ϟ).injective; rw [map_zero,hats_mul ϟ Ϟ Ϟ, harmonicC, hats_mean,FourierX]; ext ⟨i,p⟩ j:1; rw [diagX,diagB]; by_cases hp:p=0 <;> simp [hp,ξ_zero,X0,constants]
lemma constants_y : harmonicC G n*Pg=0:= by
    apply (hats Ϟ ϟ).injective; rw [map_zero,hats_mul Ϟ Ϟ ϟ, harmonicC,hats_mean, FourierY]; ext ⟨i,p⟩ j:1; rw [diagX,diagB]; by_cases hp:p=0 <;> simp [hp,ξ_zero,Y0,constants]
lemma noMeanX : Pg*Λ=1 - harmonicC G n:= by
    apply (hats Ϟ Ϟ).injective; rw [ hats_mul Ϟ ϟ Ϟ,map_sub,FourierX,FourierY,hats_one,harmonicC,hats_mean ]; ext ⟨i,p⟩ ⟨j,q⟩:1; by_cases he:q=p; swap; · simp only [Matrix.sub_apply,diagX,diagB]; simp [Ne.symm he]
    subst q; simp only [ Matrix.sub_apply,diagX, diagB,if_true, Function.comp_apply ]; by_cases hp:p=0; · subst p; rw [ξ_zero,X0]; simp [constants,Matrix.one_apply]
    rw [crossV p hp]; simp [hp,constants,Matrix.one_apply]
end YM.WilsonBridge.Full
