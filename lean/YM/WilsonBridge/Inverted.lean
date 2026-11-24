import YM.WilsonBridge.Spectra
/-!
# Ambient kernel after inversion image, both legs

Exact momentum propagation of reflected links (offset included).
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBridge.Full
open MS MS.Book MS.Book.Program MS.Swirl MS.Koszul MS.City MS.Native MS.Tone MS.Plane MS.Landau Lattice MS.Orbit MS.Orbit.Cog MS.Latch
open Function Finset FiniteDFT Tone.Frame Momentum PertExtension
open scoped BigOperators Matrix
variable {V K:Type}[DecidableEq V][Fintype V]
variable {G:Gauge}{n:Side}
local notation "J" => Glu G n
local notation "C" => Ghost G n
local notation "I" => Index G n
local notation "Ns₀" => Ns G n false
local notation "Ys₀" => Ys G n false
local notation "Ϡ" => iota G n
local notation "U" => GU G n
local notation "T" => BH G
-- output basis action weighted *columns*
def Reflect (f:V→V)(u:V→ℂ): Matrix V V ℂ:= fun i j=> if i=f j then u j else 0
lemma reflects_right (f:V→V)(u:V→ℂ)(M:Matrix K V ℂ)(i:K)(j:V): (M*Reflect f u) i j=M i (f j)* u j:= by simp [ Reflect, Matrix.mul_apply,mul_ite ]
lemma reflects_left (f:V→V)(u:V→ℂ)(M:Matrix V K ℂ)(i:V)(j:K): ((Reflect f u).transpose*M) i j= u i* M (f i) j:= by simp [ Reflect,Matrix.mul_apply,ite_mul ]
omit [Fintype V] in
lemma reflects_symm (f:V→V)(u:V→ℂ)(he: Involutive f)(h:u ∘ f=u): (Reflect f u).transpose=Reflect f u:= by
   ext i j:1; unfold Reflect; rw [Matrix.transpose_apply ]; split_ifs with hx hx' <;> first| exact hx ▸ (congr_fun h i).symm | (simp [ *, he i,he j ] at *) -- type?
lemma reflec_squares (f:V→V)(u:V→ℂ)(hf: Involutive f)(he:∀ i,u (f i)*u i=1) : Reflect f u*Reflect f u=1:= by
   ext i j:1; rw [reflects_right,Reflect,hf j]; split_ifs with h; · subst j; rw [he,Matrix.one_apply_eq]
   simp [h]
-- positions
abbrev flipA (i:J) : J:= (Orb.reflect i.1,i.2)
abbrev flipC (i:C): C:= (-i.1,i.2)
def jump (i:T): Site n:= match i.1.1 with| none=>0| some d=>step d
def mesref (i:I): I:= (i.1,-i.2 - jump i.1)
variable (G n)
def Ra : Matrix J J ℂ:= Reflect flipA fun _=> -1
def Rc : Matrix C C ℂ:= Reflect flipC fun _=>1
def Rt : Matrix I I ℂ:= Reflect mesref (tick antiZ ∘ Prod.fst)
def Rhat : Matrix I I ℂ := Reflect (Ϡ).mode ( (Ϡ).spin ∘ (Ϡ).mode )
variable {G n}
lemma RA2 : Ra G n * Ra G n=1:= reflec_squares _ _ (fun i=>Prod.ext (Orb.reflect_reflect _) rfl) (fun i=> by simp)
lemma RC2 : Rc G n * Rc G n=1:= reflec_squares _ _ (fun _=>Prod.ext (neg_neg _) rfl) (fun _=> one_mul _)
lemma RA_symm : (Ra G n).transpose=Ra G n:= reflects_symm _ _ (fun _=>Prod.ext (Orb.reflect_reflect _) rfl) rfl
lemma RC_symm : (Rc G n).transpose=Rc G n:= reflects_symm _ _ (fun _=>Prod.ext (neg_neg _) rfl) rfl
lemma RT_symm : (Rt G n).transpose=Rt G n:= reflects_symm _ _ (fun i=>Prod.ext rfl (by simp [mesref])) rfl
lemma bill_step (i:T)(p:Site n): (lace (i, Coord p))^2= Bloch.cell p (-jump i):= by
    rcases i with ⟨⟨_|i,b⟩,j⟩; · change lace (iC b j, _ ) ^2 = Bloch.cell p (-(0:Site n)); simp only [Spectra.laceC,one_pow,neg_zero,Bloch.cell_origin]
    change lace (iA b (i,j), _ ) ^2= Bloch.cell p (- Lattice.step i); rw [Spectra.laceA,pow_two]; unfold Spectra.bead; rw [← rightadd,← Tone.Frame.centr,Tone.opp,Tone.rights,dual_cell,wrap_step,Bloch.cell_inverse ]
lemma Φrun : Rhat G n*U= U*Rt G n:= by
    ext ⟨i,p⟩ ⟨j,x⟩:1; rw [Rt,reflects_right,Rhat]; let F:= (Ϡ).mode; let H:= (Ϡ).spin;
    have ht : ((Reflect F ( H ∘ F ))*U) (i,p) (j,x) = H (i,p)* U ( i,-p ) (j,x):= by
       rw [Matrix.mul_apply, Finset.sum_eq_single_of_mem (i,-p) (Finset.mem_univ _)]; swap; · intro b _ hh; rw [Reflect,if_neg (show ¬ (i,p)=F b from fun h=> hh (by rw [ ← show F (F b)=b from (Ϡ).perm b,← h]; rfl)),zero_mul]
       simp only [Reflect]; rw [if_pos ( show (i,p)=F (i,-p) from Prod.ext rfl (neg_neg _).symm )]; unfold Function.comp; rw [show F (i,-p)=(i,p) from Prod.ext rfl (neg_neg _)]
    rw [ht]; unfold GU FiniteDFT.F; dsimp only [mesref]; by_cases he:i=j; swap; · rw [if_neg he,if_neg he,mul_zero,zero_mul]
    subst j; simp only [if_true, Function.comp_apply ]; unfold H; rw [ iota_spin ]; unfold switch gscore; dsimp only [ addr ]; rw [ bill_step, sub_eq_add_neg,Bloch.cell_add, Bloch.cell_duality (-p) x, Bloch.cell_inverse x p, Bloch.cell_duality x p, Bloch.cell_inverse p x ]; ring
local notation "Q" => ChillP G n
lemma images : Q true = Q false + Q false * Rt G n:= by
    have hu : ChillF G n true=ChillF G n false+ ChillF G n false * Rhat G n:= by
        ext i j:1; rw [Matrix.add_apply,Rhat,reflects_right]; change 2* (mat n _ i j + mat n _ i _ * _)= 2*mat n _ i j + 2*mat n _ i ((Ϡ).mode j)* ( ((Ϡ).spin ∘ (Ϡ).mode ) j); unfold Function.comp; ring
    rw [voltF,voltF,hu,Matrix.mul_add, Matrix.add_mul ]; simp only [ Matrix.mul_assoc, Φrun ]
lemma position_sym (t:Bool) : Cog.Sym (σbranch ( n:=n )) (HalfF G n t) := by
    let p := σbranch ( n:=n ) ( G:=G );
    intro i j; let B:= Near.Master G n t
    rw [ HalfF, entries,entries ]; rw [Finset.sum_comm]; -- which sum?
    simp_rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun k _=> Finset.sum_congr rfl fun x _=>?_); by_cases hx:U x i=0; · simp [hx]
    by_cases he:U k j=0; · simp [he]
    rw [ show σbranch i=σbranch x from tie_fwd Landau.parity i x hx,show σbranch j=σbranch k from tie_fwd Landau.parity j k he, Near.paySym t x k ]; ring
lemma Ns_sym (t:Bool): (Ns G n t).transpose=Ns G n t:= by
   ext i j:1; change Chill (HalfF _ _ _) _ _= Chill _ _ _; exact Eq.trans (Swirl.traceS (Full.a j) (Full.a i) (position_sym t)) (one_mul _)
lemma t_ck (i:J)(j:C)(t:Bool): ChillP G n t (k i) (c j)=Ys G n t j i:= by
   have he : ChillP G n t (k i) (c j)=-1* ChillP G n t (c j) (k i):= Swirl.traceS _ _ (position_sym t); rw [he,neg_one_mul]; rfl
lemma t_cY (i:J)(j:C)(t:Bool): ChillP G n t (c j) (k i)= -Ys G n t j i:= (neg_neg _).symm
lemma Υa : Ns G n true= Ns₀+Ns₀ * Ra G n:= by
    unfold Ns; rw [images]; ext i j:1; rw [ Matrix.submatrix_apply,Matrix.add_apply, Matrix.add_apply,Rt,reflects_right,Ra,reflects_right]; change _=(Q false (a i) _)+_; congr 2; -- j=..., rfl?
lemma Υa_comm : Ra G n * Ns₀= Ns₀ * Ra G n:= by
    have hx:= congr_arg Matrix.transpose (Υa ( G:=G ) ( n:=n )); rw [Ns_sym, Matrix.transpose_add,Matrix.transpose_mul,Ns_sym,RA_symm] at hx; exact add_left_cancel (hx.symm.trans Υa)
lemma Υc : Ys G n true= Ys₀+Ys₀ * Ra G n:= by
    ext i j:1; unfold Ys; simp_rw [Matrix.neg_apply, Matrix.add_apply, images, Matrix.submatrix_apply ]; rw [ Matrix.add_apply, Rt,reflects_right,Ra,reflects_right ]; rw [neg_add]; -- multiply `-` on left
    congr 1; exact (neg_mul ..).symm
lemma Υc_alt : Ys G n true= Ys₀+Rc G n * Ys₀:= by
    ext i j:1; rw [ ← t_ck j i true, images,Matrix.add_apply, Matrix.add_apply,Rt,reflects_right, ← RC_symm ( G:=G ) ( n:=n ), Rc, reflects_left ]; change ChillP G n false (k j) (c i) + ChillP G n false (k j) (_, -i.1-(0:Site n))* 1= Ys₀ i j + (1:ℂ)* Ys₀ (flipC i) j; rw [sub_zero]; change Q false (k j) (c i) + Q false (k j) (c (flipC i)) *1=_; rw [t_ck,t_ck,one_mul,mul_one]
lemma Υc_comm : Rc G n* Ys₀=Ys₀* Ra G n:= add_left_cancel ((Υc_alt).symm.trans Υc)
-- no other blocks propagate including B and its constants. no mode exception ignored.
def Attaches (i j: BH G) : Prop:= match i.1,j.1 with
    | (some _,false),(some _,false)=> True
    | (some _,true), (none,false)=> True
    | (none,false),(some _,true)=>True
    | _,_=>False
private lemma st_off (i j:I)(h: ¬ Attaches i.1 j.1): Near.Master G n false i j=0:= by
    have he : ∀ x:QP, Near.Tail i.1.1 j.1.1 (wave x)=0 := by intro x; rcases i with ⟨⟨⟨_|i,_|_⟩,t⟩,p⟩ <;> rcases j with ⟨⟨⟨_|j,_|_⟩,u⟩,q⟩ <;> first| rfl| exact (h True.intro).elim
    unfold Near.Master Orbit.Paper imageV; rw [if_neg (by decide)]; unfold mat; split; swap; rfl
    next => simp [EdgeV, Near.FinalK, Near.Bass, Landau.choir, he]
private lemma ms_off (t:Bool)(i j:I)(h:¬Attaches i.1 j.1): Near.Master G n t i j=0:= by
    cases t; exact st_off i j h
    change Near.Master G n false i j+ Near.Master G n false i ((Ϡ).mode j)*_= _; rw [st_off i j h, st_off i ((Ϡ).mode j) h,zero_mul,zero_add]
lemma chill_off (t:Bool)(i j:I)(h:¬ Attaches i.1 j.1): Q t i j=0:= by
    change 2* (HalfF G n t i j)=_; unfold HalfF; rw [entries,Finset.sum_eq_zero]; · exact mul_zero _
    intro a _; apply Finset.sum_eq_zero; intro b _; by_cases he:i.1=a.1; swap; · unfold GU FiniteDFT.F; rw [if_neg (Ne.symm he),zero_mul,zero_mul]
    by_cases hh:j.1=b.1; swap; · unfold GU FiniteDFT.F; rw [if_neg (Ne.symm hh),mul_zero]
    rw [ ms_off t a b (he ▸ hh ▸ h), mul_zero, zero_mul ]
end YM.WilsonBridge.Full
