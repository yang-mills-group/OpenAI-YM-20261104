import YM.WilsonBridge.ActualFix
/-!
# Reprojection & change of alphabet. Lifted kernel is exactly terminal MS.Cog line

Operators use transposes for the slot maps. On the based alphabet Θ lets us compare
vertices on the support (A transverse, K longitudinal); genuine projection, no B leg.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBridge.Injections
open MS MS.Book MS.Koszul MS.City MS.Native MS.Tone MS.Plane Lattice MS.Orbit MS.Landau MS.Bare MS.Cylinder MS.Swirl
open Function Finset Full Based Based.Position Matrix
open scoped BigOperators Matrix
variable {I J V K R:Type}[Zero R]
variable {G:Gauge}{n:Side}
local notation "▷"=> Matrix.fromBlocks
local notation "GJ" => Position.Gluon G n
local notation "GC" => Position.Ghost G n
local notation "P" => Position.Parity G n
local notation "L" => Based.Letters GJ GC
local notation "V₀" => Full.alphabet G n
local notation "J₀" => Full.Glu G n
local notation "C₀" => Full.Ghost G n
local notation "E₀" => Full.Index G n
local notation "Ls" => Λe G n
local notation "Lv" => Λc G n
local notation "Po" => YsOrbit G n
local notation "No" => NsOrbit G n
local notation "S" => kinetic G n
local notation "So" => Kinetics.X ( Position.kinetic G n )
-- beware reindex's `Matrix.submatrix` orientation. Θ(neg).
abbrev diagM (a k:Matrix J V R)(c b:Matrix I K R) : Matrix (Letters J I) (Letters V K) R:= ▷ (▷ a 0 0 c) 0 0 (▷ k 0 0 b)
-- C output blocks
abbrev formK (N:Matrix J J ℂ)(Y:Matrix I J ℂ): Matrix (Letters J I) (Letters J I) ℂ:=
    ▷ (▷ N 0 0 0) (▷ 0 0 (-Y) 0) (▷ 0 Y.transpose 0 0) 0
-- push conventional covariance
lemma withK [Fintype V][Fintype K](a k:Matrix J V ℂ)(c b:Matrix I K ℂ)(N:Matrix V V ℂ)(Y:Matrix K V ℂ) : (diagM a k c b)*formK N Y*(diagM a k c b).transpose= formK (a*N*a.transpose) (c*Y*k.transpose):= by unfold formK diagM; simp only [Matrix.fromBlocks_transpose, fromBlocks_multiply, transpose_mul ]; simp [ Matrix.fromBlocks_multiply, ← Matrix.mul_assoc ]
variable [Fintype I][Fintype J][DecidableEq V][DecidableEq K]
omit [Fintype I][Fintype J][DecidableEq V][DecidableEq K] in
lemma tied (a k:Matrix J V ℂ)(c b:Matrix I K ℂ): Tie (Based.parity J I) (Based.parity V K) (fun i j => (diagM a k c b).transpose i j):= by rintro ((i|i)|(i|i)) ((j|j)|(j|j)) h<;> first| rfl| exact (h rfl).elim
@[simp] lemma alph_a (i:J₀): Full.alphabet G n (Based.a i)= Full.a i := rfl -- change below
@[simp] lemma alph_k (i:J₀): Full.alphabet G n (Based.k i)=Full.k i:= rfl
@[simp] lemma alph_c (i:C₀): Full.alphabet G n (Based.c i)=Full.c i:=rfl
@[simp] lemma alph_b (i:C₀): Full.alphabet G n (Based.b i)=Full.b i:=rfl
-- block proofs full covariance (chill_off true etc)
lemma image_table (t:Bool): (Full.ChillP G n t).submatrix V₀ V₀= formK (Full.Ns G n t) (Full.Ys G n t):= by
    ext i j:1; rcases i with (i|i)|(i|i)<;> rcases j with (j|j)|(j|j)
    · rfl
    · exact chill_off t (Full.a i) (Full.c j) not_false
    · exact chill_off t (Full.a i) (Full.k j) not_false
    · exact chill_off t (Full.a i) (Full.b j) not_false
    · exact chill_off t (Full.c i) (Full.a j) not_false
    · exact chill_off t (Full.c i) (Full.c j) not_false
    · exact t_cY j i t
    · exact chill_off t (Full.c i) (Full.b j) not_false
    · exact chill_off t (Full.k i) (Full.a j) not_false
    · exact t_ck i j t
    · exact chill_off t (Full.k i) (Full.k j) not_false
    · exact chill_off t (Full.k i) (Full.b j) not_false
    · exact chill_off t (Full.b i) (Full.a j) not_false
    · exact chill_off t (Full.b i) (Full.c j) not_false
    · exact chill_off t (Full.b i) (Full.k j) not_false
    · exact chill_off t (Full.b i) (Full.b j) not_false
variable (he: Even n.val)
local notation "Fp" => landauBasis G he
local notation "Ch" => Based.Kinetics.Fixing.half (landauBasis G he)
lemma fix_table : Matrix.of (Chill Ch)= formK No Po:= by ext i j:1; change Chill Ch i j=_; rw [( Fp ).ch]; rcases i with (i|i)|(i|i)<;> rcases j with (j|j)|(j|j)<;> rfl
omit [DecidableEq V] [Fintype I] in
lemma from_chill [Fintype V] (U: Matrix V I ℂ)(X: Cog.Grain V)(Y: Cog.Grain I)(hx:U.transpose* Matrix.of (Chill X)*U=Matrix.of (Chill Y) ): cov_push X U=Y:= by
    rw [show Matrix.of (Chill X)= (2:ℂ) • Matrix.of X from rfl, show Matrix.of (Chill Y)= (2:ℂ) • Matrix.of Y from rfl,Matrix.mul_smul, Matrix.smul_mul ] at hx; exact smul_right_injective (Matrix I I ℂ) (show (2:ℂ)≠0 from (by norm_num)) hx
-- lift. diagM new field operator.
variable (G n)
def Ux : Matrix L E₀ ℂ := (diagM Ls Ls Lv 0).transpose.submatrix id (V₀).symm
def Long : Matrix GJ GJ ℂ:= (kinetic G n).X * YsOrbit G n
def Short : Matrix GJ GJ ℂ := 1-Long G n
def Θ : Matrix L L ℂ := (diagM (Short G n) (Long G n) (1:Matrix GC GC ℂ) 0).transpose
variable {G n}
local notation "Foo" => diagM Ls Ls Lv 0
local notation "Θp" => Θ G n
local notation "η" => Ux G n
local notation "Jv" => Long G n
local notation "Jo" => Short G n
lemma at_Ux (i:L)(j:Based.Letters J₀ C₀): η i (Full.alphabet G n j)= Foo j i:= by simp only [Ux, Matrix.submatrix_apply,id_eq, Equiv.symm_apply_apply, Matrix.transpose_apply ]
lemma transports : Tie (σbranch ( n:=n )) P (fun i j=> η i j):= by
    intro i j h; obtain ⟨i,rfl⟩:= (V₀).surjective i; rw [show σbranch _= _ from Full.charges i]; dsimp only at h; rw [at_Ux] at h; exact tied _ _ _ _ i j h
lemma Upr : (η).transpose* Matrix.of (Chill Ch) * η= Matrix.of (Chill (Full.HalfF G n true)):= by
    have ht: Foo * Matrix.of (Chill Ch) * (Foo).transpose=(Full.ChillP G n true).submatrix V₀ V₀:= by rw [ fix_table he, withK, N_equi he,Y_equi he,image_table]
    ext i j:1; obtain ⟨i,rfl⟩:= (V₀).surjective i; obtain ⟨j,rfl⟩:= (V₀).surjective j; have hh:=congr_fun (congr_fun ht i) j; simp_rw [Matrix.mul_apply, Matrix.transpose_apply, at_Ux]; -- fold Foo
    simp_rw [Matrix.mul_apply, Matrix.transpose_apply] at hh; exact hh
lemma charge_push : cov_push Ch η=Full.HalfF G n true:= from_chill _ _ _ (Upr he)
lemma projection_tie : Tie P P (fun i j=> Θp i j):= tied _ _ _ _
include he
lemma supportedAA : Short G n * No * (Jo).transpose=No := by
    unfold Short; rw [Matrix.transpose_sub,Matrix.transpose_one]; unfold Long; rw [ortho he, Matrix.sub_mul,Matrix.one_mul, Matrix.mul_sub,Matrix.mul_one ]; have hv : No * (So * Po)=0:= by rw [← Matrix.mul_assoc,NX he,Matrix.zero_mul]
    have hr:= congr_arg Matrix.transpose hv; rw [Matrix.transpose_mul,ortho he, sym_n, transpose_zero ] at hr; rw [hr,sub_zero,hv,sub_zero]
lemma K_part : Po * (Jv).transpose = Po:= by unfold Long; rw [ortho he,← Matrix.mul_assoc, shadowProj he, Matrix.one_mul]
lemma firms : cov_push Ch Θp=Ch:= by
    apply from_chill; unfold Θ; rw [Matrix.transpose_transpose,fix_table he,withK,Matrix.one_mul,supportedAA he,K_part he ]
end YM.WilsonBridge.Injections
