import YM.WilsonBridge.Injections
import YM.WilsonBridge.TreeFix
/-!
# Actual Landau resolution, as gauge fixing on based orbit charts
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBridge.Injections
open MS MS.Book MS.Koszul MS.City MS.Native MS.Tone Lattice MS.Orbit MS.Landau MS.Bare MS.Cylinder MS.Cylinder.Taylor
open Function Finset FiniteDFT Full Based Based.Position PertExtension Orb
open scoped BigOperators Matrix
variable {G:Gauge}{n:Side}{V:Type}
local notation "Πₐ" => Position.E G n
local notation "J" => Full.Glu G n
local notation "Lv" => Λe G n
local notation "Ls" => Λc G n
local notation "Rcc" => Rc G n
local notation "R" => Ra G n
local notation "Z" => Full.harmonicA G n
local notation "Vx" => Full.X G n
local notation "N" => Full.Ns G n false
local notation "H" => Full.H G n
local notation "W" => Full.Ys G n false
local notation "SΨ" => Position.kinetic G n
local notation "Ξ" => Kinetics.X ( Position.kinetic G n )
local notation "He" => Kinetics.H ( Position.kinetic G n )
local notation "GJ" => Position.Gluon G n
local notation "GC" => Position.Ghost G n
lemma actually_rent : ( (Native.Chart.rent (G:=G) ( Native.Chart.drive n )) ∘ liftA G n ) = (2:ℝ) • exponent G n:= by funext i; rw [Pi.smul_apply, multiplier ]; unfold liftA; simp only [smul_eq_mul, Function.comp_apply]; ring
lemma basis_h :  (Lv).transpose * H * Lv= He+He := by
    let B:= Native.Chart.drive n; let V := Native.Chart.rent B (G:=G)
    let e:= liftA G n; let P:= glyph e
    let L:= e.toContinuousLinearMap
    let Zx := ink (priv (G:=G) (Q:=Edge (Site n))) V; let Zb:= ink (priv (G:=G) (Q:=OEdge n)) (exponent G n)
    have hv: pull (Lv).transpose Zx=(2:ℂ) • Zb:= by rw [ show (Lv).transpose=P.transpose.map ((↑):ℝ→ℂ) from rfl, show pull (P.transpose.map _) Zx = ink (L ∘ priv) V from pull_ink _ _ (L ∘ priv) _ (Native.Chart.rent_s _) (fun i=> (Native.frame (e (priv i))).symm), ← ink_ctrl_one _ L (show germ V from Native.Chart.rent_s _),show V ∘ L=(2:ℝ) • exponent G n from actually_rent, ink_smul _ ( expGerm G n ) ]; norm_num; rfl
    have ht : H= -(at2 Zx) :=by ext i j:1; rw [ H_entry i j ]; rfl
    have hh:= congr_arg at2 hv; rw [ Full.pull_two, Matrix.transpose_transpose ] at hh; rw [ht,Matrix.mul_neg, Matrix.neg_mul, hh ]; ext i j:1; change - (2 * (((layer _ (layer _ (exponent G n)) 0):ℝ):ℂ))= _; rw [ two_layer (expGerm G n) ]
    change _=(hessian G n (priv i) (priv j):ℂ)+(hessian G n (priv i) (priv j):ℂ); rw [orbit_hessian (priv i)]; unfold hessian; simp only [neg_apply]; push_cast; ring
variable (G n) in
def NsOrbit: Matrix GJ GJ ℂ:= (1/2:ℂ) • ((Λe G n).transpose * Ns G n false * Λe G n)
variable (G n) in
def YsOrbit: Matrix GC GJ ℂ:= (projectC G n)*(Ys G n false)*(Λe G n)
local notation "Λ" => NsOrbit G n
local notation "Ψ" => YsOrbit G n
lemma lift_cancels (X Y:Matrix GJ V ℂ) (h:Lv*X=Lv*Y): X=Y:= by rw [← Matrix.one_mul X,← Matrix.one_mul Y, ← restrictA (G:=G) (n:=n), Matrix.mul_assoc,Matrix.mul_assoc,h]
lemma lifted_N (he: Even n.val): Lv*Λ=N*Lv:= by
    unfold NsOrbit; rw [Matrix.mul_smul,← Matrix.mul_assoc,← Matrix.mul_assoc,equivProjA he,Matrix.add_mul, Full.Υa_comm,Matrix.one_mul,Matrix.add_mul, Matrix.mul_assoc _ ( Ra G n ),equivA he]; module
lemma lifted_Y (he:Even n.val): Ls*Ψ=W*Lv:= by
    unfold YsOrbit; simp_rw [ ← Matrix.mul_assoc ]; rw [Matrix.mul_assoc ( Ls * projectC G n )]; apply insideC; · rw [ ← Matrix.mul_assoc, Υc_comm,Matrix.mul_assoc,equivA he ]
    rw [← Matrix.mul_assoc,constants_y,Matrix.zero_mul]
lemma Y_equi (he:Even n.val): Ls*Ψ*(Lv).transpose=Ys G n true:= by rw [ lifted_Y he,Matrix.mul_assoc,equivProjA he,Matrix.mul_add,Matrix.mul_one,Υc]
lemma N_equi (he:Even n.val): Lv*Λ*(Lv).transpose=Ns G n true:= by rw [ lifted_N he,Matrix.mul_assoc,equivProjA he,Matrix.mul_add,Matrix.mul_one,Υa]
lemma sym_n : (Λ).transpose=Λ:= by unfold NsOrbit; rw [ Matrix.transpose_smul,Matrix.transpose_mul,Matrix.transpose_mul, Ns_sym,Matrix.transpose_transpose, ← Matrix.mul_assoc]
-- orthogonal support
lemma hComm : (Vx * W).transpose=Vx*W:= by
    have hh:= Full.project (G:=G) (n:=n)
    apply_fun Matrix.transpose at hh; rw [ Matrix.transpose_add,Matrix.transpose_mul,H_flip,Ns_sym, Matrix.transpose_sub, Matrix.transpose_one, show (Full.harmonicA G n).transpose=Full.harmonicA G n from ?_, ← harmonicComm ] at hh; -- orientation
    · exact add_left_cancel ( hh.trans (Full.project (G:=G) (n:=n)).symm )
    ext i j:1; unfold harmonicA FiniteDFT.mean; rw [Matrix.transpose_apply]; simp [eq_comm]
lemma fix_proj (he:Even n.val): Lv*(Ξ * Ψ)=Vx * W * Lv:= by rw [ ← Matrix.mul_assoc, ← basis_lift he, Matrix.mul_assoc, lifted_Y he, Matrix.mul_assoc]
lemma ortho (he: Even n.val): (Ξ * Ψ).transpose=Ξ * Ψ:= by
    have hh:= congr_arg ( (Lv).transpose * · ) (fix_proj (G:=G) he); rw [← Matrix.mul_assoc, eigenA he,Matrix.add_mul,Matrix.one_mul] at hh;
    have ht:= congr_arg Matrix.transpose hh; rw [Matrix.transpose_add, Matrix.transpose_mul (Lv).transpose, Matrix.transpose_mul ( Vx * W ), hComm, Matrix.transpose_transpose, Matrix.mul_assoc (Lv).transpose (Vx*W) ] at ht; linear_combination (norm:=module) (1/2:ℂ) • (ht.trans hh.symm)
lemma NX (he:Even n.val): Λ*Ξ=0:= lift_cancels _ _ (by rw [Matrix.mul_zero, ← Matrix.mul_assoc,lifted_N he,Matrix.mul_assoc, ← basis_lift he, ← Matrix.mul_assoc,transvers, Matrix.zero_mul ])
lemma shadowProj (he:Even n.val): Ψ*Ξ=1:= by
    unfold YsOrbit; simp_rw [Matrix.mul_assoc]; rw [ ← basis_lift he, ← Matrix.mul_assoc W,noMeanX,Matrix.sub_mul,no_mean (G:=G) (n:=n ),Matrix.one_mul,sub_zero,leftC]
lemma green_l (he:Even n.val): Λ*He+Ξ*Ψ=1:= by
    apply lift_cancels; rw [ Matrix.mul_add, ← Matrix.mul_assoc _ Λ,lifted_N he, fix_proj he,Matrix.mul_one ]; -- N*Lv*He + X...
    have hu : R*(Vx * W *Lv)=Vx *W * Lv:= by rw [← fix_proj he,← Matrix.mul_assoc,equivA he]
    have hd := Full.project (G:=G) (n:=n); replace hd:= congr_arg ( · * Lv ) hd; rw [ Matrix.sub_mul,harmonic_empty he, Matrix.add_mul,Matrix.one_mul,sub_zero] at hd;
    have hk : R*(N*H*Lv)=N*H*Lv:= by have hh:=congr_arg (R*·) hd; rw [Matrix.mul_add, hu,equivA he] at hh; exact add_right_cancel (hh.trans hd.symm)
    have hc : N*Lv*He=N*H*Lv:= by
       have hm:= basis_h (G:=G) (n:=n); have hy:= congr_arg ((N*Lv)* · ) hm; rw [Matrix.mul_add, ← Matrix.mul_assoc,← Matrix.mul_assoc,Matrix.mul_assoc N Lv, equivProjA he,Matrix.mul_add, Matrix.mul_one,Matrix.add_mul,Matrix.add_mul, ← Υa_comm ] at hy; simp_rw [ Matrix.mul_assoc R ] at hy; rw [ hk ] at hy; linear_combination (norm:=module) (-(1/2:ℂ)) • hy
    rw [hc,hd]
variable (G) in
def landauBasis (he:Even n.val): (SΨ).Fixing:= {
    «N»:=Λ
    Y:=Ψ
    sym i j:= congr_fun (congr_fun sym_n j) i
    green:= green_l he
    ghost:= shadowProj he }
end YM.WilsonBridge.Injections
