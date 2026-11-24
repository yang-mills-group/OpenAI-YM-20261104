import YM.WilsonBridge.Projection

/-!
# Concrete tree Fixing with `Orb.saddle` and resolution identities
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBridge.Based.Position
open PertExtension Orb MS Native Bare Koszul Lattice Filter Function Finset
open Cylinder Cylinder.Taylor FreeBV GaussianScore Series Series.Radial
open scoped Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G : Gauge} {n : Side}
local notation "T" => (insertCo G n)
local notation "Γ" => (based (0:E G n))

lemma two_layer {X : Type} [NormedAddCommGroup X][NormedSpace ℝ X]
    {f:X→ℝ}(h:germ f)(u v:X) : layer v (layer u f) 0=fderiv ℝ (fderiv ℝ f) 0 v u:= by
    unfold layer; rw [((h.fderiv_right (m:=ω) (by simp)).differentiableAt (by simp)|>.hasFDerivAt.clm_apply (hasFDerivAt_const u _) |>.fderiv)]; simp
lemma tree_self (x:Dir G n) : score x x=hessian G n (T x) (T x):= by
    let C:Unit→ Dir G n:= fun _=>x; let J:Unit := ()
    let L:= (insertCo G n).toContinuousLinearMap
    let f:= exponent G n
    have hX : fiscal (G:=G) (n:=n)= ((((-1:ℝ) • f)) ∘ L):= by funext i; exact (expense_tree i).symm.trans (by simp; rfl)
    have hq:=congr_fun (ink_ctrl_one C L (show germ ((-1:ℝ) • f) from (expGerm G n).const_smul (-1:ℝ))) [J,J]; rw [← hX,ink_smul _ (expGerm G n)] at hq
    change ((layer x (layer x fiscal) 0:ℝ):ℂ)=((-1:ℝ):ℂ) * (layer (T x) (layer (T x) f) 0:ℝ) at hq
    rw [two_layer fiscal_smooth.contDiffAt,two_layer ( expGerm G n )] at hq
    have he : fderiv ℝ (fderiv ℝ fiscal) 0 x x=hessian G n (T x) (T x):= Complex.ofReal_injective (hq.trans (by push_cast; simp [hessian]))
    rw [← he, second_jet, jet, show (fun _ : Fin 2 => x)=![x,x] by ext i; fin_cases i<;> rfl, iteratedFDeriv_two_apply ]; norm_num [Nat.factorial]; ring
lemma precision_tree (he:Even n.val)(x y:Dir G n): (saddle he).P x y=hessian G n (T x) (T y) := by
    let X:= saddle he (G:=G)
    have ht u: X.P u u=hessian G n (T u) (T u):= tree_self u
    have hz:= ht (x+y); simp_rw [map_add, LinearMap.add_apply, add_apply] at hz
    rw [ht x,ht y,(X.turns y x),orbit_hessian (T y) (T x)] at hz
    change X.P x y=_; linarith
lemma restriction_hessian (he: Even n.val)(v:E G n)(x:Dir G n) : hessian G n (T x) v=(saddle he).P (co G n (v-Γ (Y G he v))) x := by
    rw [precision_tree he,← erase_branch he v, orbit_hessian _ (T x), map_sub,pure_gauge,sub_zero]

variable (he: Even n.val)
local notation "S" => saddle (G:=G) he
def covector (i:Gluon G n): Orb.Source G n:= (projector i).toLinearMap.comp (insertCo G n)
def AAcov (i j:Gluon G n): ℝ:= covector i ((S).inverse (covector j))
lemma inverse_turn {X : Type} [NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X]
    (P:Law X)(u v:Module.Dual ℝ X): u (P.inverse v)=v (P.inverse u):= by
    nth_rw 1 [← P.applies u]; nth_rw 2 [← P.applies v]; exact P.turns .. -- maybe applies rewrite
lemma AAsymm (i j:Gluon G n) : AAcov he i j=AAcov he j i:= inverse_turn _ _ _
lemma N_charges (i j:Gluon G n) :
    ∑ k:Gluon G n, AAcov he i k * costH k j = projector i (priv j- Γ (Y G he (priv j))) := by
    let v:= priv j; let u:= co G n (v-Γ (Y G he v)); let P:= S
    have hp : ∑ k:Gluon G n,costH k j • covector k=P.P u:= by
        apply LinearMap.ext; intro x
        let a:= T x; have hx:= congr_arg (fun f:E G n=> hessian G n v f) (image_charge a); rw [map_sum,orbit_hessian v a] at hx; simp_rw [map_smul] at hx;
        rw [LinearMap.sum_apply]; rw [ ← restriction_hessian he v x, ← hx ]; refine Finset.sum_congr rfl fun k _=> ?_; rw [LinearMap.smul_apply]; change costH k j * projector k a = projector k a * hessian G n _ (priv k); rw [orbit_hessian]; exact mul_comm ..
    have hu: ∑ k:Gluon G n,costH k j • covector i ((P).inverse (covector k))=covector i u:= by rw [← GaussianScore.Law.solves P u,← hp,map_sum,map_sum]; simp_rw [map_smul]
    refine Eq.trans ?_ (hu.trans ?_)
    · exact Finset.sum_congr rfl fun _ _=>mul_comm ..
    change projector i (T u)=_; rw [erase_branch he (priv j)]; -- affects v unfolded?
lemma Y_charges (i j:Gluon G n) : ∑ k:Ghost G n, chargeX i k * projector k (Y G he (priv j)) = projector i (Γ (Y G he (priv j))) := by
    let u:= Y G he (priv j); have hu:= Native.frame u; change _= projector i (Γ u); nth_rw 1 [← hu]; rw [map_sum,map_sum]; simp_rw [map_smul]; exact Finset.sum_congr rfl fun _ _=> mul_comm .. -- arg orientation
lemma X_charges (i j:Ghost G n) : ∑ k:Gluon G n, projector i (Y G he (priv k)) * chargeX k j = if i=j then 1 else 0:= by
    rw [← basis_pr,← show Y G he (generator j 0)= _ from solves_y he (priv j), ← stamp j,map_sum,map_sum]; simp_rw [map_smul]; exact Finset.sum_congr rfl fun _ _=> mul_comm ..

def treeFix (G:Gauge)(he:Even n.val) : (kinetic G n).Fixing where
    N i j:= AAcov he i j
    Y i j:= projector i (Position.Y G he (priv j))
    sym i j:= congr_arg (fun x:ℝ => (x:ℂ)) (AAsymm he i j)
    green := by
        ext i j; have hp:= N_charges he i j
        have hz := Y_charges he i j
        rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]
        change (∑ k:Gluon G n,(AAcov he i k:ℂ)*(costH k j:ℂ))+(∑ k:Ghost G n,(chargeX i k:ℂ)*(projector k (Position.Y G he (priv j)):ℂ))= _
        simp_rw [← Complex.ofReal_mul, ← Complex.ofReal_sum]; rw [hp,hz,map_sub]; push_cast; rw [sub_add_cancel,basis_pr]; by_cases h:i=j<;> simp [h, Matrix.one_apply]
    ghost := by
        ext i j; rw [Matrix.mul_apply]; change (∑ k:Gluon G n,(projector i (Position.Y G he (priv k)):ℂ)*(chargeX k j:ℂ))=(1:Matrix (Ghost G n) _ ℂ) i j; simp_rw [← Complex.ofReal_mul, ← Complex.ofReal_sum, X_charges ]; by_cases h:i=j<;> simp [h, Matrix.one_apply]
end YM.WilsonBridge.Based.Position
