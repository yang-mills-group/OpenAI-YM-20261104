import YM.FVA2.BosMoment
import YM.MS.Swirl.Sits

/-!
# Comparing factorial-normalized radial coefficients with MS symbol convention
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Bosonic
open Function Filter Finset Matrix MeasureTheory MS MS.Swirl MS.Book MS.Book.Convolve MS.Koszul
open MS.Puff SplitP Engine Actors Dynamics Mom MS.Cylinder MS.Cylinder.Taylor
open MS.Orbit MS.Orbit.Cog MS.Orbit.LogReal Substitute
open PertExtension.Series PertExtension.Series.Radial
open scoped Topology ContDiff Classical
variable {A E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma iter_one (F : E→ℝ) (h:germ F) (u:E) (n:ℕ) : (ink (fun _:Unit => u) F (List.replicate n ()))=
    ((iteratedFDeriv ℝ n F 0 fun _=>u:ℝ):ℂ) := by
  let L:= ContinuousLinearMap.toSpanSingleton ℝ u
  have he := Taylor.ink_ctrl_one (fun _:Unit=> (1:ℝ)) L h
  have hu : (L ∘ (fun _:Unit=>(1:ℝ)))=(fun _=>u):=funext fun v=> by simp [L]
  rw [hu] at he
  have hs (f:ℝ→ℝ)(n:ℕ) : ink (fun _:Unit=>(1:ℝ)) f (List.replicate n ())=
      ((iteratedDeriv n f 0 : ℝ):ℂ):= by
    induction n generalizing f with
    | zero=> simp
    | succ n IH=> rw [List.replicate_succ,D_eval () (ink _ _),inktip]; rw [show layer 1 f=deriv f from rfl, iteratedDeriv_succ']; exact IH _
  rw [← he, hs]
  have hv:= homogeneous_derivative F u n (h.of_le le_top); unfold jet at hv; congr 1
  exact (mul_left_cancel₀ (by positivity) hv).symm

variable [Fintype A]
lemma value_jet (V : Module.Basis A ℝ E) (F : E →ℝ)(h : germ F)(i:ℕ)(x:E) :
    value (fun i:A=> V.coord i) (mask i (ink V F)) x = (jet F i x : ℂ) := by
  unfold value; rw [ evaluating _ _ (n:=i) (Limit.mod _ _),range_here,
    Finset.sum_eq_single_of_mem i (Finset.mem_range.mpr (by omega)) ]
  · rw [in_rank,enough _ (by simp)]
    let T: Matrix A Unit ℝ:=Matrix.of fun i _=> V.coord i x
    have hv : (fun a:Unit=> ∑ i:A,T i a • V i)=(fun _=>x):=funext fun _=> V.sum_repr x
    change Actors.phase i * ξ[intoC T] _ _= _
    rw [ink_along T V h,hv,iter_one F h]; unfold Actors.phase jet; push_cast; rfl
  intro b hb he; rw [in_rank,strange _ (by simp [he]),mul_zero]

variable (f : A→E)(F : E→ℝ)
local notation "π"=> plain A
local notation "M"=> PermV π
local notation "R"=> rankLevel 0 (ink f F)
local notation "W"=> rankLevel 0 (ink f (Real.exp ∘ F))

omit [Fintype A] in
lemma guarded (F:SpecB A) : F∈(M).guard := fun i _ l hi=> (hi (bosDeg l)).elim
where bosDeg (l:List A) : degree π l=false:=by induction l with| nil=>rfl|cons a l ih=>simp [plain,ih]
omit [Fintype A] in
lemma D_transit (i : A) : Cinch useN (actor π) (promote (D i)) := by
  constructor
  · exact ⟨fun h j hj=> congr_arg (D i) (h j hj)⟩ -- order hv
  · funext j; change D i (useN.refineV (coin 1) j) = (0:Raw A ℂ); unfold SplitP.refineV; split; exact coin_nod ..; exact map_zero _
  · exact fun _=> guarded _
  intro x y; funext j; change D i (pairW (product π) x y j)= (((M).core ((promote (D i)) x) y) j)+ (((M).core x ((promote (D i)) y)) j)
  simp_rw [paired,map_sum,D_product, show π i=false from rfl, sign_id, sum_add_distrib]; rfl

omit [Fintype A] in
lemma rank_zero (hz:F 0=0) : R 0=0 := by
  unfold rankLevel; funext l; rcases l with _|l; simp [mask,hz]
  exact strange _ (by simp; omega)

omit [Fintype A] in
lemma exp_word0 (hz:F 0=0) (n:ℕ) : exp0 π R n [] = if n=0 then 1 else 0 := by
  let G:= R; let L:= M
  have h (i l:ℕ) : L.power G (i+1) l []=0:= by
    unfold Actors.power; change pairW (product π) G _ l []=_
    rw [paired,Finset.sum_apply]; refine Finset.sum_eq_zero fun p _=>?_
    by_cases hs:p.1=0; · rw [hs,show G 0=0 from rank_zero f F hz,map_zero]; rfl
    rw [nil_product]; exact Eq.trans (by unfold G rankLevel; rw [strange _ (by simp; omega)]) (zero_mul _)
  by_cases H:n=0; · subst n; rw [if_pos rfl]; exact congr_fun (Stencil.simple_E _ R _ (rank_zero f F hz)) []
  rw [if_neg H]; unfold exp0 Actors.Cheer Actors.cheers; simp only [Finset.sum_apply]; refine Finset.sum_eq_zero fun i _=> ?_
  cases i
  · rw [firstW]; exact congr_fun (show (M).unit n=0 from if_neg H) _
  rename_i m hm
  unfold wages; rw [Pi.smul_apply,Pi.smul_apply]; exact (congr_arg ((Actors.phase (m+1)) • ·) (h m n)).trans (smul_zero _)

omit [Fintype A] in
lemma eta_exp (hx:F 0=0)(H:germ F): exp0 π R=W := by
  let L:= rankLevel 0 (ink f F); let e:=Real.exp ∘ F
  let X:= rankLevel 0 (ink f e)
  have hh:Happy useN L:= rank_zero f F hx
  have hg : germ e:= Real.contDiff_exp.contDiffAt.comp 0 H
  have ht (i : A) : promote (D i) X= pairW (product π) (promote (D i) L) X := by
    funext k; rw [ paired,promised ]; unfold X L
    simp_rw [promised,mask_conn,inktip ];
    have he : layer (f i) e=ᶠ[𝓝 0] layer (f i) F * e := by
      filter_upwards [H.eventually (by simp)] with x ha; unfold layer; unfold e; rw [fderiv_comp x Real.differentiableAt_exp (ha.differentiableAt (by simp)),ContinuousLinearMap.comp_apply,(Real.hasDerivAt_exp _).hasFDerivAt.fderiv]; rfl
    rw [inkit f he, ink_mul f (p:=π) (fun _ h => Bool.noConfusion h) (germ_layer H _) hg ]; exact (pairLevel (F:=ink f (layer (f i) F)) (H:=ink f e) k (h:=0-1) (g:=0) (p:=π) (fun l hl=>by omega) (fun l hl=>by omega)).symm
  have hy i : promote (D i) (exp0 π R)=pairW (product π) (promote (D i) L) (exp0 π R) :=
    (D_transit i).idea (guarded _) hh
  funext n
  induction n using Nat.strong_induction_on with
  | h n IH=>
    apply ext_D
    · rw [exp_word0 _ _ hx]; by_cases k:n=0
      · subst n; simp [mask,hx,rankLevel]
      rw [if_neg k]; exact (strange _ (by simp; omega)).symm
    intro i
    change promote (D i) (exp0 π R) n = promote (D i) X n
    rw [ht,hy,paired,paired]
    refine Finset.sum_congr rfl fun j hj => ?_
    by_cases hp:j.1=0; · rw [promised,hp,show L 0=0 from hh,map_zero,map_zero]; rfl
    obtain hv:= Finset.mem_antidiagonal.mp hj; rw [IH _ (by omega)]

local notation "σ"=> Trunk

lemma eval_multiply (x:A→ℂ) (F V:SpecB A) (h:Γ F π)(hv:Γ V π) :
    promote (eval x) ((M).core F V)=(σ).core (promote (eval x) F) (promote (eval x) V):= by
  funext j; change eval x (pairW (product π) F V j)= ∑ i∈antidiagonal j, _
  rw [paired,map_sum]; exact Finset.sum_congr rfl fun i _=> prod_eval x _ _ (fee_spec (h i.1 (Set.mem_univ _))).1 (fee_spec (h i.1 (Set.mem_univ _))).2 (fee_spec (hv i.2 (Set.mem_univ _))).2
lemma eval_exp (x:A→ℂ) (F:SpecB A)(h:Γ F π):
    promote (eval x) (exp0 π F)= Actors.Cheer Toy useN (promote (eval x) F) := by
  let U:= promote (eval x)
  have hf : ∀ i,Γ ((M).power F i) π:=by
    intro i; induction i with| zero=> exact refineπ useN (actor π).unit feeUnit| succ k ih=>exact ΤΓ_pair h ih
  have he (i : ℕ) : U ((M).power F i)= (Trunk).power (U F) i := by
    induction i with
    | zero=> funext j; change eval x (useN.refineV _ j)= useN.refineV _ j; unfold refineV; split; exact value_constant _ _; exact map_zero _
    | succ i IH=> rw [power, show U _ = _ from eval_multiply x F _ h (hf i), power]; exact congr_arg _ IH
  funext i; unfold exp0 Actors.Cheer Actors.cheers Actors.wages; rw [promised,Finset.sum_apply,map_sum,Finset.sum_apply]; exact Finset.sum_congr rfl fun j _=> by
    simp only [Pi.smul_apply,map_smul]; exact congr_arg ((Actors.phase j) • ·) (congr_fun (he j) i)
end YM.FVA2.Bosonic
