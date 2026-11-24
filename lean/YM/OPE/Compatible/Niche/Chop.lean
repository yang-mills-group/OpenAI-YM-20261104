import YM.OPE.Compatible.Lake.Frame
/-! # Obtaining calibrated sensor support and push on each slot with the true common clock. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Owl
open Function Filter MeasureTheory Spec Lattice RG Wilson Source Cov Allot MergeProof Next.Extract Dash Analysis Extra.Histories Next.Rank
open scoped Topology BigOperators Classical
variable {d k m N p:ℕ}{Y:Side}{G:Gauge}{C:Family G}(T:C.Makes)
local notation "A"=>C.path.levels
local notation "X"=>C.label d
local notation "X0"=>C.labels.level d
variable (hp:C.ref d ≤ m)(hy:m ≤ N)
include hp T hy
open Lake Next.Rank.Price
lemma tenorX : Bijective (tallyman T d m (N,p)):= by
        let f:= tallyman T d m (N,p); have h:Injective f :=by
            change Injective f.toLinearMap; refine LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr ?_); intro x hy'
            have hx: Price.columns C d m N p x=0:= (tallyCurrent T x hp hy).symm.trans hy'; have hv:= at_current C T hp hy p x; rw [hx] at hv; exact Work.G08.size_separates _ _ (by simpa only[Labels.Frame.coeffSize,Pi.zero_apply,norm_zero,Finset.sum_const_zero,mul_zero] using hv)
        exact ⟨h,LinearMap.injective_iff_surjective.mp (show Injective f.toLinearMap from h)⟩
def Pinwheel (p:ℕ): X≃L[ℂ]X:= (LinearEquiv.ofBijective (tallyman T d m (N,p)).toLinearMap (tenorX T hp hy)).toContinuousLinearEquiv
lemma tic (x:X): Pinwheel T hp hy p x=Price.columns C d m N p x:=tallyCurrent T x hp hy
noncomputable def Lot (p:ℕ)(x:C.label d):= (C.factory d N p).terminal.symm ((Pinwheel T hp hy p).symm x)
local notation "λv"=>Lot T hp hy p
lemma lire (x:X) : ((C.factory d N p).entries m (λv x)).x=x:= (tic (p:=p) T hp hy ((Pinwheel T hp hy p).symm x)).symm.trans (ContinuousLinearEquiv.apply_symm_apply _ _)
-- κ up_π.T.For any length >=n
omit hy
variable (hm:m<N)

def OarX (p:ℕ): X≃L[ℂ] X:= (Pinwheel T (hp.trans (Nat.le_succ m)) hm p).symm.trans (Pinwheel T hp hm.le p)
private lemma secret (x:X): Lot T hp hm.le p (OarX T hp hm p x)= Lot T (hp.trans (Nat.le_succ m)) hm p x:=by unfold Lot OarX; rw [ContinuousLinearEquiv.trans_apply,ContinuousLinearEquiv.symm_apply_apply]
abbrev Stepm (p:ℕ)(v:X):= (C.factory d N p).entries m (Lot T hp hy p v) -- hy not included
include hm
lemma pools (x:X): (Stepm T hp hm.le p (OarX T hp hm p x)).density 0 (C.localSection d) (C.path.rep N p m)= ((C.S.block m).val:ℝ)^d • ((A).clock.op m p).push (C.path.rep N p (m+1)).beta ((Stepm T (hp.trans (Nat.le_succ m)) hm p x).density 0 (C.localSection d) (C.path.rep N p (m+1))):=by
        unfold Stepm; rw [secret,(T.calibrated d N p (hp.trans hm.le)).unnormalized m hp hm]; ext w; rw [Pi.smul_apply,Pi.smul_apply,←Complex.coe_smul]; norm_cast -- syntax fix
noncomputable def YieldP {i:ℕ} (V:Labels.Frame G i)(x:Side)(Z:Stage):ℝ:= Z.columns*((x.val:ℝ)^i)*Fintype.card V.Index
noncomputable def Earnest {i:ℕ}(V:Labels.Frame G i)(Z:Stage):ℝ:= Z.columns * Fintype.card V.Index
set_option quotPrecheck false
local notation "scope"=>(A).params (m+1)
lemma Singer : ‖(OarX T hp hm p).toContinuousLinearMap‖≤ YieldP (X0) (C.S.block m) (scope):=by
        let P:= OarX T hp hm p; let v:= (scope).columns*((C.S.block m).val:ℝ)^d; have ht:(scope).columns≥0:=le_trans zero_le_one (((A).params (m+1)).columns_ge)
        have hh:0≤v:= mul_nonneg ht (by positivity)
        apply ContinuousLinearMap.opNorm_le_bound; exact mul_nonneg hh (Nat.cast_nonneg _)
        intro x; let Y:=P x; have he := (T.calibrated d N p (hp.trans hm.le)).front m hp hm (Lot T hp hm.le p Y); rw [lire T hp hm.le (p:=p), show Lot T hp hm.le p Y=_ from secret T hp hm x, lire] at he; exact (Size.norm_le (X0) Y).trans (he.trans ((mul_le_mul_of_nonneg_left (Size.le_norm (X0) x) hh).trans_eq (mul_assoc ..|>.symm)))
lemma Sentry : ‖(OarX T hp hm p).symm.toContinuousLinearMap‖≤Earnest (X0) (scope):=by
        let P:= OarX T hp hm p; have ht:0 ≤ (scope).columns:= le_trans zero_le_one ((A).params (m+1)).columns_ge; apply ContinuousLinearMap.opNorm_le_bound; exact mul_nonneg ht (Nat.cast_nonneg _)
        intro x; let Y:=P.symm x; have he := (T.calibrated d N p (hp.trans hm.le)).back m hp hm (Lot T (hp.trans (Nat.le_succ m)) hm p Y); rw [lire,←secret T hp hm Y (p:=p),lire,show OarX T hp hm p Y=x from ContinuousLinearEquiv.apply_symm_apply ..] at he; exact (Size.norm_le (X0) Y).trans (he.trans ((mul_le_mul_of_nonneg_left (Size.le_norm (X0) x) ht).trans_eq (mul_assoc ..|>.symm)))
end YM.OPE.Owl
