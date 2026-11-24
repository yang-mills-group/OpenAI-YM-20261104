import YM.Analysis.SmoothJets
import YM.RG.Patch
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Topology.ContinuousMap.ContinuousMapZero

/-!
# Test currency for a uniform one-root column
D derivatives on the closed unit cube ([-1/2,1/2]^4 in *this* root's native units).
Doesn't ask for extra derivatives after one step. Coordinate sup (new Wick-coefficient
budget; consumed over arbitrary Smooth profiles; not an actual marker budget).
Kernels may use elements of the dual. In the next file produce them as honest
finite measures. Sup on axis coordinates, use repetitions, NO divided iterated derivatives.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Embroider
open Filter Function Set Lattice RG
open scoped Topology BigOperators ContDiff
abbrev E := Four ℝ
variable {D d:ℕ} {P:Patch}
abbrev Doll:= Metric.closedBall (0:E) (2:ℝ)⁻¹
abbrev Chamber:= ↥Doll
instance :CompactSpace Chamber:= isCompact_iff_compactSpace.mp (ProperSpace.isCompact_closedBall _ _)
def zeroC : Chamber:= ⟨0,Metric.mem_closedBall_self (by norm_num)⟩
instance :Nonempty Chamber:= ⟨zeroC⟩
lemma c_norm (x:Chamber): ‖(x:E)‖ ≤ (2:ℝ)⁻¹:= by rw [←dist_zero_right]; exact x.property
-- allow smooth (C^D, incl boundary data from extension)
def Molli (D:ℕ): Submodule ℝ (E→ℝ) where
   carrier:= {f|ContDiff ℝ (↑D) f}
   add_mem':= by
      intro f g h t; exact ContDiff.add (show ContDiff ℝ (↑D) f from h) (show ContDiff ℝ (↑D) g from t)
   zero_mem':= (show ContDiff ℝ (↑D) (fun _ : E=> (0:ℝ)) from contDiff_const)
   smul_mem':= fun c f h=> (show ContDiff ℝ (↑D) (fun x=> c • f x) from ContDiff.const_smul _ (show ContDiff ℝ (↑D) f from h))
abbrev Scroll D:=↥(Molli D)
lemma scribble (f:Scroll D) {i:ℕ}(hi:i ≤ D): ContDiff ℝ (↑i) f.val:= ContDiff.of_le (show ContDiff ℝ (↑D) f.val from f.property) (Nat.cast_le.mpr hi)
def dot (i: Axis):E:= Pi.single i 1
abbrev Knob (D:ℕ):= (d:Fin (D+1)) × (Fin d.val→Axis)
def crease (p:Scroll D)(v:Fin d→Axis)(x:E):= iteratedFDeriv ℝ d p.val x (dot ∘ v)
private def inkα (p:Scroll D)(i:Knob D): ContinuousMap Chamber ℝ:= ⟨fun x=>crease p i.2 x.val,continuous_iff_continuousAt.mpr fun x=> (Analysis.iterD (x:=x.val) (scribble p (Nat.le_of_lt_succ i.1.isLt)).contDiffAt _).comp continuous_subtype_val.continuousAt⟩

abbrev Sleeves (D:ℕ):= Knob D→ ContinuousMap Chamber ℝ

def write (D): Scroll D →ₗ[ℝ] Sleeves D where
   toFun:= inkα
   map_add' x y:= by
      ext1 i; ext v; exact Eq.trans (DFunLike.congr_fun (iteratedFDeriv_add_apply (x:=v.val) (scribble x (Nat.le_of_lt_succ i.1.isLt)).contDiffAt (scribble y (Nat.le_of_lt_succ i.1.isLt)).contDiffAt) _) (add_apply ..)
   map_smul' c x := by
      ext1 i; ext v; exact Eq.trans (DFunLike.congr_fun (iteratedFDeriv_const_smul_apply (a:=c) (x:=v.val) (scribble x (Nat.le_of_lt_succ i.1.isLt)).contDiffAt) _) (smul_apply ..)

def book (D):= LinearMap.range (write D)
abbrev Volume D:= ↥(LinearMap.range (write D))
scoped instance (D:ℕ) : NormedAddCommGroup (Volume D):=inferInstance
scoped instance (D:ℕ) : NormedSpace ℝ (Volume D):=inferInstance
def page (D) : Scroll D→ₗ[ℝ] Volume D := (write D).rangeRestrict
lemma submitted (p:Volume D):∃ f:Scroll D, page D f=p:= LinearMap.surjective_rangeRestrict _ p
@[simp] lemma submission (p:Scroll D): (page D p).val=write D p:=rfl
lemma draft (p:Scroll D)(i:Knob D)(v:Chamber): (write D p i) v=crease p i.2 v.val:=rfl
lemma registry (p:Volume D)(i:Knob D)(v:Chamber) : ‖p.val i v‖≤‖p‖:= (ContinuousMap.norm_coe_le_norm (p.val i) _).trans (norm_le_pi_norm (p.val) _)
lemma vote_cap (p:Volume D) {M:ℝ}(h:0≤M)(v:∀ i:Knob D,∀ v:Chamber,‖p.val i v‖≤ M): ‖p‖≤M:= by
    change ‖p.val‖ ≤ M; exact (pi_norm_le_iff_of_nonneg h).mpr fun i=> (ContinuousMap.norm_le _ h).mpr (v i)
lemma creased (f:Scroll D){i:ℕ}(hi:i≤ D)(w:Fin i → Axis)(v:Chamber): ‖crease f w v.val‖≤‖page D f‖:= registry (page _ f) ⟨⟨i,by omega⟩,w⟩ v
lemma pledge (f:Scroll D){M:ℝ}(h:0≤M)(hf:∀ i, i≤ D → ∀ w:Fin i→Axis, ∀ v:Chamber,‖crease f w v.val‖≤ M): ‖page _ f‖≤ M:= vote_cap _ h (fun j v=> hf j.1 (Nat.le_of_lt_succ j.1.isLt) j.2 v)

abbrev Vote (D:ℕ) := Volume D→L[ℝ] ℝ

-- (sum_count * stencil) coordinates
variable (P)

def speck:= (P.L.val:ℝ)⁻¹
lemma speck_pos: 0 < speck P:= by unfold speck; positivity
lemma speck_le: speck P ≤ 1:= inv_le_one_of_one_le₀ (by exact_mod_cast (show 1 ≤ P.L.val from P.L.property))

def offset (k:Site P.L):E:= speck P • fun i:Axis=> ((lift k i:ℤ):ℝ)
def tucks (k:Site P.L)(w:E):= offset P k + speck P • w
lemma tucks_enter (k:Site P.L)(w:Chamber): tucks P k w.val∈Doll:=by
   rw [Metric.mem_closedBall,dist_zero_right]
   apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr; intro i
   have hx := (norm_le_pi_norm w.val i).trans (c_norm w)
   obtain ⟨hp,hq⟩:= lift_centers k i
   have hg : 2 * lift k i ≤ (P.L.val:ℤ)-1:=by obtain ⟨a,ha⟩:= P.odd_side; omega
   have hu :1-(P.L.val:ℤ) ≤ 2 * lift k i:=by omega
   have hl:=P.L.property
   rw [Real.norm_eq_abs,abs_le] at hx ⊢
   let y:= ((lift k i :ℤ):ℝ)
   have hk:2*y ≤ (P.L.val:ℝ)-1:=by unfold y; exact_mod_cast hg
   have hn:1-(P.L.val:ℝ) ≤ 2*y:=by unfold y; exact_mod_cast hu
   let L:ℝ:=P.L.val
   have hw: tucks P k w.val i= (y+w.val i)/L := by unfold tucks offset; simp only [speck,Pi.add_apply,Pi.smul_apply, smul_eq_mul]; unfold L y; ring
   have h : L>0:= by unfold L; positivity
   rw [hw]; constructor
   · apply (le_div_iff₀ h).mpr; dsimp [L]; linarith [hx.1]
   apply (div_le_iff₀ h).mpr; dsimp [L]; linarith [hx.2]

def growWord (k:Site P.L) (D) :Scroll D →ₗ[ℝ] Scroll D where
   toFun f:= ⟨fun w=> f.val (tucks P k w), by
       change ContDiff ℝ (↑D) (f.val ∘ tucks P k); unfold tucks; apply (scribble f le_rfl).comp; fun_prop⟩
   map_add' _ _:= rfl
   map_smul' _ _:= rfl

lemma narrow (k:Site P.L)(f:Scroll D)(v:Fin d→Axis)(hi:d≤D)(x:E): crease (growWord P k D f) v x = speck P^d* crease f v (tucks P k x):=by
    let b (x:E):= f.val (offset P k+x); let t : E →L[ℝ] E:= speck P • ContinuousLinearMap.id ℝ E
    have he : ContDiff ℝ (↑D) b:= (scribble f le_rfl).comp (contDiff_const.add contDiff_id)
    change iteratedFDeriv ℝ d (b ∘ t) x _= _
    rw [ContinuousLinearMap.iteratedFDeriv_comp_right _ he _ (Nat.cast_le.mpr hi),ContinuousMultilinearMap.compContinuousLinearMap_apply]
    change iteratedFDeriv ℝ d b _ (fun i:Fin d=> speck P • ((dot∘v) i))= _
    rw [(iteratedFDeriv ℝ d b _).map_smul_univ (fun _=>speck P) (dot ∘ v),show iteratedFDeriv ℝ d b (t x)=_ from iteratedFDeriv_comp_add_left d (offset P k) _]; simp; left; rfl
lemma gain_page (k:Site P.L)(f:Scroll D): ‖page _ (growWord P k D f)‖≤ ‖page _ f‖:=by
    apply pledge _ (norm_nonneg _); intro i hi v w
    rw [narrow _ _ _ _ hi,norm_mul, norm_pow, Real.norm_eq_abs, abs_of_pos (speck_pos _)]
    apply le_trans (mul_le_mul_of_nonneg_right (pow_le_one₀ (speck_pos P).le (speck_le P)) (norm_nonneg _)); rw [one_mul]; exact creased f hi _ ⟨_, tucks_enter ..⟩

omit P in
lemma factoring {F U X:Type}[AddCommGroup F][Module ℝ F][NormedAddCommGroup U][NormedSpace ℝ U][NormedAddCommGroup X][NormedSpace ℝ X](A:F→ₗ[ℝ]U)(B:F→ₗ[ℝ]X)(h:Surjective A)(C:ℝ)(he:0≤ C)(hf:∀ f,‖B f‖≤C * ‖A f‖): ∃ D:U→L[ℝ]X, (∀ f,D (A f)= B f) ∧ ‖D‖≤ C:=by
    choose g hg using h
    have hr a b (h:A a=A b): B a=B b:=by
       apply sub_eq_zero.mp; rw [←map_sub]; apply norm_le_zero_iff.mp; exact (hf _).trans_eq (by rw [map_sub,h,sub_self,norm_zero,mul_zero])
    let f: U→ₗ[ℝ] X:={
       toFun:= fun x=>B (g x)
       map_add':=fun x y=> (hr (g (x+y)) (g x+g y) (by rw [map_add,hg,hg,hg])).trans (map_add ..)
       map_smul':=fun c x=> (hr (g (c • x)) (c • g x) (by rw [map_smul,hg,hg])).trans (map_smul ..)}
    have ht (x:U): ‖f x‖≤C*‖x‖ := (hf (g x)).trans_eq (by rw [hg])
    exact ⟨f.mkContinuous C ht,fun v=>hr _ _ (hg (A v)),LinearMap.mkContinuous_norm_le _ he _⟩

lemma padWord (k:Site P.L)(D): ∃ V:Volume D→L[ℝ]Volume D,(∀ f:Scroll D,V (page D f)=page D (growWord P k D f)) ∧ ‖V‖ ≤ 1:= factoring (page D) (LinearMap.comp (page D) (growWord P k D)) (submitted (D:=D)) _ zero_le_one (fun f=> by rw [one_mul]; exact gain_page ..)

def foldWord (k:Site P.L)(D): Volume D→L[ℝ]Volume D:= (padWord P k D).choose
lemma observed (k:Site P.L)(p:Scroll D): foldWord P k D (page D p)=page D (growWord P k D p):=(padWord ..).choose_spec.1 p
lemma fold_bound (k:Site P.L)(D): ‖foldWord P k D‖ ≤ 1:=(padWord ..).choose_spec.2
end YM.WilsonCoeffUV.Embroider
