import YM.OPE.Compatible.Lagrange.Density
import YM.Ground.Lean
import Mathlib.LinearAlgebra.Vandermonde
/-!
# finite selection of common test directions (integer stations)
-/
set_option autoImplicit false
noncomputable section
namespace YM.FrameRead
open Function Set Filter Analysis Table Lattice
open scoped Topology InnerProductSpace BigOperators Matrix.Norms.Frobenius
variable {I : Type}[Fintype I]{S :Schedule}
-- strictly positive in EVERY screen projection

def trail (b:ℕ) : E4 := WithLp.toLp 2 fun i:Axis=> ((b:ℝ)+1)^(i.val)
lemma trail_eye (i:ℕ)(a:Axis):0 < trail i a := by unfold trail; rw [WithLp.ofLp_toLp]; positivity
lemma trail_step (j i:ℕ) (k:ℤ): ∃ x,S.gridPoint j x=(S.a j * (k:ℝ)) • trail i:= by
    refine ⟨fun a:Axis=> k*((i:ℤ)+1)^a.val,?_⟩; ext a; simp [Schedule.gridPoint,trail]; ring
structure Sight where
    code : Axis→ℕ
    many : Injective code
lemma sees_across (E:Sight) (x:E4): ∃ b:Axis→ℝ, ∑ i,b i • trail (E.code i)= x:=by
    let f i:=(E.code i:ℝ)+1; let A:= Matrix.vandermonde f; have hu:Injective f:=fun i j hi=> E.many (Nat.cast_injective (R:=ℝ) (add_right_cancel hi))
    obtain ⟨b,h⟩:= (Matrix.vecMul_surjective_iff_isUnit.mpr (show IsUnit A from (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hu)))) x.ofLp
    refine ⟨b,?_⟩; ext a; change (∑ i,b i • trail (E.code i)).ofLp a=x.ofLp a; simp_rw [WithLp.ofLp_sum,Finset.sum_apply]; exact congr_fun h a
-- time axis aligns e

def polar (a:ℕ): Ortho := (OS.Ground.orients (trail a) (trail_eye a timeAxis)).choose
lemma north (a:ℕ): Ortho.move (polar a) (trail a) = ‖trail a‖ • YM.basis timeAxis:= (OS.Ground.orients _ (trail_eye a timeAxis)).choose_spec.1
-- separate inner by actual projection

def shade (a:ℕ)(x:E4):ℝ:= time (Ortho.move (polar a) x)
lemma dodges (x:E4)(hx:x≠0) : ∀ᶠ i:ℕ in atTop, shade i x ≠0 :=by
    by_contra! hh
    obtain ⟨u,hu,hp⟩:= extraction_of_frequently_atTop (show ∃ᶠ i in atTop, shade i x=0 by simpa only [Filter.Frequently,not_not] using! hh)
    let v:Sight:= ⟨fun i=>u i, hu.injective.comp Fin.val_injective⟩; obtain ⟨b,hb⟩:= sees_across v x
    have he(i): inner ℝ (trail (u i)) x=0:=by
       rw [← LinearIsometryEquiv.inner_map_map (Ortho.motion (polar (u i)))]; simp_rw [Ortho.motion_at,north,real_inner_smul_left,basis_inner]; change _*shade (u i) x=_; rw [hp i,mul_zero]
    apply hx; apply (inner_self_eq_zero (𝕜:=ℝ)).mp; nth_rw 1 [← hb]; simp_rw [sum_inner,real_inner_smul_left]; change ∑ i:Axis,b i*inner ℝ (trail (u i)) x=0; simp_rw [he]; simp
-- open cover on test I
lemma menu (I:Type)[Fintype I] : ∃ S : Finset Sight, ∃ c:ℝ, 0<c ∧ ∀ y:I→E4,(∀ i,y i≠0)→ ∃ K∈S,∀ i j,c*‖y i‖≤|shade (K.code j) (y i)| :=by
    classical
    let B:= Metric.sphere (0:E4) 1
    let T : Type := I→ B
    haveI : CompactSpace B := isCompact_iff_compactSpace.mp (isCompact_sphere ..)
    have hx (t:T):∃ a:Sight, ∃ b:ℝ,0<b∧∀ i k,b < |shade (a.code k) (t i)| :=by
       have hh (i) : (t i: E4)≠0:=by
           have hp:= show ‖(t i: E4)‖=1 by simp [B]
           exact norm_ne_zero_iff.mp (hp.symm ▸ one_ne_zero)
       have hv := eventually_all.mpr fun i=> dodges _ (hh i); obtain ⟨u,hu,hv⟩:= extraction_of_eventually_atTop hv
       let a:Sight:=⟨fun i=> u i, hu.injective.comp Fin.val_injective⟩; have he : ∀ᶠ b:ℝ in 𝓝 0, ∀ i k,b < |shade (a.code k) (t i)| := eventually_all.mpr fun i=> eventually_all.mpr fun k=> gt_mem_nhds (abs_pos.mpr (hv k i))
       exact ⟨a,(((show ∀ᶠ t:ℝ in 𝓝[>] 0,0<t from self_mem_nhdsWithin).and (he.filter_mono nhdsWithin_le_nhds)).exists)⟩
    choose a c hc he using hx
    let U(t:T):Set T:= ⋂ i:I, ⋂ j:Axis, {x:T | c t < |shade ((a t).code j) (x i)|}
    have hh(t:T): IsOpen (U t) := isOpen_iInter_of_finite fun i=> isOpen_iInter_of_finite fun j=> isOpen_lt continuous_const (show Continuous (fun x:T=> |shade ((a t).code j) (x i)|) from by
       unfold shade; have ht : Continuous (Ortho.move (polar ((a t).code j))) := (Ortho.motion _).continuous; fun_prop)
    obtain ⟨s,hs⟩:= isCompact_univ.elim_finite_subcover U hh (fun t _=> mem_iUnion.mpr ⟨t,mem_iInter.mpr fun i=> mem_iInter.mpr fun j=> he t i j⟩)
    obtain ⟨d,hd,hD⟩:= ((show ∀ᶠ i:ℝ in 𝓝[>]0,0 < i from self_mem_nhdsWithin).and (((eventually_all_finset s).mpr fun i _=> ge_mem_nhds (hc i)).filter_mono nhdsWithin_le_nhds)).exists
    refine ⟨s.image a,d,hd,fun y hy=>?_⟩; have hH i : 0 < ‖y i‖:= norm_pos_iff.mpr (hy i)
    let u:T := fun i=> ⟨(‖y i‖)⁻¹ • y i,by simp [B,norm_smul,hy]⟩
    obtain ⟨t,ht,hv⟩:= mem_iUnion₂.mp (hs (mem_univ u)); refine ⟨a t,Finset.mem_image_of_mem _ ht,fun i j=>?_⟩; have hz : d ≤ |shade ((a t).code j) (u i)| := (hD t ht).trans (le_of_lt (mem_iInter.mp (mem_iInter.mp hv i) j))
    let R:=polar ((a t).code j); change d≤|time (Ortho.motion R ((‖y i‖)⁻¹ • y i))| at hz; rw [map_smul] at hz; change d≤|‖y i‖⁻¹ * shade ((a t).code j) (y i)| at hz
    rwa [abs_mul,abs_of_pos (inv_pos.mpr (hH i)), ← div_eq_inv_mul,le_div_iff₀ (hH i)] at hz
end YM.FrameRead
