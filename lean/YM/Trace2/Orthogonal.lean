import YM.Trace.Revel

/-! Low-weight stress algebra in exactly equivariant frames. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 160000
set_option maxRecDepth 4000
noncomputable section
namespace YM.Trace
open Function Set Filter Table Maxwell Labels Climb Work.A01 Next.UVStress UVNext.FreeStress Spin
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
open scoped Classical
variable {G : Gauge} {C : Family G} {L : Register G} {S : Table L}

def inclineInt : Axis→Axis→ℤ := fun i j=> if i=0 then if j=0 then 3 else if j=1 then -4 else 0 else if i=1 then if j=0 then 4 else if j=1 then 3 else 0 else if i=j then 5 else 0
def inclineMat : M4 := fun i j=> (inclineInt i j:ℝ)/5
lemma incline_cost (i j:Axis) : (∑ k,inclineInt i k * inclineInt j k) = if i=j then 25 else 0:=by revert i j; decide
lemma incline_valid : inclineMat*star inclineMat = 1:=by
   ext i j
   simp [inclineMat,Matrix.mul_apply, Matrix.star_apply, show ∀ a b : ℝ,(a/5)*(b/5)=a*b/25 from by intros;ring,← Finset.sum_div,← Int.cast_sum,← Int.cast_mul, incline_cost, Matrix.one_apply];split <;>simp
@[irreducible] def incline : Ortho:= ⟨inclineMat,Matrix.mem_unitaryGroup_iff.mpr incline_valid⟩
lemma tensor_sub_smul {L:Register G} {S:Table L}(R : S.Rotation) {J V:S.Stress}
    (hJ : Tensorial R J)(hV : Tensorial R V)(t : ℝ) : Tensorial R (J-t • V) := fun p i j=> by
     change R.act 4 p (J i j-t • V i j) = ∑ m:Axis,∑ n:Axis,(↑(p.val m i * p.val n j):ℂ) • (J m n -t • V m n)
     rw [map_sub,RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smul,hV,hJ]
     simp_rw [smul_sub,Finset.smul_sum,Finset.sum_sub_distrib,RCLike.real_smul_eq_coe_smul (K:=ℂ) t]
     congr 1; apply Finset.sum_congr rfl;intro v _;apply Finset.sum_congr rfl;intro k _;exact smul_comm ..
lemma scalar_diagonal {L:Register G} {S:Table L}(R:S.Rotation) {J:S.Stress}
    (ht : Tensorial R J) (hz : J 0 1=0) (hb : J 1 0=0) : J 0 0=J 1 1:=by
    let s:=incline
    have hs:=ht s 0 1; rw [hz,map_zero] at hs
    simp only [s,incline,inclineMat] at hs
    norm_num [Fin.sum_univ_four,hz,hb,inclineInt] at hs -- need symmetry assumption implied by tensor and zero? not if map antisymmetric. include Sym
    have he : (12/25 :ℂ) • J 0 0=(12/25:ℂ) • J 1 1:= by simpa [eq_comm, sub_eq_neg_add, neg_add_eq_iff_eq_add] using hs
    calc J 0 0=((12/25:ℂ)⁻¹) • ((12/25:ℂ) • J 0 0):=by module
         _=((12/25:ℂ)⁻¹) • ((12/25:ℂ) • J 1 1):=congr_arg _ he
         _=J 1 1:=by module

variable {F : Frames G} {W : DiffPlan (freeTable F)} (H : (freeTable F).Hierarchy) (R : (freeTable F).Rotation)
lemma paint_sum_any (a b d : ℝ) : (∑ i : Axis,(UVNext.FreeStress.paintStress F a b d) i i) = (a+2*b) • UVNext.FreeStress.total F := by
   simp only [paintStress,Pi.add_apply,Pi.smul_apply,east,west,splitDiag,across,if_true,smul_zero,add_zero,Finset.sum_add_distrib,
      ← Finset.smul_sum]
   have h (i : Axis) : far F i = total F - (2:ℝ) • near F i := by rw [total_at F i]; rw [RCLike.real_smul_eq_coe_smul (K:=ℂ) (2:ℝ)]; push_cast; abel
   rw [show ∑ x : Axis, near F x = total F by rfl]; simp_rw [h]
   rw [Finset.sum_sub_distrib,Finset.sum_const,← Nat.cast_smul_eq_nsmul ℝ, ← Finset.smul_sum,
       show ∑ x : Axis, near F x = total F by rfl]; norm_num; module
lemma centered_in_stress {J : (freeTable F).Stress}(hR : R.Laws W H.spin) (hJ : Tensorial R J)
       (he : ∀ a b,J a b=J b a)(hv : ∀ a b, (freeTable F).conj H.spin 4 (J a b)=J a b) :
    reCenter (freeTable F) J ∈ KernelSpace H.spin:= enters H _ (sym_mem.mpr ⟨he,hv,fun k i j=> by rw [← hR.signed]; exact hJ ..⟩)

theorem paint_iso {J : KernelSpace H.spin}
    (hp:Tensorial R J.val)(he:∀ i j:Axis,i≠j→J.val i j=0): ∀ i:Axis,J.val i i=J.val 0 0:=by
   have hx := scalar_diagonal R hp (he 0 1 (by decide)) (he 1 0 (by decide))
   intro i; rcases eq_or_ne 0 i with hi|hi; subst i; rfl
   let s : Equiv.Perm Axis:= Equiv.swap 1 i
   have hs:s 0=0:=by simp [s,Equiv.swap_apply_def,hi]
   rw [← show s 1 = i by simp [s], ← perm_tensor F H.spin J s (1:Axis) 1,← hx,perm_tensor F H.spin J s 0 0,hs]

theorem isotropic_value {J : KernelSpace H.spin} (hG:G.Simple)
    (hT : Tensorial R J.val)(hr:∀ i j:Axis,i≠j→ J.val i j=0): ∃ t : ℝ, J.val=splitDiag F (fun _=>t • scalarLabel F) := by
    obtain ⟨a,b,c,hH⟩:= exhaust F H.spin hG (J)
    have he : (4:ℝ) • (J.val 0 0) = (a+2*b) • (4:ℝ) • scalarLabel F := by
       rw [← scalar_actual,← paint_sum_any,← hH]; simp_rw [paint_iso H R hT hr]; norm_num
       module
    refine ⟨a+2*b,?_⟩; funext i j; obtain rfl|hn:=eq_or_ne i j; unfold splitDiag
    · rw [paint_iso H R hT hr,if_pos rfl];calc
         _ = (4:ℝ)⁻¹ • ((4:ℝ) • (J.val 0 0)):= by module
         _ = _ := by rw [he]; module
    · rw [hr i j hn]; unfold splitDiag;rw [if_neg hn]
local notation "M"=>freeTable F
lemma decomposed_stress (hK:R.Laws W H.spin)(ho:R.Oriented M)(hT : Tensorial R (canonicalStress F)) (h : G.Simple)
    {J : (M).Stress} (hJ : Tensorial R J)(hs:∀ i j,J i j=J j i)(hr:∀ i j,(M).conj H.spin 4 (J i j)=J i j) :
      ∃ a d:ℝ, ∃ p:ℂ, ∀ i j, J i j=a • canonicalStress F i j +
         if i=j then d • scalarLabel F + p • (M).unit 4 else 0 := by
    let J' := reCenter M J; have hm:=centered_in_stress H R hK hJ hs hr
    have ht:=stays_tensor H hK ho hJ
    obtain ⟨u,v,a,hU⟩:= exhaust F H.spin h (⟨J',hm⟩:KernelSpace H.spin)
    let V:=J'-a • canonicalStress F
    have hM:V∈KernelSpace H.spin := by unfold V; rw [← lighting F H.spin]; exact (KernelSpace _).sub_mem hm ((KernelSpace _).smul_mem _ (generator F H.spin).property)
    have hV : ∀ i j:Axis,i≠j→ V i j=0:=by
      intro i j hij
      change J' i j - a • canonicalStress F i j=0
      change J'=paintStress _ _ _ _ at hU
      rw [hU]; simp [paintStress,UVNext.FreeStress.across,canonicalStress,east,west,splitDiag,hij]
    obtain ⟨d,hd0⟩:=isotropic_value H R (J:=⟨V,hM⟩) h (tensor_sub_smul R ht hT a) hV
    have hd (i j:Axis): J' i j = a • canonicalStress F i j + if i=j then d • scalarLabel F else 0:=by
      change J' i j= (a • (canonicalStress F i j))+ splitDiag F (fun _ : Axis=>d • scalarLabel F) i j
      rw [← hd0]; change _=a • canonicalStress F i j+(J' i j- a • (canonicalStress F i j)); abel
    have hu : Tensorial R (J-(1:ℝ) • J'):=tensor_sub_smul R hJ ht 1
    let b(i) := expectation M 4 (J i i)
    let σ:=b 0
    have hz (i j:Axis) : (J-J') i j=expectation M 4 (J i j) • (M).unit 4:=by
      change J i j - centering M 4 _= _ ; rw [value_center]; abel
    rw [one_smul] at hu
    have hk : RawTensor H.spin (J-J'):= fun s i j => by rw [← hK.signed]; exact hu ..
    -- expectation is itself a complex tensor invariant all rotations/reflections; use sign flips on tensor difference
    have hv : ∀ i j:Axis,i≠j→(J-J') i j=0:= by
       intro i j hij
       let s:=Signed.mirror i
       have he:=tensor_column hk s i j
       rw [show s.perm i=i from rfl,show s.perm j=j from rfl,hz] at he -- try
       rw [map_smul, (M).mirror_unit, eps_mirror_bit,eps_mirror_bit] at he
       norm_num [bit,hij,Ne.symm hij] at he
       rw [hz]; change expectation M 4 (J i j) • (M).unit 4=0
       let v:=expectation M 4 (J i j) • ((M).unit 4: (M).Field 4)
       change v=-v at he
       calc _ = (2:ℝ)⁻¹ • (v-(-v)) := by unfold v; module
            _ = 0 := by rw [← he,sub_self,smul_zero]
    have hEq := scalar_diagonal R hu (hv _ _ (by decide)) (hv _ _ (by decide))
    have hD (i:Axis) : (J-J') i i=σ • (M).unit 4:=by
      rcases eq_or_ne 0 i with rfl|hi;· exact hz 0 0
      let s:Equiv.Perm Axis:=Equiv.swap 1 i; let t:=UVNext.FreeStress.round s
      have hp: s 0=0:=by simp [s,hi,Equiv.swap_apply_def]
      have hh:= congr_arg ((M).mirror H.spin 4 t) hEq
      simp_rw [tensor_column hk,eps_self] at hh
      change (↑(1:ℝ):ℂ) • (J-J') (s 0) (s 0) = (↑(1:ℝ):ℂ) • (J-J') (s 1) (s 1) at hh
      rw [show s 1=i by simp [s],hp,Complex.ofReal_one,one_smul,one_smul] at hh; rw [← hh,hz]
    refine ⟨a,d,σ,fun i j=> ?_⟩; obtain rfl|hne:= eq_or_ne i j
    · have he:=hD i;change J i i-J' i i= _ at he
      rw [hd] at he;rw [if_pos rfl,← he]; simp;abel
    have he:=hv i j hne; change J i j-J' i j=_ at he; rw [sub_eq_zero.mp he,hd];simp [hne]

end YM.Trace
