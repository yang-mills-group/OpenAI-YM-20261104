import YM.Spec.Closed
import YM.OS.Schwinger

/-! The complete physical Schwinger correlation across an independently chosen separating plane. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichTwoLengthSlates
open Function Set Lattice Extraction Spec Word OS
open scoped Classical Topology InnerProductSpace
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Spec.Final C f S)

include F

/-- Both diagonal norms are measured in the original reflection-positive Hilbert space. -/
theorem paired (a:Axis)(x y:Future C.book a):
    ‖S.expect (reflect x.val a++y.val)‖≤Real.sqrt ‖S.expect (reflect x.val a++x.val)‖*Real.sqrt ‖S.expect (reflect y.val a++y.val)‖:=by
  let H:Schwinger S a:=(schwinger_ready F.room.kernel).some
  have self (z:Future C.book a): ‖H.plant z‖=Real.sqrt ‖S.gram a z.val z.val‖:=by
    rw [←H.measure z z,inner_self_eq_norm_sq_to_K,norm_pow,RCLike.norm_coe_norm,Real.sqrt_sq (norm_nonneg _)]
  change ‖S.gram a x.val y.val‖≤_
  rw [←H.measure x y];exact (norm_inner_le_norm (𝕜:=ℂ) (H.plant x) (H.plant y)).trans_eq (by rw [self x,self y];rfl)

/-- Both words keep every original label. The reference point of the plane is allowed to depend on their two lengths. -/
theorem original (a:Axis)(c:E4)(x y:C.book.Word)(hx:distinct x)(hy:distinct y)
    (before:∀v∈x,v.1 a<c a)(after:∀v∈y,c a<v.1 a):
    let A:=carry x (-c)
    let B:=carry y (-c)
    ‖S.expect (x++y)‖≤Real.sqrt ‖S.expect (A++reflect A a)‖*Real.sqrt ‖S.expect (reflect B a++B)‖:=by
  intro A B
  have past:Positive (reflect A a) a:=by
    refine ⟨reflects a (still hx _),?_⟩;intro v hv
    rw [reflectedPoint,List.mem_map] at hv
    obtain ⟨t,ht,rfl⟩:=hv;have mem:t∈A:=by simpa using ht
    change t∈x.map _ at mem;obtain ⟨v,pre,rfl⟩:=List.mem_map.mp mem
    simpa using sub_pos.mpr (before v pre)
  have future:Positive B a:=by
    refine ⟨still hy _,?_⟩;intro t ht;change t∈y.map _ at ht
    obtain ⟨v,pre,rfl⟩:=List.mem_map.mp ht
    change 0<v.1 a+ -c a;exact sub_pos.mpr (after v pre)
  have joined:distinct (A++B):=by simpa only [reflect_twice] using twoSides past future
  have shift:S.expect (x++y)=S.expect (A++B):=by
    have eq:=OS.invariance F.room.kernel.translations joined c
    simpa [A,B,OS.distribute,OS.paths,OS.rest] using eq
  rw [shift];simpa only [reflect_twice] using paired F a ⟨reflect A a,past⟩ ⟨B,future⟩

end YM.Integration.WilsonMacroscopicRichTwoLengthSlates
