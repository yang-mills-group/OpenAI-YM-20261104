import YM.Integration.WilsonMacroscopicRichFixedDecoder
import YM.Next.UV_STRESS.Shell

/-! A fixed, faithful macroscopic physical readout for a signed field on any later cell. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichFixedWatchSale
open Function Filter Set Lattice Wilson Cells Extraction OPE OPE.Cards PhysMS Spec
open RG MergeProof OPE.Orbits RG16 RG16.Literal MergeProof.Accent Next.UVStress
open scoped Classical BigOperators Topology
variable {G:Gauge}{C:Family G}{S:Table C.book}{f:Extraction.Order}

/-- The actual physical grid testers that become uniformly affordable exterior fields. -/
theorem select (F:Spec.Final C f S)(h:ℕ):∃a:ℕ,∃ W:Fin a→Watch C,∃D:(Fin a→ℂ)→L[ℂ] S.Field h,
    ∀y,D (fun i=>(W i).tester S h y)=y:=by
  let test (w:Watch C):=w.tester S h
  obtain ⟨rows,mem,span,_⟩:=Submodule.exists_fun_fin_finrank_span_eq ℂ (range test)
  choose W eq using fun i=>mem i
  let M:=LinearMap.pi rows
  have ker:LinearMap.ker M=⊥:=LinearMap.ker_eq_bot'.mpr fun x hx=>by
    have zero:x∈(Submodule.span ℂ (range rows)).dualCoannihilator:=by
      rw [(by rfl:(x∈_)= (x∈((Submodule.span ℂ (range rows)).dualCoannihilator:Set (S.Field h)))),Submodule.coe_dualCoannihilator_span]
      rintro _ ⟨i,rfl⟩;exact congr_fun hx i
    rw [span] at zero
    apply observes F.room.kernel h
    ext w
    change (test w) x = (test w) 0
    rw [map_zero];exact Submodule.mem_dualCoannihilator _ |>.mp zero _ (Submodule.subset_span (mem_range_self w))
  obtain ⟨D,left⟩:=M.exists_leftInverse_of_injective ker
  refine ⟨_,W,D.toContinuousLinearMap,fun x=>?_⟩
  change D (fun i=>test (W i) x)=x
  simp_rw [eq];exact LinearMap.congr_fun left x

/-- Native small-cell to large-cell transfer for one entire centered signed source, with its
own whole-program subtraction performed before reflection. -/
theorem promote (C:Family G)(k:ℕ):∀ᶠ b:ℕ in atTop,∀N per:ℕ,∀β amt:ℝ,∀A:Config G (C.side N per)→ℂ,
    Seam G (C.side N per) β→PaidAt C.S N per b β amt A→PaidAt C.S N per k β amt A:=by
  have small:=C.S.shrinks.const_mul (9:ℝ)
  rw [mul_zero] at small
  filter_upwards [eventually_ge_atTop k,small.eventually (ge_mem_nhds (C.S.a_pos k))] with b kb width
  intro N p β amt A seam paid
  let kn:=kb.trans paid.live
  let T:=center C.S p kn 0
  let d:=3*Cells.span C.S paid.live p
  have bound:d≤T.side.val/3:=by
    apply (Nat.le_div_iff_mul_le (by decide)).2;apply (Nat.cast_le (α:=ℝ)).1
    apply le_of_mul_le_mul_left _ (C.S.a_pos N)
    rw [show C.S.a N*T.side.val=C.S.a k from C.S.embeds_scale T.units]
    unfold d;push_cast;convert width using 1
    rw [←C.S.embeds_scale (C.S.toDepth paid.live p)];ring
  have seated: (0:Site (C.S.side N p))∈T.margin 0 (T.side.val/3):=by
    have wrapped : wrap (C.S.side k p) (0:Cover) = (0:T.Cell) := by ext t; simp [wrap]; rfl
    have v := Ribbons.buffer C.S k kn p 0
    dsimp only at v
    rw [Next.UVStress.location_origin,wrapped] at v
    exact v
  have smaller:=paid.smaller false 1 rfl (Extraction.Around.inherits (C:=C) kb paid.live) (Lease.fewer T _ bound seated) seam
  rw [Push.RelayDifference.oriented_zero] at smaller
  exact ⟨kn,smaller.1,smaller.2⟩

def heard {a:ℕ}(W:Fin a→Watch C)(w:ℕ×ℕ)(A:Config G (C.side w.1 w.2)→ℂ)(i:Fin a):ℂ:=
  moment (C.beta w.1 w.2) (fun U=>A U*(W i).plot w.1 w.2 U)

/-- Uniformly before the later source cell, all upper fields and numerical charges, the same
finite detector recovers every physical field and tests any later submitted signed cell. -/
theorem original (F:Spec.Final C f S)(h:ℕ):∃a:ℕ,∃W:Fin a→Watch C,∃D:(Fin a→ℂ)→L[ℂ] S.Field h,
    (∀y,D (fun i=>(W i).tester S h y)=y) ∧ ∃k:ℕ,(∀j,(W j).t≤k) ∧ ∃B:ℝ,0≤B ∧ ∀ᶠb:ℕ in atTop,∀ᶠw:ℕ×ℕ in f.fuse,∀A:Config G (C.side w.1 w.2)→ℂ,
      ∀amt:ℝ,PaidAt C.S w.1 w.2 b (C.beta w.1 w.2) amt A→‖D (heard W w A)‖≤‖D‖*B*amt:=by
  obtain ⟨a,W,D,left⟩:=select F h
  let k:=Finset.univ.sup (fun i:Fin a=>(W i).t)
  have fits (i:Fin a):(W i).t≤k:=Finset.le_sup (s:=Finset.univ) (f:=fun j:Fin a=>(W j).t) (Finset.mem_univ i)
  choose K pos sale using fun i:Fin a=>Ribbons.acorns (W i) F.room.cutoff F.room.copies k (fits i)
  let B:=∑i,K i
  have bp:0≤B:=Finset.sum_nonneg (fun i _=>pos i)
  refine ⟨a,W,D,left,k,fits,B,bp,?_⟩
  filter_upwards [promote C k] with b smaller
  filter_upwards [eventually_all.mpr sale] with w tests
  intro A amt paid
  have funded:=smaller w.1 w.2 _ amt A (F.room.copies.all w.1 w.2) paid
  have bound:‖heard W w A‖≤B*amt:=by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg bp paid.cost)).mpr
    intro i
    obtain ⟨_,cash⟩:=tests i
    have hr:‖heard W w A i‖≤amt*K i:=(cash A funded.ticket).trans (mul_le_mul_of_nonneg_right funded.mark (pos i))
    exact hr.trans (by rw [mul_comm];exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun j _=>pos j) (Finset.mem_univ i)) paid.cost)
  exact (D.le_opNorm _).trans ((mul_le_mul_of_nonneg_left bound (norm_nonneg _)).trans_eq (by ring))
end YM.Integration.WilsonMacroscopicRichFixedWatchSale
