import YM.XSpace.Section

/-! A fixed survey measured at a high horizon defines a bona fide lower group section.
The same compact cylinder is read on the original gauge field. Its nonlinear
low-horizon calibration is obtained by testing the high survey on the truncated jet. -/
noncomputable section
set_option maxHeartbeats 900000
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialPublicJointCapSurvey
open Function Filter Set Lattice RG Labels Source Source.Drops Wilson XSpace
open Work.G05 Bid
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{H:Hol G}{lo hi:ℕ}

/-- An already truncated connection is exactly the same path on each lattice link. -/
theorem links (H:Hol G)(le:lo≤hi)(J:Jet G)(v:ℝ):
    H.links hi (expand lo (trunk lo J)) v=H.links lo J v:=by
  classical
  have pot (i:Axis)(x:E4):potential hi (expand lo (trunk lo J)) i x=potential lo J i x:=by
    let f (j:ℕ):=((expand lo (trunk lo J)) j).value i x
    change ∑ j∈Finset.range (hi-1),f j=∑ j∈Finset.range (lo-1),(J j).value i x
    calc
      _ = ∑j∈Finset.range (lo-1),f j:=by
        symm
        apply Finset.sum_subset (Finset.range_mono (Nat.sub_le_sub_right le 1))
        intro j _ out
        have gone:¬j<lo-1:=fun h=>out (Finset.mem_range.mpr h)
        simp [f,expand,gone,Taylor.value,Tensor.diagonal]
      _ = _:=by
        apply Finset.sum_congr rfl
        intro j hj
        simp [f,expand,trunk,Finset.mem_range.mp hj]
  funext l
  have same:partConnection hi (expand lo (trunk lo J)) v l=partConnection lo J v l:=by
    funext t
    simp only [partConnection,pot]
  exact congrFun ((H.solves hi _ v l).unique (show SolvesLink _ _ from by
    rw [same]
    exact H.solves lo J v l)) 1

theorem projects (H:Hol G)(le:lo≤hi)(p:Label G lo)(f:CoverConfig G→ℂ)
    (high:Projects H (raiseLabel G le p) f):Projects H p f:=by
  intro J
  have measured:=high (expand lo (trunk lo J))
  have group:(fun t=> f (H.links hi (expand lo (trunk lo J)) t))=
      (fun t=> f (H.links lo J t)):=funext fun t=>congrArg f (links H le J t)
  have print:(fun t=>read (scaleJet (expand lo (trunk lo J)) t) (raiseLabel G le p).val)=
      (fun t=>read (scaleJet J t) p.val):=by
    funext t
    have phase:scaleJet (expand lo (trunk lo J)) t=expand lo (trunk lo (scaleJet J t)):=by
      funext j
      by_cases h:j<lo-1 <;> simp [scaleJet,expand,trunk,h]
    rw [phase]
    exact racts p (scaleJet J t)
  dsimp only at measured ⊢
  rw [group,print] at measured
  exact ⟨measured.1.of_le (by exact_mod_cast le),measured.2.1.of_le (by exact_mod_cast le),
    fun k hk=>measured.2.2 k (hk.trans le)⟩

theorem original (A:Survey G H hi)(F:Frame G lo)(le:lo≤hi):
    ∃T:SectionData F,T.Sound H ∧ pop T ∧ ∀(p:Label G lo)(U:CoverConfig G),
      T.evaluate (F.coords p) U=read (expand hi (A.reading U)) p.val:=by
  obtain ⟨r,hr⟩:= Work.G06.enclose A.looks
  obtain ⟨Y,hY⟩:= Work.G06.realize G A.looks (box r) hr
  let T : SectionData F:=⟨box r,Y.toLinearMap ∘ₗ A.cyl.toLinearMap ∘ₗ (localFields G lo).subtype ∘ₗ F.coords.symm.toLinearMap⟩
  have he (v : Label G lo) : T.evaluate (F.coords v)=lumin (A.cyl v.val) ∘ mapped A.looks:=by
    funext U
    change MvPolynomial.aeval (entry U) (Y (A.cyl (F.coords.symm (F.coords v)).val))=_
    rw [hY,F.coords.symm_apply_apply]; rfl
  have ht (v : Label G lo) (U : CoverConfig G) : T.evaluate (F.coords v) U = read (expand hi (A.reading U)) v.val:= by rw [he]; exact A.cylinder_at ..
  refine ⟨T,⟨center_box r,box_covariant r,?_,?_,?_,?_,?_⟩,?_,ht⟩
  · intro v; obtain ⟨v,rfl⟩:=F.coords.surjective v; intro t U; rw [ht,ht,Survey.reading_gauge]
    have h (a : G.El) (x : Snap G hi) : expand hi (Cast a x)= colored a (expand hi x):=by funext i; by_cases h:i<hi-1 <;> simp [expand,h,Cast,colored]
    rw [h]; exact v.property.2 ..
  · rw [← F.coords_unit]; funext U; rw [ht]; exact map_one _
  · intro s v x; obtain ⟨v,rfl⟩:= F.coords.surjective v; rw [F.act_coords,ht,ht, A.reading_signed,snap_expand]; exact (eval_changed ..).symm
  · intro v x
    have hv : star v=F.coords (realBar (F.coords.symm v)):= (funext fun i=> F.conj_basis v i).symm
    rw [hv,ht]; nth_rw 2 [show v= F.coords (F.coords.symm v) from (F.coords.apply_symm_apply v).symm]; rw [ht]; exact conj_value ..
  · intro v; obtain ⟨v,rfl⟩:= F.coords.surjective v; rw [he,F.coords.symm_apply_apply]; exact projects H le v _ (A.projects (raiseLabel G le v))
  intro i
  refine ⟨A.size,A.looks,hr,A.cyl (F.basis i).val, F.coords_basis i ▸ he (F.basis i),lows_substitute _ A.coordinate_low _ _ ?_⟩
  intro a ha; have ha':=((pure_grade _ (F.basis i)).mp (F.pure i)) (MvPolynomial.mem_support_iff.mp ha); rw [weight_slot] at ha'; exact congr_arg Prod.snd ha'.symm
end YM.Integration.WilsonPositionProgramTrialPublicJointCapSurvey
