import YM.Integration.WilsonCenteredAlignedGeometry

/-! A fixed dictionary on the true Wilson leading frame may be compared at
one aligned finite mesh. Distinct residue classes are enforced before the
node comparison. The physical interpolation uses only its true shape jets. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredAlignedPhysical
open Function Filter Set Metric Finset Lattice Spec Extraction Table PhysMS OPE OPE.Orbits
open OPE.Stencils Trace.Pilot WilsonCenteredAlignedGeometry
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge} {C:Family G} {f:Extraction.Order} {S:Table C.book}

theorem original (F:Final C f S) {J:ℝ→tower S} (lead:Leading F J)
    {n:ℕ} {d:Caps n} (v:MaxwellSlots C d) (L:ℕ) (W:Finset E4) {K:Set (Points n)}
    (compact:IsCompact K) (sep:K⊆conf n) :
    ∃ R B A:ℝ,0<R ∧ 0≤B ∧ 1≤A ∧
      IsCompact (cthickening R K) ∧ cthickening R K⊆conf n ∧
      ∀ᶠ r:ℝ in trail,∀ (s:ℕ),let h:=C.S.a s/r
      ‖assemble n‖*(step n W h*((L+1:ℕ)+3))≤R →
      ∀(Z:Points n→ℂ) (Q η:ℝ),0≤Q → 0≤η → ContDiffOn ℝ (L+1) Z (conf n) →
      (∀x∈cthickening R K,‖iteratedFDeriv ℝ (L+1) Z x‖≤Q) →
      (∀ (o:Fin n → Cover) (y:Points n),y∈cthickening R K →
        (∀i,r•y i=C.S.gridPoint s (o i)) → Screen (fun i=>y i) →
        (∀i a,o i a%Cloud.count (Fin n) W=Cloud.residue W h i a) →
        ‖measured F none (J r) v r y-Z y‖≤η) →
      ∀x∈K,‖measured F none (J r) v r x-Z x‖≤A*(η+(B+Q)*h^(L+1)) :=by
  obtain ⟨R,rp,room⟩:=compact.exists_cthickening_subset_open (conf_open n) sep
  have enlarged:IsCompact (cthickening R K):=compact.cthickening
  obtain ⟨B,bp,physics⟩:=WilsonCenteredAlignedPhysicalRegularity.original F lead v (L+1) enlarged room
  obtain ⟨D,dp,tensorprice⟩:=WilsonCenteredAlignedTensor.original (ι:=Coord n) L
  let M:=max 1 (‖assemble n‖*|(Cloud.count (Fin n) W:ℝ)|)
  have m1:1≤M:=le_max_left _ _
  let A:=D*M^(L+1)
  have a1:1≤A:=one_le_mul_of_one_le_of_one_le dp (one_le_pow₀ m1)
  refine ⟨R,B,A,rp,bp,a1,enlarged,room,?_⟩
  filter_upwards [physics,(self_mem_nhdsWithin : ∀ᶠr:ℝ in trail,0<r)] with r physical r0
  have rp:0<r:=r0
  intro s h fits Z Q η qp ep smooth cap actual x hx
  let H:=step n W h
  have hp:0<h:=div_pos (C.S.a_pos s) r0
  have Hp:0<H:=positive n W hp
  let p:=chart x-offset W h
  let Y:=fun t:Coord n→ℝ=>measured F none (J r) v r (shot W h t)-Z (shot W h t)
  have amount:0≤(B+Q)*‖assemble n‖^(L+1):=mul_nonneg (add_nonneg bp qp) (pow_nonneg (norm_nonneg _) _)
  have test (y) (vy:valid (L+1) H (univ:Finset (Coord n)).toList p y) : ‖Y y‖≤η:=by
    have ready:=mem_cthickening_of_dist_le _ x R K hx ((full_tube W hp _ x y vy).trans fits)
    obtain ⟨o,deployed,legal,named⟩:=grid W hp C.S s (show r*h=C.S.a s by dsimp [h];field_simp [rp.ne']) _ p y vy
    exact actual o (shot W h y) ready deployed legal named
  have bill:=tensorprice H η ((B+Q)*‖assemble n‖^(L+1)) Hp ep amount p Y test
  have paid:‖Y p‖≤D*(η+((B+Q)*‖assemble n‖^(L+1))*H^(L+1)):=by
    apply bill
    intro y i hy
    let T:=H*((L+1:ℕ)+3)
    have tp:0<T:=mul_pos Hp (by positivity)
    have path (t) (ht:t∈Icc 0 T):shot W h y+t•unit i∈cthickening R K:=
      mem_cthickening_of_dist_le _ x R K hx ((tube W hp (L+1) x y i hy ht).trans fits)
    obtain ⟨reg,price⟩:=physical (shot W h y) (unit i) T tp path
    have inConf (t) (ht:t∈Icc 0 T):shot W h y+t•unit i∈conf n:=room (path t ht)
    obtain ⟨fit,jet⟩:=WilsonCenteredAlignedPhysicalRegularity.line (conf_open n) (L+1) smooth
      (shot W h y) (unit i) T tp inConf
    let P:=fun t:ℝ=>measured F none (J r) v r (shot W h y+t•unit i)
    let V:=fun t:ℝ=>Z (shot W h y+t•unit i)
    have same:(fun t:ℝ=>Y (update y i (y i+t)))=P-V:=by funext t;dsimp [Y,P,V];rw [line]
    rw [same]
    refine ⟨reg.sub fit,?_⟩
    intro t ht
    rw [iteratedDerivWithin_sub ht (uniqueDiffOn_Icc tp) (reg t ht) (fit t ht)]
    have ybill:‖iteratedDerivWithin (L+1) V (Icc 0 T) t‖≤Q*‖unit i‖^(L+1):=by
      rw [jet t ht]
      let A:=iteratedFDeriv ℝ (L+1) Z (shot W h y+t•unit i)
      have pay:‖A (fun _=>unit i)‖≤‖A‖*‖unit i‖^(L+1):=by simpa using A.le_opNorm (fun _=>unit i)
      exact pay.trans (mul_le_mul_of_nonneg_right (cap _ (path _ ht)) (pow_nonneg (norm_nonneg _) _))
    have localCost:=(norm_sub_le ..).trans (add_le_add (price t ht) ybill)
    rw [←add_mul] at localCost
    exact localCost.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (unit_bound i) _) (add_nonneg bp qp))
  change ‖measured F none (J r) v r (shot W h p)-Z (shot W h p)‖≤_ at paid
  rw [show shot W h p=x from start W h x] at paid
  have card:0<(Cloud.count (Fin n) W:ℝ):=Int.cast_pos.mpr (Cloud.count_pos W)
  have rent:‖assemble n‖*(Cloud.count (Fin n) W:ℝ)≤M:=by simp [M,abs_of_pos card]
  have order:=pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) card.le) rent (L+1)
  have pad:η≤η*M^(L+1):=le_mul_of_one_le_right ep (one_le_pow₀ m1)
  apply paid.trans
  have allowance:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left order (add_nonneg bp qp)) (pow_nonneg hp.le (L+1))
  calc
    _ ≤D*(η*M^(L+1)+((B+Q)*M^(L+1))*h^(L+1)):=by
      apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans dp)
      apply add_le_add pad
      calc
        _=((B+Q)*(‖assemble n‖*(Cloud.count (Fin n) W:ℝ))^(L+1))*h^(L+1):=by
          dsimp [H, WilsonCenteredAlignedGeometry.step]
          simp only [mul_pow]
          ring
        _≤_:=allowance
    _=A*(η+(B+Q)*h^(L+1)):=by dsimp [A];ring

end YM.Integration.WilsonCenteredAlignedPhysical
