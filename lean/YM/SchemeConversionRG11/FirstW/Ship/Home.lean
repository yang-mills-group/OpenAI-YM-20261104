import YM.SchemeConversionRG11.FirstW.Ship.Amend
/-! Self linear arrivals with auxiliary Wick offset retained, power to all finite demands. Ordinary even-period branch. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.FirstW
open Function Filter MeasureTheory Set Metric Lattice Pert Align Topology Maxwell
open scoped BigOperators Classical Matrix
variable {G : Gauge} {n : Side} {T : Itinerary}
-- local native functionals read small or tipped marks.
lemma letter_glide {o : StepPath T} {A : Sight T G} (hA : Tip T o A) (a : Labels.Key G) : Fleck T (fun i=>native a (o i) (A i)) := by
  simp_rw [letter_exact,LinearMap.sum_apply,LinearMap.smul_apply]
  have hv {j:ℕ}(t:Atom j) (u:G.Color) : Fleck T (fun i=> eman (o i) t u (A i)) := by simp_rw [eman,LinearMap.sum_apply,LinearMap.smul_apply]; apply Fleck.collect; intro k _; exact Fleck.const ((hA (t.offset k) t.rotated).push (innerSL ℝ u)) _
  apply Fleck.collect; intro s _; apply Fleck.collect; intro v _; refine Fleck.const (t:=billed s a.snd v) ?_
  simp_rw [LinearMap.sub_apply,sub_eq_add_neg]; exact Fleck.roll (hv _ _) (Fleck.minus (hv _ _))
lemma short_self (a b : Labels.Key G) (x : StepPath T) : ∃ p:ℝ,Fleck T (fun i=> native a (x i) (canal b (x i))-p) := by
  -- finite combination of linGreen at fixed offsets via stamped derivatives. any scalar has power-price at each offset.
  have hh (p : Cover) (D : List Axis) : Fleck T (fun i=> combine D (linGreen (T.period i)) (wrap (T.period i) p) - combine D Cellular.coverLine p) := by
    induction D generalizing p with
    | nil=>
      intro k; have he:= Cellular.strike_two T.period T.gap T.positive T.even_at T.huge T.cutoff k p
      simp only [zpow_neg,zpow_natCast] at he; exact he.congr fun i=>mul_comm .. -- might not elaborate
    | cons j D ih=>
      have he := Fleck.roll (ih (p+step j)) (Fleck.minus (ih p))
      simp_rw [combine,up]; convert! he using 1; ext i; simp only [map_add,wrap_step]; abel
  let Q := fun i:ℕ=>canal b (x i)
  let Y (w : Cover) (k:Axis) := ∑ p:QuotSpot b, combine (rivDir b p) Cellular.coverLine (w+footA b p) • header b p k
  have hv w k : Fleck T (fun i=> Q i (plume T x w i k)-Y w k) := by
    simp_rw [Q,Y,plume, repr_river, add_sub_cancel_left,←Finset.sum_sub_distrib,← sub_smul, ← map_add]; refine Fleck.collect fun p _=>?_; let he := (ContinuousLinearMap.id ℝ ℝ).smulRight (header b p k); exact Fleck.push (hh _ (rivDir b p)) he
  let V(k : Atom a.1) (u:G.Color):= ∑ p:Atom.Kind a.1,k.degree p * inner ℝ u (Y (k.offset p) k.rotated)
  have hz (k : Atom a.1) (u:G.Color) : Fleck T (fun i=> eman (x i) k u (Q i)- V k u) := by
    simp_rw [eman,V,LinearMap.sum_apply, LinearMap.smul_apply,pinch_eq, smul_eq_mul,←Finset.sum_sub_distrib,←mul_sub, ←inner_sub_right]; refine Fleck.collect fun j _=>?_ ; exact Fleck.const ((hv (k.offset j) k.rotated).push (innerSL ℝ u)) _
  let p:= ∑ s : Signed,∑ k:Spot G a.1,billed s a.2 k*(V (k.atom s) (unitColor G k.color)- V (Align.swap (k.atom s)) (unitColor G k.color))
  refine ⟨p,?_⟩; simp_rw [p,letter_exact,LinearMap.sum_apply,LinearMap.smul_apply, LinearMap.sub_apply, smul_eq_mul,←Finset.sum_sub_distrib, ← mul_sub]; refine Fleck.collect fun s _=> Fleck.collect fun k _=>?_ ; refine Fleck.const (t:=billed s a.snd k) ?_; convert! Fleck.roll (hz (k.atom s) (unitColor G k.color)) (Fleck.minus (hz (Align.swap (k.atom s)) (unitColor G k.color))) using 1; funext i;dsimp only [Q];abel
lemma liftLink (a b : Labels.Key G) (h : ℝ) : Full.link h a b = (h^(mass a+mass b))⁻¹*Full.link 1 a b := by
  have he a c p: Full.leg h a c p=(h^mass (G:=G) a)⁻¹*Full.leg 1 a c p := by change tape a h (0:Cover) (Full.material c p)=_; rw [tape_scales]; rfl
  have hp p : Full.spectral h a b p=(h^(mass a+mass b))⁻¹*Full.spectral 1 a b p := by
    unfold Full.spectral; rw [mul_left_comm ( (h^(mass a+mass b))⁻¹)]; simp_rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro c _; simp_rw [he,pow_add, mul_inv];ring
  simp only [Full.link,hp,integral_const_mul]; ring
variable {r d : ℕ}
lemma aura_eq (a b : Labels.Key G) (x y : Site n) (h : ℝ): kField h x a ⬝ᵥ (Orb.covarianceM G n *ᵥ kField h y b) = tape b h y (river h a x+reflectT G n (river h a x)) := by
  simp only [kField,←tape_again,dot_inverse,pinch_potential,gauged]
lemma self_fleck (b c : Labels.Key G) (x : ∀ i, Full.Grid (T.period i) r) (v : Points r) (hv : v∈conf r) (hx : ∀ j, Home T (fun i=>x i j) (v j)) (hr : ∀ i,4∣(T.period i).val) (j : Fin r): Fleck T (fun i=> corrected (T.gap i) (x i) j j b c) := by
  let o i := x i j
  obtain ⟨D,H⟩:=short_self c b o; let F i:= tbranch G (T.period i) (native b (o i))
  have hb (i): F i=canal b (o i) := rfl
  have hp :=remote_from hr o o (hx j) (hx j)
  have H1 := letter_glide (A:=fun i=> reflectT G (T.period i) (canal b (o i))) (spl_tip _ _ o (spline_image (canal_base T b o)) hp) c
  let e:=mass b+mass c
  let P i:= corrected (T.gap i) (x i) j j b c
  let V (i:ℕ):=native c (o i) (canal b (o i))-D+native c (o i) (reflectT G (T.period i) (canal b (o i)))
  have hxW i : T.gap i^e * P i=V i+D-Full.link 1 b c := by
    unfold e P; unfold corrected; rw [if_pos rfl, aura_eq,liftLink b c,tape_scales]; unfold river V o; simp only [map_smul, LinearMap.smul_apply,map_add, smul_eq_mul,pow_add, mul_inv]; field_simp [(T.positive i).ne']; ring
  have h0 : Tendsto P atTop (𝓝 0) := by
    have H:=corrected_limit T x v hv hx hr j j b c
    simp only [indirect, if_true] at H; exact H
  have ht : Tendsto (fun i:ℕ=> T.gap i^e * P i) atTop (𝓝 0) := by simpa only [mul_zero] using (T.cutoff.pow _).mul h0
  have hF : Fleck T V := H.roll H1
  have he : D=Full.link 1 b c := by
    apply sub_eq_zero.mp
    have hp:= hF.cheap.add_const D |>.sub_const (Full.link 1 b c); simp only [zero_add] at hp
    exact tendsto_nhds_unique (hp.congr fun i=> (hxW i).symm) ht
  have hQ : P = fun i=> (T.gap i^e)⁻¹ * V i := funext (fun i=>by
    have hh := hxW i; rw [← he, add_sub_cancel_right] at hh; rw [←hh, inv_mul_cancel_left₀ (by exact pow_ne_zero _ (T.positive i).ne'
    )])
  change Fleck T P; rw [hQ]; exact hF.sale _
end YM.RG11.FirstW
