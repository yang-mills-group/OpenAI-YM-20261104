import YM.UVNext.FREE_STRESS_CERTIFICATE.StressSpace

/-! Complex grade-four stress coordinates on the signed-axis Maxwell table. -/
set_option autoImplicit false
noncomputable section

namespace YM.UVNext.FreeStress.Uncentered

open Maxwell Labels Climb Table Work.A01 Next.UVStress Function Set Submodule

variable {G : Gauge} (F : Frames G) (H : (freeTable F).RealSpin) (hG : G.Simple)
variable (J : (freeTable F).Stress) (tensor : RawTensor H J)

include tensor in
theorem permuted (p : Wheels) (a b : Axis) :
    ride F H 4 p (J a b) = J (p a) (p b) := by
  unfold ride
  rw [tensor_column tensor, eps_round, eps_round]
  simp [round]

include tensor in
theorem colored (i j : Axis) :
    swatch F H 4 (fun t => bit t i * bit t j) (J i j) := by
  intro t
  rw [tensor_column tensor, eps_mirror_bit, eps_mirror_bit]
  push_cast
  rfl

include hG tensor in
theorem diagonal : J 0 0 ∈ span ℂ { (freeTable F).unit 4, near F 0, far F 0 } := by
  let U := span ℂ {(freeTable F).unit 4, near F 0, far F 0}
  have H1 : (freeTable F).unit 4 ∈ U := subset_span (by simp)
  have H2 : singles (fun i => flat F 0 i 0 i)∈U := near_zero F ▸ subset_span (by simp)
  have H3 : pairs (fun i j => flat F i j i j)∈U := far_zero F ▸ subset_span (by simp)
  have ht (p : Wheels) (_h : p 0=0) : ride F H 4 p (J 0 0)=J 0 0 := by rw [permuted F H J tensor,_h]
  apply secure F H _ ht
  let χ (t : Axis) := bit t 0 * bit t 0
  apply align F H _ χ (binary_compose (binary_bit _) (binary_bit _)) (colored F H J tensor 0 0) _ _ (spanFour hG)
  rintro _ (rfl|⟨i,k,rfl⟩)
  · rw [pin_unit]; refine ⟨fun _ => 1,binary_unit,unit_color F H _,fun _ => ?_⟩
    change revolving F H 4 ((freeTable F).unit 4) ∈ U
    rw [revolve_value]; simp only [around,ride_unit]
    exact U.add_mem (U.add_mem (U.add_mem (U.add_mem (U.add_mem H1 H1) H1) H1) H1) H1
  refine ⟨fun t => zob i t*zob k t,binary_compose (binary_plane i) (binary_plane k),
    link_color F H _ _ _ _ le_rfl, fun he => ?_⟩
  obtain ⟨-,rfl⟩|⟨c,_,_,hx,_⟩ := even_format i k 0 fun t => congr_fun he.symm t
  · obtain ⟨⟨a,b⟩,hp⟩ := i
    change flat F a b a b∈U.comap (revolving F H 4)
    change a < b at hp
    have hb : b≠0 := (lt_of_le_of_lt (Fin.zero_le _) hp).ne'
    rcases eq_or_ne a 0 with rfl|ha
    · exact harvest_single F H (fun b => flat F 0 b 0 b) b hb (fun p hw => by simp only [flat,ride_link,hw]) U H2
    exact harvest_pair F H (fun a b => flat F a b a b) a b ha hb hp.ne (fun p _ => by simp only [flat,ride_link]) U H3
  exact (hx rfl).elim

include hG tensor in
theorem offDiagonal : J 0 1 ∈ span ℂ {panel F 0 1} := by
  let U := span ℂ {panel F 0 1}
  let V := U.comap (lastPair F H 4)
  let χ t := bit t 0*bit t 1
  apply securing F H _ (by rw [permuted F H J tensor]; simp [l23,Equiv.swap_apply_def])
  apply align F H _ χ (binary_compose (binary_bit _) (binary_bit _)) (colored F H J tensor 0 1) V _ (spanFour hG)
  rintro _ (rfl|⟨i,k,rfl⟩)
  · rw [pin_unit]; refine ⟨fun _ => 1,binary_unit,unit_color F H _,fun h => ?_⟩
    have hh := congr_fun h (0:Axis); norm_num [χ,bit] at hh
  refine ⟨fun t => zob i t*zob k t,binary_compose (binary_plane i) (binary_plane k),link_color F H _ _ _ _ le_rfl, fun h => ?_⟩
  have he (a : Axis) (ha : a ≠ 0) (ht : a ≠ 1) : flat F 0 a 1 a∈V := by
    change flat F _ a _ a + ride F H _ l23 _ ∈ U
    dsimp only [flat]; rw [ride_link,show l23 0=0 by decide,show l23 1=1 by decide]
    let f := fun i => flat F 0 i 1 i
    change f a + f (l23 a) ∈ U
    rw [two_one f a ha ht, ← panel_one]; exact subset_span (mem_singleton _)
  rcases even_format i k 1 (fun t => congr_fun h.symm t) with ⟨hf,-⟩|⟨a,h1,h2,h3,⟨h4,h5⟩|⟨h4,h5⟩⟩
  · exact ((by decide : (1:Axis) ≠ 0) hf).elim
  · exact click_link F i k 0 a 1 a h4 h5 le_rfl V (he a h1 h2)
  rw [two_flip _ i k]
  exact click_link F k i 0 a 1 a h4 h5 le_rfl V (he a h1 h2)


/-- The fourth coordinate is the off-diagonal curvature contraction. -/
def fields (d a b c : ℂ) : (freeTable F).Stress := fun i j =>
  (if i = j then d • (freeTable F).unit 4 else 0) +
    a • east F i j + b • west F i j + c • across F i j

private theorem fields_permuted (d a b c : ℂ) (p : Wheels) (i j : Axis) :
    ride F H 4 p (fields F d a b c i j) = fields F d a b c (p i) (p j) := by
  have he : ride F H 4 p (east F i j) = east F (p i) (p j) :=
    perm_tensor F H ⟨east F, east_on F H⟩ p i j
  have hw : ride F H 4 p (west F i j) = west F (p i) (p j) :=
    perm_tensor F H ⟨west F, west_on F H⟩ p i j
  have ha : ride F H 4 p (across F i j) = across F (p i) (p j) :=
    perm_tensor F H ⟨across F, across_on F H⟩ p i j
  by_cases hij : i = j
  · subst j
    simp [fields, he, hw, ha, ride_unit]
  · simp [fields, hij, he, hw, ha]

include hG tensor in
/-- Every complex signed-axis tensor has a single unit and three quadratic
coordinates. The identity holds on every pair of axes before taking a mean. -/
theorem coordinates : ∃ d a b c : ℂ, J = fields F d a b c := by
  have hd := diagonal F H hG J tensor
  rw [Set.insert_eq, span_union, mem_sup] at hd
  obtain ⟨u, hu, v, hv, huv⟩ := hd
  obtain ⟨d, rfl⟩ := mem_span_singleton.mp hu
  obtain ⟨a, b, rfl⟩ := mem_span_pair.mp hv
  obtain ⟨c, hc⟩ := mem_span_singleton.mp (offDiagonal F H hG J tensor)
  let P := fields F d a b c
  have h00 : J 0 0 = P 0 0 := by
    simpa [P, fields, east, west, across, splitDiag, add_assoc] using huv.symm
  have h01 : J 0 1 = P 0 1 := by
    simpa [P, fields, east, west, across, splitDiag] using hc.symm
  refine ⟨d, a, b, c, ?_⟩
  funext i j
  let f : Wheels := Equiv.swap 0 i
  have hf : f 0 = i := by simp [f]
  rcases eq_or_ne j i with rfl | hji
  · have h := congrArg (ride F H 4 f) h00
    simpa only [P, permuted F H J tensor, fields_permuted, hf] using h
  let p := Equiv.swap (f 1) j * f
  have hne : f 0 ≠ f 1 := f.injective.ne (by decide)
  have hp : p 0 = i := by
    simp [p, Equiv.swap_apply_def, hf, hji.symm, show i ≠ f 1 from hf ▸ hne]
  have h1 : p 1 = j := by simp [p]
  have h := congrArg (ride F H 4 p) h01
  simpa only [P, permuted F H J tensor, fields_permuted, hp, h1] using h

end YM.UVNext.FreeStress.Uncentered

