import YM.Comparison.Stencils.Color

/-!
# Turning the insertion columns

Covariant (simultaneous, source and test) symmetry; ordinary real form is
separate from time reflection. Kernel identity on all log link arrays, not a
character or a.e. statement. We *don't* move the interacting frames by
assuming O(4) action on those arrays; lattice here uses only Signed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Stencils.Motion
open CubicMatch Lattice Function RG Wilson Symbols Labels Source Source.Drops Filter Feed
open Next.Foundations
open Planned.PrimaryIntegral295.Place (Spot Dev column_smooth slant_smooth placeEdge pore)
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
variable {G : Gauge} {S S' : Finset Cover} {s : Signed}

section Rotate

/-- Literal symbol rotation (P stencil turns to Q stencil). -/
def Spins (s : Signed) (P : LocalPol G S) (Q : LocalPol G S') := ∀ (A : Links ℤ G.Color),
    inscribe (Symbols.patch S (pullLogs A s 0)) P = inscribe (Symbols.patch S' A) Q

lemma spins_portion {P : LocalPol G S} {Q : LocalPol G S'} (h : Spins s P Q) (i : ℕ) :
    Spins s (portion i P) (portion i Q) := by
  intro A; simp_rw [portion_rays]; apply congrArg _; funext t
  rw [show t • pullLogs A s 0=pullLogs (t • A) s 0 by
    funext e; simp only [Pi.smul_apply, pullLogs, orientedColor]; split <;> first | rfl | rw [smul_neg]]
  exact h _

def rotJ (s : Signed) (A : Jet G) : Jet G := changedJet (fun _ => Taylor.turn s.ortho⁻¹) A

lemma rotated_reads (s : Signed) (J : Jet G) (p : Pol G) :
    Labels.read J (rotated s.ortho p) = Labels.read (rotJ s J) p := eval_changed ..
lemma portion_spin (p : Pol G) (s : Signed) (i : ℕ) :
    portion i (rotated s.ortho p)= rotated s.ortho (portion i p) := by
  refine Labels.eval_ext _ _ ?_
  intro A; rw [rotated_reads s _ (portion i p), radial_rays, radial_rays]
  apply congrArg (term i); funext t
  rw [rotated_reads, show rotJ s (t • A)=t • rotJ s A from funext fun k => map_smul (Taylor.turn _) t (A k)]

private lemma plog_inv_near (G : Gauge) : ∀ᶠ u : G.El in 𝓝 1, G.plog (G.mat u⁻¹) = - G.plog (G.mat u) := by
  let f (u : G.El) := - G.plog (G.mat u)
  have he : ContinuousAt f 1 := by
    exact ((show ContinuousAt G.plog (G.mat 1) from by rw [G.mat_one]; exact G.plog_diff.continuousAt).comp
      G.continuous_mat.continuousAt).neg
  have hh : Tendsto f (𝓝 1) (𝓝 0) := (show f 1=0 from by simp [f]) ▸ he
  filter_upwards [G.plog_right, hh.eventually G.plog_left] with x hv hp
  rw [show x⁻¹ = G.lieExp (f x) by unfold f; rw [Work.F03.exp_neg_color, hv]]
  exact hp

theorem ink_rot (J : Jet G) (s : Signed) (H : Hol G) (d : ℕ) :
    ∀ᶠ t in 𝓝 0, Symbols.patch S (ink H (rotJ s J) d t) =
      Symbols.patch S (pullLogs (ink H J d t) s 0) := by
  have he (i : Edge Cover) : ∀ᶠ t in 𝓝 0, ink H (rotJ s J) d t i = pullLogs (ink H J d t) s 0 i := by
    let j := (posDir i.2).rotate s
    let x := affine s (0:Cover) i.1
    filter_upwards [(hatch H J d (j.used x)).eventually (plog_inv_near G)] with t ht
    rw [ink, rotJ, ← Work.G01.swirls_of_flow H s]
    change G.plog (G.mat (j.read (H.links d J t) x)) = orientedColor _ _ _
    unfold orientedColor Step.read
    split
    · exact ht
    rfl
  exact (eventually_all.mpr (fun i : Spot S => he (placeEdge i))).mono fun _ hu => funext hu

lemma pushes (p : LocalPol G S) (q : LocalPol G S') (hs : Spins s p q) (H : Hol G) (d : ℕ) :
    projector H d q = rotated s.ortho (projector H d p) := by
  apply sole_poly _ _ d (raw_cap ..) (moved_limit (d := d) (raw_cap ..) _)
  intro X k hk
  have he (t : ℝ) (Q : Pol G) : Labels.read (scaleJet X t) (rotated s.ortho Q) =
      Labels.read (scaleJet (rotJ s X) t) Q := by
    rw [rotated_reads,show rotJ s (scaleJet X t)=scaleJet (rotJ s X) t from funext fun i => map_smul (Taylor.turn _) _ (X i)]
  change iteratedDeriv k (fun t => Labels.read (scaleJet X t) (rawPi H d q)) 0 =
    iteratedDeriv k (fun t => Labels.read (scaleJet X t) (rotated s.ortho (rawPi H d p))) 0
  simp_rw [he]
  rw [jet_reads H d q X k hk, jet_reads H d p (rotJ s X) k hk]
  refine Filter.EventuallyEq.iteratedDeriv_eq k ?_
  change (fun t => inscribe (Symbols.patch S' (ink H X d t)) q) =ᶠ[𝓝 0]
      fun t => inscribe (Symbols.patch S (ink H (rotJ s X) d t)) p
  filter_upwards [ink_rot (S:=S) X s H d] with t ht
  rw [ht, hs _]

theorem sends (P : LogSeries G S) (Q : LogSeries G S') (hs : ∀ i, Spins s (P i) (Q i)) (H : Hol G) (d n) :
    stage H d n Q = rotated s.ortho (stage H d n P) := by
  simp only [stage_at, booth, map_sum, LinearMap.sum_apply]
  simp only [LinearMap.comp_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [pushes (s := s) _ _ (spins_portion (hs i) j), portion_spin]
end Rotate

section Conjugate
variable {P : LocalPol G S}
def starSymbol (p : LocalPol G S) := MvPolynomial.map (starRingEnd ℂ) p

lemma reflected_symbol (P : LocalPol G S) (x : Dev S G) : inscribe x (starSymbol P) = star (inscribe x P) := by
  unfold starSymbol
  induction P using MvPolynomial.induction_on with
  | add p q hp hq => simp only [map_add,hp,hq,star_add]
  | C a => simp [inscribe]
  | mul_X p i hp =>
    rw [map_mul, map_mul, map_mul, hp, star_mul, mul_comm (star (inscribe x p))]
    simp [inscribe]

lemma limited_star (P : Pol G) (d : ℕ) (h : P ∈ limited G d) : conjPol P ∈ limited G d :=
    (MvPolynomial.mem_restrictSupport_iff ℂ).mpr fun _ h' =>
      (MvPolynomial.mem_restrictSupport_iff ℂ).mp h (MvPolynomial.support_map_subset (starRingEnd ℂ) P h')

lemma ordinary (P : LocalPol G S) (H : Hol G) (d : ℕ) :
    projector H d (starSymbol P)=conjPol (projector H d P) := by
  refine sole_poly _ _ d (raw_cap ..) (limited_star _ _ (raw_cap ..)) ?_
  let L := (starL' ℝ (A := ℂ)).toContinuousLinearMap
  have he {f : ℝ → ℂ} {k : ℕ} (hf : ContDiffAt ℝ ω f 0) :
      iteratedDeriv k (fun x => star (f x)) 0 = star (iteratedDeriv k f 0) := by
    change iteratedDeriv k (L ∘ f) 0 = _
    rw [iteratedDeriv,L.iteratedFDeriv_comp_left hf le_top]; rfl
  intro X k hk
  change iteratedDeriv k (fun t => Labels.read (scaleJet X t) (rawPi H d (starSymbol P))) 0 =
      iteratedDeriv k (fun t => Labels.read (scaleJet X t) (conjPol (rawPi H d P))) 0
  simp_rw [Labels.conj_value]
  rw [he (Next.Foundations.read_smooth X _ _).contDiffAt, geometry H d P X k hk,
    geometry H d (starSymbol P) X k hk]
  simp_rw [reading, reflected_symbol]
  exact he (Feed.ray_smooth ..)

lemma portion_star (P : LocalPol G S) (j : ℕ) : portion j (starSymbol P)=starSymbol (portion j P) := by
  unfold starSymbol
  apply MvPolynomial.ext; intro k
  rw [portion_coeff, MvPolynomial.coeff_map, MvPolynomial.coeff_map, portion_coeff]; split_ifs <;> simp

lemma slot_star (P : Pol G) (j : ℕ) : portion j (conjPol P)=conjPol (portion j P) := by
  unfold conjPol
  apply MvPolynomial.ext; intro k
  rw [portion_coeff, MvPolynomial.coeff_map, MvPolynomial.coeff_map, portion_coeff]; split_ifs <;> simp

lemma kept_star (P : LogSeries G S) (H : Hol G) (d r : ℕ) :
    stage H d r (starSymbol ∘ P) = conjPol (stage H d r P) := by
  simp only [stage_at, booth, comp_apply, LinearMap.sum_apply, LinearMap.comp_apply, portion_star, ordinary, slot_star]
  simp only [conjPol, map_sum]
end Conjugate

section Actual
variable {d : ℕ} {F : Frame G d} {T : SectionData F} {H : Hol G}

lemma tangent_smooth (T : SectionData F) (p : F.Coeff) (A : Links ℤ G.Color) :
    ContDiff ℝ ω (fun t : ℝ => T.evaluate p (linksOf (t • A))) := by
  have ht : (fun t : ℝ => T.evaluate p (linksOf (t • A))) =
      fun t => T.evaluate p (pore (t • Symbols.patch T.stencil A)) :=
    funext fun t => as_logs _ (T.cylinder_local p) _
  rw [ht]
  exact (slant_smooth T p).comp (f := fun t : ℝ => t • Symbols.patch T.stencil A) (contDiff_id.smul contDiff_const)

/-- Useful for combinations kept real- and H-equivariant instead of
member-by-member symmetric bases. -/
lemma graded_record (T : SectionData F) {p : Label G d} {m : ℕ×ℕ} (h : p ∈ Grade m)
    (A : Links ℤ G.Color) (n : ℕ) :
    inscribe (Symbols.patch T.stencil A) (columns T (F.coords p) n) =
      term (n+m.2) (fun t : ℝ => T.evaluate (F.coords p) (linksOf (t • A))) := by
  rw [portion_eval]
  have he U : T.evaluate (F.coords p) U = ∑ i : F.Index, F.coords p i • cylinder T i U := by
    have hw (v : F.Coeff) : v = ∑ j : F.Index, v j • Pi.single j (1:ℂ) := by funext i; simp [Finset.sum_apply, Pi.single_apply, mul_ite]
    have ht := map_sum (T.eval_linear.mk' _) (fun j => F.coords p j • Pi.single j (1 : ℂ)) Finset.univ
    rw [← hw] at ht
    exact (congr_fun ht U).trans (by rw [Finset.sum_apply]; exact Finset.sum_congr rfl (fun i _ => congr_fun ((T.eval_linear.mk' _).map_smul (F.coords p i) _) U))
  simp_rw [he]
  let f i (t : ℝ) := F.coords p i • cylinder T i (linksOf (t • A))
  rw [term_sum (g := f) (fun i _ => ContDiffAt.const_smul (F.coords p i) ((tangent_smooth T (Pi.single i 1) A).contDiffAt.of_le le_top))]
  apply Finset.sum_congr rfl
  intro i _
  unfold f
  by_cases ht : m=F.grades i
  · simp only [ht, column_value]; unfold term
    rw [iteratedDeriv_fun_const_smul_field, smul_comm]
  · rw [F.power_coefficient _ ht h]; simp [term]

theorem spins (h : T.Sound H) (Tt : F.Coeff) (s : Signed) (u : ℕ) :
    Spins s (columns T Tt u) (columns T (F.act s.ortho Tt) u) := by
  obtain ⟨p,rfl⟩ := F.coords.surjective Tt
  intro A
  rw [← F.basis.sum_repr p]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_congr rfl; intro i _
  rw [F.act_coords]
  apply congrArg (F.basis.repr p i • ·)
  have hx : Labels.tensor s.ortho (F.basis i) ∈ Grade (F.grades i) := by
    have e : gradePart (F.grades i) (Labels.tensor s.ortho (F.basis i)) = Labels.tensor s.ortho (F.basis i) := by
      rw [gradePart_turn, gradePart_self _ _ (F.pure i)]
    exact e ▸ gradePart_mem _ (Labels.tensor s.ortho (F.basis i))
  rw [graded_record T (F.pure i), graded_record T hx]
  simp_rw [turned, h.Hpart]; rw [F.act_coords]

theorem respects_real (h : T.Sound H) (p : F.Coeff) (i : ℕ) :
    columns T (star p) i=starSymbol (columns T p i) := by
  apply inscribe_ext
  intro x
  rw [reflected_symbol, ← drops x]
  simp_rw [portion_eval, star_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [star_smul]
  change star (p j) • _ = star (p j) • _
  congr 1
  let f := fun t : ℝ => cylinder T j (linksOf (t • widen x))
  rw [column_value]
  let L := (starL' ℝ (A := ℂ)).toContinuousLinearMap
  have he : ∀ t : ℝ, f t = L (f t) := by
    intro t
    have hx (U : CoverConfig G) := h.ordinary_real (Pi.single j 1) U
    rw [show star (Pi.single j 1 : F.Coeff)=Pi.single j 1 from funext fun k => by simp [Pi.single_apply]] at hx
    exact hx _
  exact (term_congr (Eventually.of_forall he)).trans (term_linear L (g := f) ((tangent_smooth T _ _).contDiffAt.of_le le_top))
end Actual
end YM.Comparison.Stencils.Motion
