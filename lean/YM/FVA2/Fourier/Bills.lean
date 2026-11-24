import YM.FVA2.Fourier.Transform
import YM.MS.Swirl.Migrate

/-!
# Their Fourier bills are the DFT of their periodic stencils

Exact periodization and full volume factor with derivative legs (`shade`), both at all momenta
for the translation-summed bulk and at a literally placed mark. Applies to every cylinder;
so in particular this transports the unmarked action, Haar and gauge-generator vertices and the
physical source stencils. The `pay` half for inversion applies only to the bulk, *not* to the
placed mark.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Fourier
open Function Set Finset
open YM.MS YM.MS.Koszul YM.MS.Plane YM.MS.Cylinder Lab YM.MS.Book YM.MS.Orbit
open YM.MS.Landau YM.MS.City YM.MS.Tone YM.MS.Native YM.MS.Swirl YM.MS.Swirl.Near
open YM.Lattice
open scoped BigOperators Matrix
variable {G : Gauge} {n : Side}

lemma cover_to_site (i : FixedMode G n) (j : LightMode G Cover) :
    (toSite G n)ᵀ i (Lab.post (wrap n) j) = lace (addr i) * paywave (addr i) j := by
  rcases i with ⟨a,p⟩; rcases j with ⟨b,x⟩
  change (if b=a then Bloch.cell p (wrap n x) else 0) = _
  by_cases h : b=a
  · subst h
    rw [if_pos rfl, show paywave (addr (b,p)) (b,x) = _ from pw b x (Coord p)]
    rw [Tone.rightadd, Tone.rights (Coord p) (embed x), dual_cell p x]
    change _ = lace _ * (_ * weightψ (addr (b,p)))
    rw [mul_left_comm, mul_comm (lace _), lace_, mul_one]
  rw [if_neg h, show paywave (addr (a,p)) (b,x)=0 from
    Classical.byContradiction fun he => h (Tone.in_light _ _ he).symm, mul_zero]

/-- No midpoint phase after `sleeve lace`. -/
theorem single_cover (F : Dot G Cover) (l : Legs (FixedMode G n)) :
    Wick.pull (toSite G n) (enters n F) l = sleeve lace (Tone.run F) (stage l) := by
  change Wick.pull _ (Ferry (post (wrap n)) F).val l = _
  rw [Wick.pull_shade, study]
  induction l generalizing F with
  | nil => exact (one_mul _).symm
  | cons i l ih =>
    obtain ⟨s,hs⟩ := fromCyl F
    let T (i' : FixedMode G n) (j : LightMode G Cover) := (toSite G n)ᵀ i' (post (wrap n) j)
    change shade T F (i::l) = (sleeve lace (shade paywave F)) (addr i :: stage l)
    rw [sleeve_here, deriv_lum T i F hs, deriv_lum paywave (addr i) F hs,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold T; rw [cover_to_site, ih (enter j F), sleeve_here]
    simp only [Tone.run, Orbit.hook, List.map_cons, List.prod_cons]; ring

lemma shifted (F : Dot G Cover) (x : Cover) (l : Legs (FixedMode G n)) :
    Wick.pull (toSite G n) (enters n (Lab.Shift x F)) l =
      Φa x (net l) * sleeve lace (Tone.run F) (stage l) := by
  rw [single_cover, sleeve_here, Tone.movement, φ_s, sleeve_here,
    Tone.rights (net (stage l))]; exact mul_left_comm ..

lemma cell_total (p : Site n) : ∑ x : Site n, Bloch.cell p x =
    if p=0 then brightness n else 0 := by
  split_ifs with h
  · subst h
    simp [Bloch.cell, brightness]
  exact Bloch.sum_cell h

/-- Translation-summed, no inversion restriction. This includes zero modes. -/
theorem bulk_cover (F : Dot G Cover) :
    Wick.pull (toSite G n) (docket n F) = Bulk G n (sleeve lace (Tone.run F)) := by
  funext l; rw [bulkZ]
  let V := sleeve lace (Tone.run F) (stage l)
  change Wick.pull _ (sumHome (shown n F)).val l = if net l=0 then brightness n * V else 0
  rw [total_uses, sum_stack, map_sum, Finset.sum_apply]
  have H (x : Site n) : Wick.pull (toSite G n) (Lab.Shift x (shown n F)).val l = Bloch.cell (net l) x * V := by
    let y := Lattice.lift x
    have H : wrap n y = x := wrap_lift _
    have h : Lab.Shift x (shown n F) = shown n (Lab.Shift y F) := by
      change _ = Lab.transport _ _
      rw [Lab.trans_shift F y (wrap n), H]; rfl
    rw [h, show (shown n (Lab.Shift y F)).val = enters n (Lab.Shift y F) from rfl, shifted]
    unfold Φa; rw [H, Bloch.cell_duality x]
  simp_rw [H, ← Finset.sum_mul, cell_total]; split <;> simp

/-- `SendB` (so includes the pay, exactly 1/2 if in the inversion quotient). -/
theorem send_cover (F : Dot G Cover) (b : Bool) :
    SendB G n b F = Wick.pull (toSite G n) (Cog.pay b • docket n F) := by
  rw [map_smul, bulk_cover]
  rfl

/-- The mark stencil is from x+c, including centered offset Fourier book. -/
theorem mark_cover (F : Dot G Cover) (x c : Cover) :
    Mark_T G n x c F = Wick.pull (toSite G n) (enters n (Lab.Shift (x+c) F)) := by
  funext l
  rw [shifted]
  change (Orbit.anchor _ _ _ _) _ = _
  rw [chase_now, Orbit.point, LinearMap.comp_apply, Fleet.f_l, Fleet.lodg, φ_s, φ_s]
  unfold be
  rw [Tone.emb_add, Tone.payadd, mul_assoc]

end YM.FVA2.Fourier
