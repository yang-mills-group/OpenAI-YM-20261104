import YM.FVA2.Plug
import YM.MS.Swirl.Resolute

/-!
# FVA Wilson bridge: put the entire Endμ problem in position variables (log links)

No midpoint ambiguity or Fourier support assumptions in this conversion. `energyPart`
acts by the sum over every *cover* site of the torus, with `pay true = 1/2` on the
inversion ensemble. Marks are singleton pinned full-weight as in the manuscript, even
at an inversion fixed point (extra clearance restrictions arise later). Everything in
this file is exact on the regulator and no assumptions on phase, geometric schedule,
group simplicity or Gram data enter. **This is still the Landau prescription with BV
variable tags**, not yet tree gauge. Files depending on this one must prove explicitly
what these contractions calculate in positions, and may not use b=false pretending it
is a massless tree Wilson integral.
-/

set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Based
open MS MS.Koszul MS.Plane MS.Landau MS.Swirl MS.Swirl.Near MS.Tone MS.Orbit MS.Orbit.Cog
open MS.Orbit.LogReal MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Engine
open MS.Puff.SplitP MS.Puff.Actors MS.Puff.Mom MS.SpaceOut MS.Fleet MS.Cylinder
open MS.Cylinder.Lab MS.Native MS.Native.Draft MS.Native.Wilsonian Lattice Finset

/-- Legal MS modes, now regarded as based field coordinates (in the test function inputs).
 Index `(some μ,true)` K and `(some μ,false)` A both use the *base* x of positive μ edge. -/
abbrev Pos (G : Gauge) (n : Side) := LightMode G (Site n)

variable (G : Gauge) (n : Side)

/-- The coordinate change is *unscaled*. Therefore the half-covariance already
in `Master` still carries the inverse full cover volume. -/
def basisM (p : FixedMode G n) (x : Pos G n) : ℂ :=
  way id p.1 x.1 * Bloch.cell p.2 x.2

lemma basis_tie : Tie σbranch σbranch (basisM G n) := by
  rintro ⟨i,x⟩ ⟨j,p⟩ h
  by_cases hx : i=j
  · subst j; rfl
  exact (h (by rw [basisM,need id (Ne.symm hx), zero_mul])).elim

private lemma cell_combined (q p x : Site n) :
    Bloch.cell (q+p) x = Bloch.cell q x * Bloch.cell p x := by
  rw [Bloch.cell_duality _ x, Bloch.cell_add, Bloch.cell_duality x, Bloch.cell_duality x p]

private lemma basisFactor (x : Site n) (v : Pos G n) (p : FixedMode G n) :
    basisM G n p (v.1,x+v.2) = Bloch.cell p.2 x * basisM G n p v := by
  simp only [basisM,Bloch.cell_add]; ring

lemma translated (x : Site n) (F : Dot G (Site n)) (w : List (FixedMode G n)) :
    shade (basisM G n) (Lab.Shift x F) w = Bloch.cell (net w) x * shade (basisM G n) F w := by
  change shade (basisM G n) (Ferry (post fun q : Site n => x+q) F) w = _
  rw [study]
  induction w generalizing F with
  | nil =>
    change _ = Bloch.cell (0:Site n) x * _
    rw [Bloch.cell_duality, Bloch.cell_origin, shade_nil,shade_nil,one_mul]
  | cons i l ih =>
    obtain ⟨s,hs⟩ := fromCyl F
    rw [net_cons,cell_combined,deriv_lum _ _ F hs,deriv_lum (basisM G n) _ F hs,
        Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [ih,show basisM G n i (post (fun q : Site n=> x+q) j)=_ from basisFactor G n x j i]
    ring

private lemma paysCovered (p : FixedMode G n) (v : LightMode G _root_.YM.Lattice.Cover) :
    basisM G n p (v.1,wrap n v.2) = lace (addr p)*paywave (addr p) v := by
  obtain ⟨a,p⟩ := p; obtain ⟨b,x⟩ := v
  by_cases hb : b=a
  · subst b
    rw [show basisM G n (a,p) (a,wrap n x) = Bloch.cell p (wrap n x) from ?_]
    · change _= lace (a,Coord p) * paywave (a,Coord p) (a,x)
      rw [pw, ← dual_cell, Tone.rights, rightadd, show bill (Coord p) (offset a.1)=
                    weightψ (a,Coord p) from rfl, mul_comm (lace _), mul_assoc, lace_,mul_one]
    change (way id (id a) a:ℂ) * _ = _
    rw [only,one_mul]
  change (way id a b : ℂ) * _ = _ * ((way id a b :ℂ)* _)
  rw [need id (Ne.symm hb),zero_mul,zero_mul,mul_zero]

/-- Full finite-series Fourier rule on every cylinder with arbitrary tags. -/
theorem transform_stencil (F : Dot G _root_.YM.Lattice.Cover) :
    shade (basisM G n) (shown n F) = Vμ (sleeve lace (Tone.run F)) n := by
  change shade (basisM G n) (Ferry (post (wrap n)) F) = _
  rw [study]; ext1 l
  induction l generalizing F with
  | nil => simp [Orbit.point,Orbit.stage,hook,Tone.run]
  | cons i l ih =>
    obtain ⟨s,hs⟩ := fromCyl F
    rw [Orbit.point,Orbit.stage,List.map_cons,sleeve_here,hook,List.map_cons,List.prod_cons,
        deriv_lum _ _ F hs]
    change _=(lace _*_)*(shade paywave F (_ :: _))
    rw [deriv_lum paywave _ F hs,Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [show basisM G n i (post (wrap n) j) = _ from paysCovered G n i j, ih,
        Orbit.point,sleeve_here]
    unfold hook
    change _ * ((_ : ℂ) * (shade paywave _ _)) = _
    ring

lemma phase_cell (A : _root_.YM.Lattice.Cover) (p : Site n) :
    Bloch.cell p (wrap n A) = Φa A p := Bloch.cell_duality ..

/-- Position representation of `Mark_T`. A Wilson stencil translated in native fine units
 before wrapping. Translation acts on all its arguments at once. -/
def place (x : Site n) : Dot G _root_.YM.Lattice.Cover →ₗ[ℂ] BL (Pos G n) :=
  (Cylinder.Stack _ _).subtype.comp ((Lab.Shift x).comp (shown n))

theorem pin (F : Dot G _root_.YM.Lattice.Cover) (A x : _root_.YM.Lattice.Cover) :
    Modes.plug (basisM G n) (place G n (wrap n (A+x)) F) = Mark_T G n A x F := by
  change Modes.plug _ (Lab.Shift (wrap n (A+x)) (shown n F)).val =
     Orbit.anchor G n A (frameL x (Tone.run F))
  rw [Modes.plug_cyl, vFrame, eFrame]
  ext1 w
  rw [chase_now,← transform_stencil, translated, ← phase_cell n]
  change _ = _* shade (basisM G n) (transport (wrap n) (Lab.Shift x F)) w
  rw [trans_shift,translated,map_add,Bloch.cell_add]
  exact mul_assoc ..

private lemma sum_phases (p : Site n) :
    ∑ x : Site n, Bloch.cell p x = if p=0 then brightness n else 0 := by
  by_cases h : p=0
  · subst p
    simp [brightness,scaleZ,νt,Bloch.cell]
  rw [if_neg h]; exact Bloch.sum_cell h

def energyPart (b : Bool) : Dot G _root_.YM.Lattice.Cover →ₗ[ℂ] BL (Pos G n) :=
  pay b • docket n

/-- Docket normalization: `SendB` actually realizes the full `pay b • docket n`, not a
 per-site average. In the quotient `energyPart` is the half-counting rule. -/
theorem unmarked (b : Bool) (F : Dot G _root_.YM.Lattice.Cover) :
    Modes.plug (basisM G n) (energyPart G n b F) = SendB G n b F := by
  change Modes.plug _ (pay b • (sumHome (shown n F)).val) = pay b • (Bulk G n _)
  rw [map_smul]; apply congr_arg (pay b • ·)
  rw [Modes.plug_cyl,total_uses,map_sum]
  ext1 l; rw [bulkZ,Finset.sum_apply]
  change _= if net l=0 then brightness n * Vμ (sleeve lace (Tone.run F)) n l else 0
  simp_rw [translated,← Finset.sum_mul,sum_phases,transform_stencil]; split <;> simp

/-- Interacting part of the log density in this representation. BV field types
 are those of the cover prescription; the full finite rank series (including
 Haar) is determined by `core`. `style` also effects the bare reparametrization. -/
def posNRG (t : Team) (x : ℝ) (b : Bool) : SpecB (Pos G n) := fun k =>
    if k=0 then 0 else energyPart G n b (style G t x k)

variable {W : Type} [LinearOrder W]

/-- Pinned source vertices (before exponentiating and normalizing at a subset). -/
def posMark (V : W → Actor G) (x : ℝ) (A : _root_.YM.Lattice.Cover)
    (c : W → _root_.YM.Lattice.Cover) : Mate (Pos G n) W := fun s =>
    if h:s.Nonempty then if s.card=1 then pointL ℕ
      (place G n (wrap n (A+c (s.min' h)))) (V (s.min' h) x)
    else 0 else 0

lemma charge_zero (t : Team) (x : ℝ) (b : Bool) : posNRG G n t x b 0=0 := rfl -- Decidable zero

lemma pin_one (V : W → Actor G) (x : ℝ) (A : _root_.YM.Lattice.Cover) (c) (w : W) :
    posMark G n V x A c {w}= pointL ℕ (place G n (wrap n (A+c w))) (V w x) := by
   simp [posMark]

lemma pin_off {s : Finset W} (h : s.card ≠ 1) (V : W → Actor G) (x : ℝ)
    (A : _root_.YM.Lattice.Cover) c : posMark G n V x A c s=0 := by
   unfold posMark; split <;> rfl

lemma pin_mark (V : W → Actor G) (x : ℝ) (A : _root_.YM.Lattice.Cover) (c) :
    Marks V x n A c = Modes.seriesPlug (basisM G n) ∘ posMark G n V x A c := by
   ext1 s; by_cases h:s.card=1
   · obtain ⟨w,rfl⟩ := Finset.card_eq_one.mp h
     rw [Function.comp_apply, mark_me, pin_one]; ext1 k
     exact (pin G n _ A (c w)).symm
   rw [Function.comp_apply, pin_off G n h, mark_off h, map_zero]

lemma bulk_interaction (t : Team) (x : ℝ) (b : Bool) :
    NRG t x n G b = Modes.seriesPlug (basisM G n) (posNRG G n t x b) := by
  ext1 k; change _=Modes.plug _ _; unfold NRG posNRG; split
  · rw [map_zero]
  exact (unmarked G n b _).symm

lemma pin_fee {F : Dot G _root_.YM.Lattice.Cover} (x : Site n) (h : Tuned F 0)
    (r : ℤ) (hr : Limit F.val r) : place G n x F∈ FeeP σbranch := by
  exact ⟨ (Tune.move (fun j=> x+j) (Tune.move (wrap n) h)).symm,
    minH (Limit.shades (shown n F) (Limit.shades F hr _) _) ⟩

lemma bulk_fee {F : Dot G _root_.YM.Lattice.Cover} (h : Tuned F 0)
    (r : ℤ) (hr : Limit F.val r) (b : Bool) : energyPart G n b F ∈ FeeP σbranch := by
  apply (FeeP σbranch).smul_mem
  change (sumHome (shown n F)).val ∈ _
  rw [total_uses,sum_stack]; exact (FeeP _).sum_mem fun i _ => pin_fee G n i h r hr

lemma bulk_bounded (t : Team) (x : ℝ) (b : Bool) : Γ (posNRG G n t x b) σbranch := by
  intro k _; unfold posNRG; split
  · exact (FeeP σbranch).zero_mem
  exact bulk_fee G n ((core_circle G t).actual k x) _ (style_limit t x G k) b

lemma pin_bounded (V : W → Actor G) (h : Badge V) (x : ℝ) (A : _root_.YM.Lattice.Cover)
    (c) (s : Finset W) : Γ (Font σbranch (posMark G n V x A c) s) σbranch := by
  let F := posMark G n V x A c
  let U := PermV (σbranch (G:=G) (n:=n))
  apply costCheer (S:=U) (marked W) (B:=allIndex (FeeP σbranch) ℕ)
     (refineπ useN (coin 1) feeUnit) (fun _ hp _ hq => ΤΓ_pair hp hq)
     (show F∈allIndex _ _ from ?_) s (Set.mem_univ _)
  intro t _; unfold F; by_cases he:t.card=1
  · obtain ⟨w,rfl⟩:= Finset.card_eq_one.mp he; intro k _; rw [pin_one]
    obtain ⟨r,hr⟩:=(h w).room k; exact pin_fee G n _ ((h w).actual k x) _ (hr x)
  rw [pin_off G n he]; exact (allIndex _ _).zero_mem

def cov (b : Bool) : Grain (Pos G n) := Modes.induceK (basisM G n) (Master G n b)

/-- Supplier toward Wilson to MS. Exact equality of the *entire* normalized BV Series
 problem at each finite regulator, including inserted fields and their addresses. Checks
 all needed finite order Rank limits. Tuning can be any Team, not postulated to have any
 particular matching property. Next tasks: identify `cov`, the portion of these jets
 read physically, and the remaining hypotheses for choosing sources. -/
theorem positionEnd (t : Team) (x : ℝ) (b : Bool) (V : W → Actor G) (h : Badge V)
    (A : _root_.YM.Lattice.Cover) c (s : Finset W) (Z : T ℂ) :
    PhysicalSum G t x n b s c A V Z ↔
      Endμ (cov G n b) σbranch (posNRG G n (Stripped t) x b)
           (Font σbranch (posMark G n V x A c) s) Z := by
   unfold PhysicalSum; rw [bulk_interaction, pin_mark G n, ← Modes.seriesPlug_sources _ (basis_tie G n)]
   exact Modes.plug_end _ (Master G n b) (basis_tie G n) (bulk_bounded G n (Stripped t) x b) (pin_bounded G n V h x A c s) Z

end YM.FVA2.Based
