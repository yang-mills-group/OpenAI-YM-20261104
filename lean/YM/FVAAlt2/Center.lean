import YM.MS.Swirl.Migrate
import YM.FVAAlt2.LatticeFourier

/-!
# Exact periodicization of the `PhysicalSum` vertices

A mark has test at absolute center A+x, NO orbital or torus weighting. All
vacuum vertices have an unnormalized torus translation sum; for inversion
will see an extra `pay true=1/2`. Inversion and the Grassmann convention
of its remaining linear gauge variables appear in the Wick kernel not these
vertices. This bridge does not require stencil supports to be small enough
for injection into the period or avoid fixed points. It is equality (uses
exact wrapping including aliasing), not an estimate uniform in regulator.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2
open Lattice Function Finset MS MS.Native MS.Native.Wilsonian MS.Koszul MS.Plane
open MS.Orbit MS.Swirl MS.Swirl.Near MS.Orbit.LogReal MS.Orbit.Cog MS.Tone MS.Landau
open MS.Cylinder MS.Cylinder.Lab MS.Fleet MS.Book MS.Book.Convolve 
variable {G:Gauge}{n:Side}
local notation "F" => fourier G n

/-- one-leg test includes the wrap point exactly because frequency is in
`proper`. This removes midpoint weights on a sharp transform. -/
lemma covered (x : LightMode G Cover)(p : FixedMode G n):
    F p (post (wrap n) x)= lace (addr p)* Tone.paywave (addr p) x:= by
  rcases p with ⟨a,p⟩; rcases x with ⟨b,x⟩; by_cases h:b=a
  · subst b; change F (a,p) (a,wrap n x) = lace (a,Coord p)* Tone.paywave (a,Coord p) (a,x)
    rw [fourier_on,pw,rightadd, inversePa,← dual_cell,rights (embed x)]
    change _= (bill (Coord p) (Tone.offset a.1))⁻¹ * (_ * _)
    field_simp
  change F (a,p) (b,_) = lace _ * _
  rw [fourier_off (Ne.symm h), show Tone.paywave _ _=0 from Classical.byContradiction fun he=> h (in_light (addr (a,p)) (b,x) he).symm, mul_zero]

lemma wrap_center (u : Dot G Cover)(w : List (FixedMode G n)) :
    pull F (shown n u).val w = sleeve lace (run u) (Orbit.stage w):= by
  rw [← eq_pull]; unfold shown transport run; rw [study]
  rw [sleeve_here]; induction w generalizing u with
  | nil=> simp [Orbit.hook,Orbit.stage]
  | cons a w ih=>
    obtain ⟨s,hs⟩ := fromCyl u
    rw [deriv_lum _ _ _ hs, show Orbit.stage (a::w)=addr a::Orbit.stage w from rfl,
      deriv_lum _ _ _ hs, show Orbit.hook lace (_ :: _) = _ from List.prod_cons, Finset.mul_sum]
    refine sum_congr rfl fun i _=>?_ ; rw [covered i, ih]; ring

lemma recVol (n:Side): brightness n=(n.val:ℂ)^4 := by
  unfold brightness scaleZ νt; push_cast; rw [inv_inv]

lemma all_bulk (u : Dot G Cover) :
    pull F (Lab.sumHome (shown n u)).val = Bulk G n (sleeve lace (run u)) := by
  funext w; rw [sumHome_pull,bulkZ,wrap_center,recVol]; rfl

lemma all_mark (A x:Cover)(u : Dot G Cover) :
    pull F (Lab.Shift (wrap n (A+x)) (shown n u)).val = Mark_T G n A x u := by
  funext w; rw [shift_character, wrap_center,
    show Mark_T G n A x u w=anchor G n A (frameL x (Tone.run u)) w from rfl,
    chase_now,f_l,Orbit.point,lodg,← φ_s]
  unfold Φa; rw [map_add,Bloch.cell_add,Bloch.cell_duality (wrap n A),Bloch.cell_duality (wrap n x)]; ring

lemma send_bulk (u : Dot G Cover) (b:Bool) : SendB G n b u=pull F (pay b • (sumHome (shown n u)).val):=by
  rw [map_smul,all_bulk]; rfl
end YM.FVAAlt2
