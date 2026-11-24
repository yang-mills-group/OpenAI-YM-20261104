import YM.Integration.WilsonAddressedWeakJoinedWick
import YM.MergeProof.West.Delft

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedWeakNativePolynomials
open Function Lattice Wilson RG Next.Rank Cells MeasureTheory Next.Rank.Tapes Next.Rank.Tapes.West
open Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station
open Ac Alarm Thirst Corona Value Finset Edition Marker
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
variable {G:Gauge} {C:Family G} {k N p n u:ℕ} {ξ:Purse} {Ψ:AtlasData G C.S p}
  {R:Lead G C.S p} {P:(i:ℕ)→Rep G (C.side i p)} {c:Course C N p k}
local notation "Lev" => C.path.levels
theorem fitted (x:Points n) (wide:4*sizeQ C k≤wood (Lev) k)
    (W:Fin n→poly (slotC G (sizeQ C k))) (price:∀ i,coin (W i)≤ξ.principal (clim (Lev) k))
    (deg:∀ i,totalDegree (W i)≤ξ.taylor) (spin:∀ i,Spirit (W i)):
    Kith (A:=C.path.levels) (fun i=>lifted Ψ (W i) (Station.choose (Lev) ξ.band k x i) k wide) x ξ:=by
  refine ⟨?_,?_,?_,?_⟩
  · intro i; rw [primeVisit]; exact (expend ..).trans (price i)
  · intro i; rw [primeVisit]; exact (totalDegree_rename_le ..).trans (deg i)
  · intro i; rw [primeVisit]; exact poetry _ (spin i) _ _
  intro i f hf
  rw [primeVisit] at hf
  obtain ⟨j,hj,rfl⟩:=mem_vars_rename _ _ hf
  let w:=Station.choose (Lev) ξ.band k x i
  change separation (core (Lev) x ξ.band p (show k≤k from le_rfl) i)
    (wrap (C.side k p) (w+j.1.val.1)) ≤ sizeQ C k
  rw [homeHere,map_add,add_comm];exact Work.E08.separation_box_add _ (faceOrigin _)

private theorem signet_shift {o:Side} {b:ℕ} (x:Site o) (g:ℝ) (W:poly (slotC G b)) (U:Config G o):
    signet x g W U=signet 0 g W (pull 1 x U):=by
  unfold signet Spindle.curl registered;rw [s_translation]

theorem singleton (x:Points n) (wide:4*sizeQ C k≤wood (Lev) k) (W:Fin n→poly (slotC G (sizeQ C k)))
    (gift:Ceremony ξ c P R Ψ) (i:(Ship.yard C ξ.band c.allow p).Cell) (j:Fin n) (g:ℝ) (U:Config G (C.side k p)):
    let X:=fun t=>lifted Ψ (W t) (Station.choose (Lev) ξ.band k x t) k wide
    let t:=solitaire x j ξ p k (Lev)
    gloryFt (C:=C) x ξ.band p c.allow le_rfl (before (Lev) ξ.band k) i t.val g (vista R X le_rfl t.val.val) U =
      dot ((Ship.yard C ξ.band c.allow p).hand i)
        (signet 0 g (W j) (pull ((Ship.yard C ξ.band c.allow p).omega i) (seats C ξ.band x c.allow p (i,j)) U)):=by
  intro X t
  let T:=Ship.yard C ξ.band c.allow p
  let h:middle (Lev) ξ.band k≤k:=before ..
  let a:=(Station.wider (Lev) ξ.band k).trans h
  let z:=wrap (C.side k p) (Station.choose (Lev) ξ.band k x j)
  have hs:seats C ξ.band x c.allow p (i,j)=affine (T.omega i) (spreadC C ξ.band p a i) z:=by
    let y:=core (Lev) x ξ.band p (k:=k) le_rfl j
    have e:y=z:=homeHere ..
    rw [←e];exact fills C x ξ.band p c.allow le_rfl a _
  have hp:8≤ξ.era.coast.Q:=by linarith only [gift.sens.canvas.radius]
  have room:2*(sizeQ C k+1)<(C.side k p).val:=by
    exact lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_right _ hp) _)) (gift.sens.canvas.suite k h le_rfl)
  simp only [gloryFt,Function.comp_apply]
  rw [x_head x j (C:=C),show t.val.val=Next.Rank.Glyph.slot j from rfl,x_cept (C:=C) (R:=R) X j]
  rw [show core (Lev) x ξ.band p le_rfl j=z from homeHere ..]
  change dot _ (caseW (lifted Ψ (W j) (Station.choose (Lev) ξ.band k x j) k wide) z g _) = _
  rw [caseK _ _ _ _ _ _ _ room,signet_shift z, watches,pull_pull,mul_one,hs]
end YM.Integration.WilsonAddressedWeakNativePolynomials
end
