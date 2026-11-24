import YM.OPE.Compatible.Ingle.Stamp
import YM.OPE.Compatible.Chest.Balls
import YM.OPE.Compatible.Hull.Daisy
import YM.OPE.Compatible.Tune.Theta
import YM.OPE.Compatible.Tune.Race
import YM.OPE.Compatible.Cant.Cadre
import YM.OPE.Compatible.Cant.Wiz
import YM.OPE.Compatible.Cant.View
import YM.OPE.Compatible.Cant.Nob
import YM.OPE.Compatible.Cant.Past
import YM.OPE.Compatible.Cant.Void
import YM.OPE.Compatible.Cant.Fat
/-!
# The kernel and a right inverse of the graded reading

`Folt` collects the phase-zero readings through degree `l` into `Folio`.
`folThrough` identifies its kernel with `tLead`, and `folLive` proves surjectivity
by prescribing the readings one degree at a time. `FolU` is the resulting
continuous linear right inverse, with `fLay` giving the identity on `Folio`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stroke
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
open Quit.PriceZ Quit.Jac Quit Hark Topic StageLight
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {v v' b u:ℝ}
variable {K:Sponsor G}{P:Patch}
abbrev Folio (G:Gauge)(d:ℕ):= (j:Fin (d+1))→ Bead G d j.val
section
variable (D:Stern K P τ l d v)
-- 0 channel
noncomputable def Folt : bed G d (τ 0)→L[ℝ] Folio G l:= ContinuousLinearMap.pi (fun i:Fin (l+1)=> stepRead G l i.val d (τ 0) ((Nat.le_of_lt_succ i.isLt).trans (sternCap D 0).le))
lemma folThrough (x:bed G d (τ 0)): Folt D x=0 ↔ x∈ tLead D:=by
       let n:= τ 0; have hl:= sternCap D 0; let f:= Folt D; have hp:= decrement (h:=Nat.add_le_add_right hl.le 1) x 
       constructor
       · intro h; have hu(y:ℕ)(hy:y ≤ l+1): x∈ fillet G d (τ 0) y (by omega):=by
                   induction y with| zero=>exact dawn x| succ i ih=> exact (slogan (d:=l) (by omega) (by omega) x (ih (by omega))).mp (congr_fun h (⟨i,by omega⟩:Fin (l+1)))
         exact hu _ le_rfl
       intro h; funext i; change stepRead G l i.val d (τ 0) (by omega) x=0; exact (slogan (by omega) (by omega) x (prev x (by omega) h)).mpr (prev x (by omega) h)
lemma folLive : Surjective (Folt D):=by
       intro p; have he:=sternCap D 0
       have hp (s:ℕ)(h:s ≤ l+1):∃ x:bed G d (τ 0),∀ i:Fin (l+1), i.val < s→ Folt D x i=p i:=by
              induction s with
              | zero=> exact ⟨0,fun _ hi=>by omega⟩
              | succ s ih=> obtain ⟨q,hq⟩:=ih (by omega); let i:Fin (l+1):=⟨s,h⟩; obtain ⟨x,hx,hh⟩:= Drift.obtains l (show i.val ≤ τ 0 by omega) ((Nat.le_of_lt_succ i.isLt).trans D.mark) (p i-Folt D q i); refine ⟨q+x,fun j hj=>?_⟩; rw [map_add, Pi.add_apply]; by_cases hv:j=i
                            · subst j; rw [show Folt D x i=_ from (show Folt D x i=p i-Folt D q i from hh)]; abel
                            have ht:j.val<s:=lt_of_le_of_ne (Nat.le_of_lt_succ hj) (fun h=>hv (Fin.ext h)); rw [hq _ ht]; rw [show Folt D x j= 0 from (slogan (e:=j.val) (d:=l) (by omega) (by omega) x (prev x ht.le hx)).mpr (prev x ht hx),add_zero]
       obtain ⟨x,hx⟩:=hp _ (le_refl _); exact ⟨x,funext fun i=>hx i i.isLt⟩
lemma fLift : ∃ f:Folio G l→L[ℝ] bed G d (τ 0), ∀ x,Folt D (f x)=x:=by
       let f:=Folt D; have hp: LinearMap.range f.toLinearMap=⊤:= LinearMap.range_eq_top.mpr (folLive D); obtain ⟨g,hg⟩:= LinearMap.exists_rightInverse_of_surjective f.toLinearMap hp; refine ⟨g.toContinuousLinearMap,fun x=>?_⟩; exact LinearMap.congr_fun hg x
noncomputable def FolU :=(fLift D).choose
lemma fLay (x:Folio G l):Folt D (FolU D x)=x:=(fLift D).choose_spec x
-- Phase-zero coordinates of the inverse frame map.
lemma LapΩ (v:solar G d τ)(u:Train r)(h:4 ≤ r): (((Fallix G D.aware K u h).symm v) (0:Phase)).val=boostS (atlasF G u h K.K) (1/2) (τ 0) d (v.val 0):=by
        let a:= (Fallix G D.aware K u h).symm v; have he :v.val=(Fallix G D.aware K u h a).val:= (congr_arg Subtype.val ((Fallix G D.aware K u h).apply_symm_apply v)).symm; rw [show v.val 0=_ from congr_fun he _, show (Fallix G D.aware K u h a).val 0=_ from (starMark D.aware a u h 0 (fun i hi=> by change i.val<0 at hi;omega)).2]; exact (sustain (1/2) (atlasF G u h K.K) (τ 0) d (a (0:Phase)).val).symm
end
end YM.OPE.Stroke
