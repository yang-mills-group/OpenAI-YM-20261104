import YM.XSpace.Soles
import YM.XSpace.Charge

/-!
# Maxwell on-shell jets on the lattice via harmonic potential modes

Use the slightly larger on-shell potential space: ONLY K A=0, not harmonic in the
coordinatewise Laplacian. Enough since the local Ward identity uses just that equation.
Computations on dip and feed in adjacent dimensions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Scale
open Lattice Litter Maxwell Maxwell.Free Tensor Sail Further.FreeCovariance.KP Analysis Filter Function Set
open scoped Topology BigOperators ContDiff
variable {F:Type*}[NormedAddCommGroup F][NormedSpace ℝ F]{G:Gauge}{d k:ℕ}
abbrev Tape (F:Type*) := Edge Cover → F
def twig (i:Axis) : Tape F →ₗ[ℝ] (Cover→F):=LinearMap.pi fun x=> LinearMap.proj (x,i)
def rat (i:Axis): Module.End ℝ (Cover→F):= LinearMap.pi (R:=ℝ) fun x:Cover=> LinearMap.proj (x-step i)-(LinearMap.proj x:(Cover→F)→ₗ[ℝ]F)
lemma rat_step (i:Axis)(p: Cover→F)(x:Cover): rat i p x= -(teeth i p (x-step i)):=by change p (x-step i)-p x=-(p (x-step i + step i)-p (x-step i)); rw [sub_add_cancel,neg_sub]
lemma pop_back (A:Stamp (d+1) F)(x:Cover)(i:Axis)(v:E4):rat i (feed (v+half i) A) x= -feed v (dip i A) x:=by
  rw [rat_step,show teeth i (feed (v+half i) A) (x-step i)=_ from feed_one ..]; congr 1
  change board _ _= board _ _; congr 1; have he:= rcast_step_add (x-step i) i; rw [sub_add_cancel,← twice] at he; rw [he]; apply congr_arg board; abel
lemma rat_const (i:Axis)(A:Stamp 0 F)(v:E4): rat i (feed v A)=0:= funext fun x=>by rw [rat_step,show teeth i (feed v A) =_ from feed_const ..]; show -(0:F)=0; exact neg_zero

def crackle (i j: Axis): Tape F→ₗ[ℝ] (Cover→F):= teeth i ∘ₗ twig j - teeth j ∘ₗ twig i
lemma crackle_ap (i j:Axis)(A:Tape F)(x:Cover): crackle i j A x = A (x+step i,j)-A (x,j)-(A (x+step j,i)-A (x,i)):=rfl
lemma plot (i j:Axis)(h:i < j)(x:Cover)(A:Tape G.Color): crackle i j A x= Chart2.linearFace (G:=G) (x,⟨(i,j),h⟩) A:=by rw [Chart2.angular,crackle_ap]; simp only; abel
def press: Module.End ℝ (Tape F):= LinearMap.pi fun x:Edge Cover=> LinearMap.proj x.1 ∘ₗ ∑ i:Axis, rat i ∘ₗ crackle i x.2
lemma job (A:Tape F)(i:Axis):twig i (press A)=∑ j:Axis,rat j (crackle j i A):=by funext x; change (∑ j:Axis,rat j ∘ₗ crackle j i) A x = _; rw [LinearMap.sum_apply]; rfl
lemma fare {A:Tape F}:press A=0↔∀ i,twig i (press A)=0:= ⟨fun h i=> by rw [h,map_zero],fun h=> funext fun i=> congr_fun (h i.2) i.1⟩

abbrev Vase (d:ℕ)(F:Type*) [NormedAddCommGroup F][NormedSpace ℝ F] := Axis→ Stamp d F
def release: Vase d F →ₗ[ℝ] Tape F:= LinearMap.pi fun x:Edge Cover=> LinearMap.proj x.1 ∘ₗ feed (half x.2) ∘ₗ LinearMap.proj x.2
def pair (i j:Axis): Vase (d+1) F →ₗ[ℝ] Stamp d F:= dip i ∘ₗ LinearMap.proj j - dip j ∘ₗ LinearMap.proj i
lemma sounds (v:Vase (d+1) F)(i j:Axis): crackle i j (release v)=feed (half i+half j) (pair i j v):=by
  change Δf i (feed (half j) (v j))- Δf j (feed (half i) (v i))= feed _ (dip i (v j)-dip j (v i))
  rw [map_sub]; congr 1; rw [funext fun x=>feed_one x i (half j) (v j),add_comm]; exact funext fun x=> feed_one x j _ _
def discord (i : Axis): Vase (d+1+1) F →ₗ[ℝ] Stamp d F:=∑ j:Axis, dip j ∘ₗ pair j i
lemma string (v:Vase (d+1+1) F)(i:Axis): twig i (press (release v))= -feed (half i) (discord i v):=by
  unfold discord; rw [job,LinearMap.sum_apply,map_sum,← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro j _; rw [sounds,add_comm (half j)]; exact funext fun x=>pop_back ..
def motif (d:ℕ)(F:Type*) [NormedAddCommGroup F][NormedSpace ℝ F] : Submodule ℝ (Vase d F) := LinearMap.ker (press ∘ₗ release)
abbrev Tune (d:ℕ)(F:Type*)[NormedAddCommGroup F][NormedSpace ℝ F]:= ↥(motif d F)
lemma harmony (v:Vase (d+1+1) F): v ∈ motif (d+1+1) F↔∀ i,discord i v=0:=by
  change press (release v)=0↔_; rw [fare]; simp_rw [string,neg_eq_zero]; apply forall_congr'; intro a; rw [map_eq_zero_iff _ (once_hard _)]
lemma soundless (v:Vase 0 F)(i j): crackle i j (release v)=0:=by
  change Δf i (feed (half j) (v j))- Δf j (feed (half i) (v i))= _; rw [feed_const,feed_const,sub_self]
lemma origin (v:Vase 0 F): v ∈ motif 0 F:= fare.mpr (fun i=>by simp [job,soundless])
lemma start (v:Vase 1 F): v ∈ motif 1 F:= fare.mpr (fun i=> by simp [job,sounds,rat_const])

-- curl affine to the actual free jet space

def tune (i:Axis)(v:Tune d F) : Stamp d F:= v.val i
def motifValue (A:Stamp d F):=Tensor.diagonal A.val
lemma motif_zero: motifValue (0:Stamp d F)=0:=rfl
lemma motif_inj : Injective (motifValue (d:=d) (F:=F)):=fun x y h=> Subtype.ext (ext_diag _ _ x.property y.property h)
lemma climbs (v:Stamp (d+1) F)(i:Axis)(x:E4): grad i (motifValue v) x =motifValue (dip i v) x:=by
  change fderiv ℝ (Tensor.diagonal v.val) x (basis i)= ((d+1:ℕ):ℝ) • _; rw [differential_diagonal _ v.property,Nat.cast_smul_eq_nsmul]; rfl
lemma plane (i:Axis)(v:Stamp 0 F)(x:E4): grad i (motifValue v) x=0:=by rw [show motifValue v=fun _=> v.val 0 from funext fun _=> congr_arg v.val (Subsingleton.elim ..)]; simp [grad,D]
def text (x:E4): Stamp d F→ₗ[ℝ] F:= (ContinuousMultilinearMap.apply ℝ _ F (fun _=>x)).toLinearMap ∘ₗ (stamps F d).subtype
lemma motif_pop (A:Stamp d F)(x:E4): motifValue A x=text x A:=rfl
def draw : Vase (d+1) F →ₗ[ℝ] (TwoJet F d):= LinearMap.pi fun i=> LinearMap.pi fun j=> (stamps F d).subtype ∘ₗ pair i j
lemma readValue (v:Vase (d+1) F)(i j:Axis): Tensor.diagonal (draw v i j)= grad i (motifValue (v j)) - grad j (motifValue (v i)):= by funext x; rw [Pi.sub_apply,climbs,climbs]; rfl
lemma draw_closed (v:Vase (d+1) F): ClosedJet (draw v):=by
  constructor
  · intro i j; exact (pair i j v).property
  · intro i j; apply congr_arg Subtype.val (show pair i j v= -pair j i v from (neg_sub ..).symm)
  intro i j k x
  have hd (i:Axis)(l :ℕ∞ω)(x:E4): ContDiffAt ℝ l (motifValue (v i)) x:= (diag_smooth _ _).contDiffAt
  have he (i j):DifferentiableAt ℝ (grad i (motifValue (v j))) x := (grad_smooth i (m:=∞) (hd j ∞ x) (by simp)).differentiableAt (by simp)
  have hh (i j k): grad i (Tensor.diagonal (draw v j k)) x= grad i (grad j (motifValue (v k))) x-grad i (grad k (motifValue (v j))) x:=by rw [readValue]; change fderiv ℝ (_ - _) _ _=_; rw [fderiv_sub (he j k) (he k j)]; rfl
  rw [hh i j k,hh j k i,hh k i j]; nth_rw 1 [grad_comm (hd k 2 x) i j]; nth_rw 1 [grad_comm (hd j 2 x) i k]; nth_rw 1 [grad_comm (hd i 2 x) j k]; abel
lemma drawn (v:Vase (d+1) F): draw v ∈ onShell F d↔ v∈motif (d+1) F:=by
  change (_∧_) ↔_; rw [and_iff_right (show draw v∈ formSpace d F from draw_closed v)]; cases d with
  | zero=> exact iff_of_true (fun i x=> Finset.sum_eq_zero fun j _=> plane j (pair j i v) x) (start v)
  | succ d=>
    have he (i:Axis)(x:E4): (∑ j:Axis,grad j (Tensor.diagonal (draw v j i)) x) =motifValue (discord i v) x:=by unfold discord; rw [motif_pop,LinearMap.sum_apply,map_sum]; exact Finset.sum_congr rfl fun j _=>climbs (pair j i v) j x
    simp_rw [he,harmony]; exact ⟨fun h i=> motif_inj (funext (h i)),fun h i x=>h i ▸ rfl⟩

def ink : Tune (d+1) F →ₗ[ℝ] Solution F d:= (draw ∘ₗ (motif _ F).subtype).codRestrict _ fun x=> (drawn x.val).mpr x.property

def fit (A:Labels.Taylor G d): Vase (d+1) G.Color:=fun i=> ⟨A.val i,A.property.1 i⟩
lemma fit_draw (A:Labels.Taylor G d) : draw (fit A)=takeCurl A:= by funext i j; change ((d+1:ℕ):ℝ) • (A.val j).curryLeft (basis i)- ((d+1:ℕ):ℝ) • (A.val i).curryLeft (basis j) = _; rw [takeCurl, smul_sub]

def roll : Shell G d →ₗ[ℝ] Tune (d+1) G.Color where
  toFun A:= ⟨fit (gaugeJet A),(drawn _).1 (by rw [fit_draw,match_leg]; exact A.property)⟩
  map_add' A B:= by apply Subtype.ext; ext1 i; apply Subtype.ext; exact congr_arg (fun A:Labels.Taylor G d=> A.val i) (map_add gaugeJet A B)
  map_smul' a A:= by apply Subtype.ext; ext1 i; apply Subtype.ext; exact congr_arg (fun A:Labels.Taylor G d=> A.val i) (map_smul gaugeJet a A)
lemma inks (A:Shell G d): ink (roll A)=A:= Subtype.ext ((fit_draw _).trans (match_leg A))
end YM.XSpace.Scale
