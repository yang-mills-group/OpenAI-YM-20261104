import YM.RG3.Annuncia.Replica
import YM.RG3.Alpes.Firma
import YM.MergeProof.Accent
/-!
# Hom commutes with pass & true force field, continuum line norm.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Annuncia.Replica
open Function Filter Finset YM.Marker Lattice RG Wilson MergeProof MergeProof.Accent
open scoped Matrix.Norms.Frobenius ContDiff BigOperators Topology Classical
variable {V W:Type*}[DecidableEq V][Fintype W][DecidableEq W](u:W→V)(R:Census V)(γ:W→ℂ)
local notation "S"=> Replica u R
lemma quota(a:Poly S)(i:R.Mode): (mouth u R γ a).part i=∑ j:(S).Mode,if bill u R j=i then sign u R γ j*a.part j else 0:=by
 rw [mouth_apply,absorb,Poly.part_sum]; exact sum_congr rfl (fun _ _=>by simp [Poly.part_send,eq_comm])
lemma quiet (a:Poly S):(mouth u R γ a).part R.quiet=a.part ((S).quiet):=by
 rw [quota]; simp_rw [hot u R]; simp [sign,Census.quiet]
lemma csmul (a:Poly S)(r:ℂ): mouth u R γ (r•a)=r•mouth u R γ a:=toScalar ..
lemma single (x:ℂ):mouth u R γ (Poly.send (S).quiet x)=Poly.send R.quiet x:=by rw [mouth_apply,puts,blank]; simp [sign,Census.quiet]
def pipe : Poly S →ₗ[ℂ] Poly R where
  toFun:= mouth u R γ
  map_smul' :=fun c x=> csmul u R γ x c
  map_add':=map_add _
def cable : Poly S →L[ℂ] Poly R:=LinearMap.toContinuousLinearMap (pipe u R γ)
@[simp] lemma cable_apply (a):cable u R γ a=mouth u R γ a:= rfl

variable [Fintype V]
lemma passed (a: Poly S)(h:a.part ((S).quiet)=0): mouth u R γ (Poly.pass a)= Poly.pass (mouth u R γ a):=by
 unfold Poly.pass; rw [_root_.map_sum]; simp_rw [csmul,map_pow]
 rcases le_total (Fintype.card W) (Fintype.card V) with H|H
 · refine sum_subset (range_mono (by omega)) ?_; intro i _ he; rw [←map_pow, Poly.stops a h i (by simp only [mem_range,not_lt] at he; omega), map_zero, smul_zero]
 symm; refine sum_subset (range_mono (by omega)) ?_; intro i _ he; rw [Poly.stops _ (quiet u R γ a|>.trans h) i (by simp only [mem_range,not_lt] at he; omega),smul_zero]
variable {n:Side}
omit [Fintype V] in
lemma estate (d:Box n→Poly S)(s:Support n): mouth u R γ (field d s)=field (mouth u R γ ∘ d) s:=by
 unfold field; rw [_root_.map_sum]; refine sum_congr rfl (fun i _=>?_); unfold grid; split; simp; exact _root_.map_zero _
end YM.RG3.Annuncia.Replica
