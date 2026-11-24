import YM.FormalOPE.RG10.Profile.Permute
import YM.MergeProof.East.Glaze
import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.Clover
import YM.Further.CURVED_GAUSSIAN_JETS.Mirrors

/-! # Signed covariance of the unrestricted finite-torus unit-weight curl
Geometric derivative read adapted to *before* the inversion quotient. Used to check the top
calibration as periods expand. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Spiral
open Function Wilson Lattice Gauge Precision Exterior Work.F03 Further.CorrectedLift.Compass
   PertExtension Filter RG PertExtension.LatticePT LatticePT.Projection Finset
open Further.CurvedGaussianJets.Shape AnalyticBridge.CouplingShape
open scoped Topology ContDiff BigOperators Classical RealInnerProductSpace
variable {G:Gauge}{n : Side}
lemma orientedSum (G : Gauge){R:Type*}[AddCommGroup R][One R](A:Links R G.Color)(x:Four R)(i j:Axis):
    Exterior.linkSum A x (square i j)= A (x,i)+A (x+ Lattice.step i,j)-A (x+Lattice.step j,i)-A (x,j) := by
  simp [square,linkSum,posDir,negDir,Step.used,Step.vec,show x+Lattice.step i+Lattice.step j-Lattice.step i=x+Lattice.step j by abel,←sub_eq_add_neg]; abel
lemma rawCoil (v:Bid.Dir G n)(p:FaceAt n) : faceCurl p v= crease G (Exterior.collect G v) p:= Eq.trans (Exterior.fundamental _ v ..).symm (orientedSum G ..)
lemma face_here (a: Slot): slotFace a (0:Site n)= Converter.position n a:= Prod.ext (add_zero _) rfl

variable (s:Signed)
def permutation : Equiv.Perm (FaceAt n) := Equiv.ofBijective (Face.send s (0:Site n)) ⟨Face.injective_send ..,Finite.injective_iff_surjective.mp (Face.injective_send ..)⟩
lemma sent (G : Gauge)(z:Slot): Converter.position n (bend G s z)=permutation s (Converter.position n z):= (Further.CorrectedLift.Compass.stamp (G:=G) z s).choose_spec.2.2 n
lemma initializes {x:FaceAt n}: ∃ s:Slot,Converter.position n s=x := by
 use ⟨Next.Rank.Spindle.paths (lift x.1),x.2⟩; refine Prod.ext ?_ rfl; change wrap _ (stop (0: Cover) (Next.Rank.Spindle.paths (lift x.1)))=_; rw [Next.Rank.Spindle.stops,wrap_lift]

lemma pulled (A:Bid.Dir G n)(p:FaceAt n):faceCurl p (Bid.pulled A s) = wind s p.2 • faceCurl (permutation s p) A := by
 obtain ⟨a,rfl⟩:= initializes (x:=p)
 have he (t:ℝ): a.atSite (represent (t • Bid.pulled A s)) 0 = wind s a.plaq • (bend G s a).atSite (represent (t • A)) 0 := by rw [← pulled_smul,← pull_flat, pocket]
 have ht:= slot_deriv a 0 (Bid.pulled A s); simp_rw [he,face_here] at ht; rw [← sent s G]; apply ht.unique; have hv:= slot_deriv (bend G s a) 0 A; rw [face_here] at hv; exact hv.const_smul (wind s a.plaq)
lemma roundTrip (A:Bid.Dir G n)(p:FaceAt n): faceCurl p (Bid.pulled (Bid.pulled A s⁻¹) s) = faceCurl p A := by
 obtain ⟨a,rfl⟩:= initializes (x:=p)
 have he (t:ℝ): (represent (t • Bid.pulled (Bid.pulled A s⁻¹) s)) = represent (t • A):= by rw [← pulled_smul,←pull_flat, ← pulled_smul,←pull_flat,pull_pull]; simp [affine]
 have ht:= slot_deriv a 0 (Bid.pulled (Bid.pulled A s⁻¹) s); rw [←face_here]; simp_rw [he] at ht; exact ht.unique (slot_deriv ..)
end YM.FormalOPE.RG10.Spiral
