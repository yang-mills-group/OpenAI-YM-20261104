import YangMills.WilsonProof.NativeSupport.YM.MS.Local.Harmony
/-!
# Idempotentization of local homotopy

Project primitive pairs before forming symmetric symbol products.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Local.BV
open Function Filter Set Finset Plane Koszul Real Momentum Wire Tensor Submodule MatrixLet
open Landau Detect
open Complex (I)
open scoped Topology ContDiff
variable {G: Gauge} {f : Grade G} {h q d k : ℤ}

def joint (A : Baton G): Baton G:= Q.comp A + A.comp Q
@[simp] lemma joint_at (A:Baton G) f : joint A f= Q (A f) + A (Q f):= rfl
structure Pairing (A : Baton G) (k : ℤ) : Prop where
   price h q (u:Grade G) (hp:h≤k): u∈yields h q → A u∈yields h (q-1)
   double h q (u:Grade G) (hp:h≤k): u∈yields h q → Q (A (Q u))= Q u
structure Calib (A : Baton G) (k:ℤ) extends Pairing A k where
   lights h q u (hp:h≤k): u∈yields h q → joint A (joint A u) = joint A u
variable {D : Baton G} (X : Pairing D k)
namespace Pairing

include X
lemma spectrum (hp:h≤k) (he:f∈ yields h q) : joint D f∈yields h q:= by
   rw [joint_at]; apply add_mem
   · simpa using stays _ _ _ (X.price h q _ hp he)
   simpa using X.price h (q+1) _ hp (stays _ _ _ he)
lemma exact_q (hp:h≤k) (he:f∈ yields h q) : Q (joint D f)=Q f:= by rw [joint_at,map_add, Q_zero, X.double _ _ _ hp he, zero_add]
lemma exact_s (hp:h≤k) (he:f∈ yields h q): joint D (Q f)=Q f:= by rw [joint_at, Q_zero, map_zero,X.double _ _ _ hp he,add_zero]

omit X
-- correct non-diagonal term when D is not a strict pair homotopy
variable (D)
def calibrate : Baton G := D-(D.comp D).comp Q
def defect : Baton G := (Q.comp D).comp (D.comp Q)
lemma calibrate_at (f : Grade G) : calibrate D f=D f - D (D (Q f)):= rfl
lemma defect_at (f : Grade G): defect D f= Q (D (D (Q f))):= rfl
variable {D}
-- uniform within cap. Need for idempotization.
include X
lemma vPrice (hx : h≤ k) (he:f∈ yields h q) : D (D (Q f))∈ yields h (q-1):= X.price h q _ hx (by simpa using X.price h (q+1) _ hx (stays _ _ _ he))
lemma v_l (hx : h≤ k) (he:f∈ yields h q): joint D (defect D f)=defect D f:= X.exact_s hx (X.vPrice hx he)
lemma v_r (hx : h≤k) (he:f∈ yields h q): defect D (joint D f)=defect D f:= by rw [defect_at, X.exact_q hx he]; rfl
omit X in
lemma v_v (D : Baton G) (f:Grade G): defect D (defect D f)=0:= by rw [defect_at,defect_at,Q_zero,map_zero,map_zero,map_zero]
lemma pwr (hx:h≤k) (he:f∈ yields h q) : joint D (joint D f)=joint D f + defect D f:= by
   rw [joint_at, X.exact_q hx he]; simp only [joint_at,map_add, X.double h (q-1) _ hx (X.price h q _ hx he), defect_at]; abel
omit X in
lemma corrected (D:Baton G) f: joint (calibrate D) f=joint D f-defect D f:= by rw [joint_at, joint_at, calibrate_at,calibrate_at,defect_at, Q_zero,map_zero,map_zero,map_sub]; abel

lemma solves : Calib (calibrate D) k where
   price h q u hx he:= (yields h (q-1)).sub_mem (X.price h q u hx he) (X.vPrice hx he)
   double h q u hx he:= by rw [calibrate_at,Q_zero,map_zero,map_zero,sub_zero,X.double _ _ _ hx he]
   lights h q u hx he:= by rw [corrected,corrected,map_sub (joint D),map_sub (defect D),X.v_l hx he,X.v_r hx he,v_v,X.pwr hx he]; abel
end Pairing
lemma Calib.annul {D:Baton G} (X:Calib D k) (hf : f∈yields h q) (hx:h≤k) (hq:q<0): joint D f=f:= by
   set g:=f-joint D f; have he:g∈yields h q:= sub_mem hf (X.spectrum hx hf); have hv : Q g=0:= by simp only [g,map_sub,X.exact_q hx hf,sub_self] -- simp rewrite joint first
   obtain ⟨p,hp,hH⟩:= negative he hq hv
   have hu : joint D g=g:= hH ▸ X.exact_s hx hp
   unfold g at hu; rw [map_sub,X.lights _ _ _ hx hf,sub_self] at hu; exact (sub_eq_zero.mp hu.symm).symm
lemma tune (G : Gauge) (k:ℤ) : ∃ A:Baton G, Calib A k := by
    obtain ⟨A,hA⟩:= full_inv G k
    have ht : Pairing A k:= ⟨fun h q u he hu => (hA h he q u hu).1, fun h q u he hu=>(hA h he q u hu).2⟩
    exact ⟨ _, ht.solves⟩
end YM.MS.Local.BV
