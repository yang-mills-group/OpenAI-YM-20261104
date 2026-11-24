import YM.Integration.WilsonOlderFreshSoftSocketGeometry

/-! An identity of two finite rooted gauge word sums on every finite group field determines the entire unsuspended geometric input, including its cover tensor at rank zero. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketWard
open Function Finset Lattice Laurent Wilson RG Precision Tree Exterior Bloch Matrix PowerSeries
open PhysicalNext.Repeat.Legato FreeResolvent WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Motion WilsonCoeffUV.Embroider WilsonCoeffUV.Soil Stationary WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank.Mosaic.Near
open OriginalMarkedSourceComet IndependentSourcePathFamily
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner

open private current_invariant from YM.Integration.OriginalMarkedSourceComet
variable {G:Gauge}{r:ℕ}
def mark (A:RG.Atom G r):Era G ℝ:=volumeR (current A (1:ℝ)) r
private theorem entry (A:RG.Atom G r)(n:Side)(e a:ℕ)(v:Fin a→Woods G n):
    (mark A).1 n e a v=if e=a then rye (meter A (0:Site n)) a v else 0:=by
  have view (j:ℕ)(x:Fin j→Woods G n):
      sapR (current A (1:ℝ)) n j x=rye (meter A (0:Site n)) j x:=by
    have eq:Mer.Rolls.dip (current A (1:ℝ)) (ContinuousLinearMap.id ℝ ℝ)=A:=by
      cases A with
      | mk leg coeff =>
        change RG.Atom.mk leg (fun j=>coeff j*1)=RG.Atom.mk leg coeff
        simp
    simpa only [eq,ContinuousLinearMap.id_apply] using
      (sap_view (current A (1:ℝ)) n j x (ContinuousLinearMap.id ℝ ℝ))
  change moved r r (sapR (current A (1:ℝ)) n) e a v=_
  by_cases he:r≤e
  · have h:r+(e-r)=e:=by omega
    rw [moved,if_pos he]
    have lit:=congrArg (fun k=>Blue.shine (sapR (current A (1:ℝ)) n k)) h
    rw [lit]
    by_cases ha:e=a
    · subst a;rw [if_pos rfl,Blue.shine_lit,view]
    · rw [if_neg ha,Blue.shine_dark ha];rfl
  · by_cases ha:e=a
    · subst a
      have hm:=(rays_jet ((meter_hot A (0:Site n)).contDiffAt (x:=0)).analyticAt r).mp
        (meter_shell A (0:Site n)) e (by omega)
      simp [moved,he,rye,hm]
    · simp [moved,he,ha]

private theorem funded {ι:Type}[Fintype ι]{grade:ι→ℕ}(A:(a:ι)→RG.Atom G (grade a))
    (c:ι→ℝ)(inv:∀ j,(A j).Invariant):Auth 0 (∑j,c j • mark (A j)):=by
  apply Auth.sum
  intro j _
  have h:=aug_auth (current (A j) (1:ℝ)) (current_invariant _ (inv j) _) (k:=0) (e:=grade j) (by omega)
  exact h.tuft ((c j) • ContinuousLinearMap.id ℝ ℝ)

private theorem finite {ι:Type}[Fintype ι]{grade:ι→ℕ}(A:(a:ι)→RG.Atom G (grade a))
    (c:ι→ℝ)(n:Side)(e a:ℕ)(v:Fin a→Woods G n):
    (∑j,c j • mark (A j)).1 n e a v=if e=a then
      rye (∑j,c j • meter (A j) (0:Site n)) a v else 0:=by
  simp only [Prod.fst_sum,Prod.smul_fst,Finset.sum_apply,Pi.smul_apply,entry]
  by_cases ea:e=a
  · simp only [if_pos ea]
    have hj (j:ι):Green (c j • meter (A j) (0:Site n)):=(meter_hot (A j) (0:Site n)).contDiffAt.const_smul (c j)
    rw [rye_scoped (W:=fun j=>c j • meter (A j) (0:Site n)) (fun j _=>hj j),Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    unfold rye
    rw [show _ from iteratedFDeriv_const_smul_apply (x:=0) (a:=c j)
      ((meter_hot (A j) (0:Site n)).contDiffAt.of_le (le_top (a:=((a:WithTop ℕ∞)))))]
    rw [_root_.smul_apply]
    simp only [smul_eq_mul]
    ring
  · simp [ea]

theorem original {ι μ:Type}[Fintype ι][Fintype μ]{p:ι→ℕ}{q:μ→ℕ}
    (A:(a:ι)→RG.Atom G (p a))(B:(b:μ)→RG.Atom G (q b))(c:ι→ℝ)(d:μ→ℝ)
    (paid:∀a,(A a).Invariant)(book:∀b,(B b).Invariant)
    (fields:∀(n:Side)(U:Config G n),
      (∑a,c a*(A a).unmasked U 0)=∑b,d b*(B b).unmasked U 0):
    (∑a,c a • mark (A a))=∑b,d b • mark (B b):=by
  apply Auth.ext (funded A c paid) (funded B d book)
  funext n e r v
  rw [finite,finite]
  have bound:(∑a,c a • meter (A a) (0:Site n))=∑b,d b • meter (B b) (0:Site n):=by
    funext z
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    exact fields n (input G n z)
  rw [bound]

end YM.Integration.WilsonOlderFreshSoftSocketWard
end
