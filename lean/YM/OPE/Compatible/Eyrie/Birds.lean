import YM.OPE.Compatible.Eyrie.Dell
import YM.MergeProof.Figment
/-! # Costed discrepancies at actual intermediate levels -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Eyrie
open Function Filter MeasureTheory Lattice Wilson RG Source Labels Bid Spec
open PathData Extra.Histories MergeProof MergeProof.Accent Owl
open scoped Topology Classical BigOperators
variable {G:Gauge}{d k m N p:ℕ} {C:Family G}(M:C.Makes)
variable (F: lots G (C.side N p))(a:C.label d) (B:ℕ→ℕ→ ℝ)
local notation "X!"=> C.factory d N p
include M
lemma rootE (hk:k ≤ N)(ht:C.ref d≤k):
     puff C.path N p d (C.O N p a 0) hk=((X!).entries k ((X!).terminal.symm a)).density 0 (C.localSection d) (C.path.rep N p k):=by
         induction hk using Nat.decreasingInduction with
         | self=>
             simp only [puff,Push.GridApprox.pushTo_self]; ext V; rw [(M.calibrated d N p ht).encode, (M.wilson.starts N p).2]; simp only [Pi.smul_apply,illum, smul_eq_mul,mul_assoc]; rfl
         | of_succ k hk ih=> rw[(M.calibrated d N p (ht.trans hk.le)).unnormalized k ht hk,PuffS C.path hk (C.O N p a 0) (C.continuousO ..), ih (ht.trans (Nat.le_succ k))]; rfl
lemma Ecost (p:ℕ)(ht:C.ref d≤ k)(hk:k ≤ N)(a:C.label d):
     ((Stepm M ht hk p (Lake.tallyman M d k (N,p) a))).density 0 (C.localSection d) (C.path.rep N p k)=puff C.path N p d (C.O N p a 0) hk:=by
         rw[rootE M a hk ht]; change ((C.factory d N p).entries _ ((C.factory d N p).terminal.symm ((Pinwheel M ht hk p).symm ((Pinwheel M ht hk p) a)))).density 0 _ _= _ -- notation X!
         rw [ContinuousLinearEquiv.symm_apply_apply]
end YM.OPE.Eyrie
