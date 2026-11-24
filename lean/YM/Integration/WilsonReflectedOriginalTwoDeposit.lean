import YM.Integration.ActualWilsonAbsoluteTransport
import YM.Push.RELAY_DIFFERENCE.Placement
import YM.Integration.WilsonCapturedSoldDeckPlacement

/-! The first common deposit of two oriented original cutoff fields on their actual Wilson history. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedOriginalTwoDeposit
open Function Finset MeasureTheory Lattice Wilson RG OPE.Therm Push PhysicalNext.Repeat.Legato
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){N p:ℕ}
local notation "family" => R.family
local notation "sample" i:max => Config G ((family).side i p)
local notation "priorAt" i:max => prior G ((family).side i p)

structure Column (N p d:ℕ) where
  lift : R.family.label d
  signed : Bool
  motion : Signed
  pin : Site (R.family.side N p)

variable {d f:ℕ}
def raw (A:Column R N p d):sample N→ℂ:=
  RelayDifference.oriented ((family).O N p A.lift 0) A.signed A.motion A.pin

theorem continuous (A:Column R N p d):Continuous (raw R A):=by
  let g:sample N→ℂ:=((family).O N p A.lift 0) ∘ pull A.motion A.pin
  have good:Continuous g:=((family).continuousO ..).comp (continuous_pull ..)
  unfold raw
  cases A.signed
  · exact good
  · exact good.star

def held (A:Column R N p d)(i:ℕ):sample i→ℂ:=
  if h:i≤N then actualTransport (family) (N:=N) (raw R A) h else 0

def separate (A:Column R N p d)(B:Column R N p f)(i:ℕ):sample i→ℂ:=
  fun U=>held R A i U*held R B i U

def birth (A:Column R N p d)(B:Column R N p f)(i:ℕ):sample i→ℂ:=
  fun U=>actualTransport (family) (N:=N) (separate R A B (i+1)) i.le_succ U - separate R A B i U

def landed (A:Column R N p d)(B:Column R N p f)(K i:ℕ)(V:sample K):ℂ:=
  if h:K ≤ i then actualTransport (family) (N:=N) (birth R A B i) h V else 0

theorem unary (A:Column R N p d){i:ℕ}(live:i+1≤N):
    actualTransport (family) (N:=N) (held R A (i+1)) i.le_succ = held R A i:=by
  rw [held,dif_pos live,actualTransport_tower (family) R.makes le_rfl]
  rw [held,dif_pos (i.le_succ.trans live)]

theorem covariance (A:Column R N p d)(B:Column R N p f){i:ℕ}(live:i+1≤N)(U:sample i):
    birth R A B i U=
    actualAverage (family) (N:=N) (fun T=>held R A (i+1) T*held R B (i+1) T) U-
      actualAverage (family) (N:=N) (held R A (i+1)) U*actualAverage (family) (N:=N) (held R B (i+1)) U:=by
  have one (A:sample (i+1)→ℂ):actualTransport (family) (N:=N) A i.le_succ=actualAverage (family) (N:=N) A:=by
    rw [actualTransport_step (family) R.makes live A (Nat.lt_succ_self i),actualTransport_base (family) R.makes live]
  rw [birth,one (separate R A B (i+1)),←one (held R A (i+1)),←one (held R B (i+1)),unary R A live,unary R B live]; rfl

private theorem pairIntegral (A:Column R N p d)(B:Column R N p f){i:ℕ}(live:i≤N):
    Integrable (fun U=>((family).path.rep N p i).eval U • separate R A B i U) (priorAt i):=by
  have finite {k}(P:Column R N p k):∃b:ℝ, AEStronglyMeasurable (held R P i) (priorAt i) ∧
      ∀U,‖held R P i U‖≤b:=by
    obtain ⟨ht,b,val⟩:=Envelope.compactC (continuous R P)
    rw [held,dif_pos live]
    exact ⟨b,(actualTransport_integrable (family) R.makes le_rfl ht.aestronglyMeasurable val live).aestronglyMeasurable,
      fun U=>actualTransport_norm_le (family) R.makes le_rfl val live U⟩
  obtain ⟨a,ma,ha⟩:=finite A
  obtain ⟨b,mb,hb⟩:=finite B
  have bound(U:sample i):‖separate R A B i U‖≤a*b:=by
    rw [separate,norm_mul];exact mul_le_mul (ha U) (hb U) (norm_nonneg _) ((norm_nonneg _).trans (ha U))
  have integrable:=actualTransport_weighted_integrable (family) R.makes live (ma.mul mb) bound (le_refl i)
  rwa [actualTransport_base (family) R.makes live] at integrable

theorem original (A:Column R N p d)(B:Column R N p f){K:ℕ}(live:K≤N)(V:sample K):
    actualTransport (family) (N:=N) (fun U=>raw R A U*raw R B U) live V -
      separate R A B K V = ∑i∈Ico K N,landed R A B K i V:=by
  let val (i:ℕ):ℂ:=if h:K ≤ i then actualTransport (family) (N:=N) (separate R A B i) h V else 0
  have lo:val K=separate R A B K V:=by simp only [val,dif_pos le_rfl,actualTransport_base (family) R.makes live]
  have hi:val N=actualTransport (family) (N:=N) (fun U=>raw R A U*raw R B U) live V:=by
    have atTop {k}(D:Column R N p k):held R D N=raw R D:=by
      rw [held,dif_pos le_rfl,actualTransport_base (family) R.makes le_rfl]
    have equal:separate R A B N=fun U=>raw R A U*raw R B U:=by
      funext U;rw [separate,atTop,atTop]
    simp only [val,dif_pos live,equal]
  have rooted:∑i∈Ico K N,landed R A B K i V=∑i∈Ico K N,(val (i+1)-val i):=by
    refine sum_congr rfl fun i hi=>?_
    have bounds:=mem_Ico.mp hi
    have upper:i+1≤N:=bounds.2
    have inner:=pairIntegral R A B upper
    have lower:=pairIntegral R A B (i.le_succ.trans upper)
    have moved:=actualTransport_weighted_integrable_of_integrable (family) R.makes upper inner i.le_succ
    simp only [landed,dif_pos bounds.1,val,dif_pos (bounds.1.trans i.le_succ)]
    have sub:=congrFun (ActualWilsonAbsoluteTransport.sub (family) R.makes (i.le_succ.trans upper) moved lower bounds.1) V
    exact sub.trans (congrArg (fun a=>a-_) (congrFun (actualTransport_tower (family) R.makes upper (separate R A B (i+1)) i.le_succ bounds.1) V))
  rw [rooted,sum_Ico_eq_sub _ live];simp_rw [sum_range_sub];rw [hi,lo];abel

end YM.Integration.WilsonReflectedOriginalTwoDeposit
