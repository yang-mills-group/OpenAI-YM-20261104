import YM.Integration.WilsonReflectedOriginalTwoDeposit
import YM.Integration.WilsonOriginalMicroscopicGuardedTrial

/-! A marked pair starts at a chosen finite date on the original N-cutoff
quiet. Its complete conditional has the actual divided covariance at every
subsequent step. The two cutoff fields and both guarded trial stencils may
have distinct roots, ranks and sources. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedRestartedPair
open Function Finset MeasureTheory Lattice Wilson RG OPE.Therm Push PhysicalNext.Repeat.Legato
open WilsonReflectedOriginalTwoDeposit
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){N p K:ℕ}
local notation "C" => R.family
local notation "space" i:max => Config G ((C).side i p)

def mean {K:ℕ}(N:ℕ)(A:space K→ℂ)(i:ℕ):space i→ℂ:=
  if h:i≤K then actualTransport (C) (N:=N) A h else 0

def product {K:ℕ}(N:ℕ)(A B:space K→ℂ)(i:ℕ)(U:space i):ℂ:=
  mean R N A i U * mean R N B i U

def incident (N:ℕ)(A B:space K→ℂ)(i:ℕ)(U:space i):ℂ:=
  actualTransport (C) (N:=N) (product R N A B (i+1)) i.le_succ U-product R N A B i U

def returned (N:ℕ)(A B:space K→ℂ)(j i:ℕ)(U:space j):ℂ:=
  if h:j ≤ i then actualTransport (C) (N:=N) (incident R N A B i) h U else 0

theorem issued {A:space K→ℂ} (data:Envelope A)(upper:K≤N){i:ℕ}(before:i≤K):
    ∃M:ℝ,AEStronglyMeasurable (mean R N A i) (prior G _) ∧ ∀U,‖mean R N A i U‖≤M:=by
  obtain ⟨borel,M,bound⟩:=data
  rw [mean,dif_pos before]
  exact ⟨M,(actualTransport_integrable (C) R.makes upper borel.aestronglyMeasurable bound before).aestronglyMeasurable,
    actualTransport_norm_le (C) R.makes upper bound before⟩

private theorem eligible {A B:space K→ℂ}(one:Envelope A)(two:Envelope B)(upper:K≤N){i:ℕ}(before:i≤K):
    Integrable (fun U=>((C).path.rep N p i).eval U • product R N A B i U) (prior G _):=by
  obtain ⟨a,ma,ba⟩:=issued R one upper before
  obtain ⟨b,mb,bb⟩:=issued R two upper before
  have bounded(U:space i):‖product R N A B i U‖ ≤ a*b:=by
    rw [product,norm_mul];exact mul_le_mul (ba U) (bb U) (norm_nonneg _) ((norm_nonneg _).trans (ba U))
  have read:=actualTransport_weighted_integrable (C) R.makes (before.trans upper) (ma.mul mb) bounded (le_refl i)
  rwa [actualTransport_base (C) R.makes (before.trans upper)] at read

theorem original (A B:space K→ℂ)(one:Envelope A)(two:Envelope B)(upper:K≤N){f:ℕ}(earlier:f≤K)(U:space f):
    actualTransport (C) (N:=N) (fun W=>A W*B W) earlier U-product R N A B f U =
      ∑i∈Ico f K,returned R N A B f i U:=by
  let value (i:ℕ):ℂ:=if h:f ≤ i then actualTransport (C) (N:=N) (product R N A B i) h U else 0
  have lower:value f=product R N A B f U:=by
    simp only [value,dif_pos le_rfl,actualTransport_base (C) R.makes (earlier.trans upper)]
  have start:value K=actualTransport (C) (N:=N) (fun W=>A W*B W) earlier U:=by
    have finalPair:product R N A B K=fun W=>A W*B W:=by
      funext W
      simp only [product,mean,dif_pos le_rfl,actualTransport_base (C) R.makes upper]
    simp only [value,dif_pos earlier,finalPair]
  have each:∑i∈Ico f K,returned R N A B f i U=∑i∈Ico f K,(value (i+1)-value i):=by
    refine sum_congr rfl fun i hi=>?_
    obtain ⟨left,right⟩:=mem_Ico.mp hi
    have late:i+1≤K:=right
    have first:=eligible R one two upper late
    have second:=eligible R one two upper (i.le_succ.trans late)
    have moved:=actualTransport_weighted_integrable_of_integrable (C) R.makes (late.trans upper) first i.le_succ
    simp only [returned,dif_pos left,value,dif_pos (left.trans i.le_succ)]
    have step:=congrFun (ActualWilsonAbsoluteTransport.sub (C) R.makes ((i.le_succ.trans late).trans upper) moved second left) U
    exact step.trans (congrArg (fun x=>x-_) (congrFun (actualTransport_tower (C) R.makes (late.trans upper) (product R N A B (i+1)) i.le_succ left) U))
  rw [each,sum_Ico_eq_sub _ earlier];simp_rw [sum_range_sub];rw [start,lower];abel

def guardField (d:Fin 3→ℕ)(N K:ℕ)(o:Fin 3→Site ((C).side K p))(w:∀a:Fin 3,(C).label (d a))(a:Fin 3):space K→ℂ:=
  WilsonOriginalMicroscopicGuardedTrial.guarded R d N p K o w a

theorem guarded (d:Fin 3→ℕ)(N K:ℕ)(o:Fin 3→Site ((C).side K p))(w:∀a:Fin 3,(C).label (d a))(a:Fin 3):
    Envelope (guardField R d N K o w a):=by
  obtain ⟨borel,_,bound⟩:=WilsonOriginalMicroscopicGuardedTrial.unary R d N p K o w a
  exact ⟨borel,_,fun U=>(bound U).1⟩

/-- Both original mixed deposits and both singleton substitutions enter on
the same configuration. The trial starts its marks at K and keeps the full
original N-cutoff quiet throughout. -/
theorem compared {a b:ℕ}(left:Column R N p a)(right:Column R N p b)
    (d:Fin 3→ℕ)(o:Fin 3→Site ((C).side K p))(w:∀i:Fin 3,(C).label (d i))(u v:Fin 3)
    (upper:K≤N){f:ℕ}(atCut:f≤K)(W:space f):
    let A:=guardField R d N K o w u
    let B:=guardField R d N K o w v
    actualTransport (C) (N:=N) (fun T=>raw R left T*raw R right T) (atCut.trans upper) W-
      actualTransport (C) (N:=N) (fun T=>A T*B T) atCut W=
     (∑i∈Ico f N,landed R left right f i W)-(∑i∈Ico f K,returned R N A B f i W)+
       (held R left f W-mean R N A f W)*held R right f W+
       mean R N A f W*(held R right f W-mean R N B f W):=by
  intro A B
  have actual:=WilsonReflectedOriginalTwoDeposit.original R left right (atCut.trans upper) W
  have trial:=original R A B (guarded R d N K o w u) (guarded R d N K o w v) upper atCut W
  unfold separate at actual;unfold product at trial
  rw [←actual,←trial]
  ring

end YM.Integration.WilsonReflectedRestartedPair
end
