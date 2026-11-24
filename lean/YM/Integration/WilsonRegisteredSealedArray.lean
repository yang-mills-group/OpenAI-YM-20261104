import YM.Integration.WilsonRegisteredSealedReplica

/-! Finite reflected arrays of the actual difference between a fine
Wilson field and a coarse counterterm use one chronological Wilson law. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredSealedArray
open Lattice Wilson RG Cells Push.GridApprox OPE.Therm PhysicalNext.Repeat.Legato
open Set MeasureTheory QLocalPhysicalPathKernel WilsonMacroscopicForwardTransfer WilsonRegisteredSealedReplica
open WilsonPositionOriginalDressedQFailedPath
open private pulled from YM.Integration.WilsonPositionOriginalDressedQPathHearing
open scoped Classical Topology

variable {V:Type} [DecidableEq V] {G:Gauge}
private theorem distribute (s:Finset V)(A B:V→ℂ):
    (∏v∈s,(A v-B v))=∑t∈s.powerset,(-1:ℂ)^(s\t).card *
      ((∏v∈t,A v) * ∏v∈s\t,B v):=by
  classical
  simp only [sub_eq_add_neg,Finset.prod_add]
  simp_rw [show ∀v,-B v=(-1:ℂ)*B v from fun v=>by ring,Finset.prod_mul_distrib,Finset.prod_const]
  apply Finset.sum_congr rfl
  intro t ht
  ring

/-- Arbitrary heterogeneous choices of the upper signed observables and
the lower fields are compared before either physical regulator. -/
theorem original (R:Run G){N per i:ℕ}(live:i<N)(s:Finset V)
    (Q:V → Config G (R.family.side (i+1) per) → ℂ)(hq:∀v,Envelope (Q v))
    (L:V → Config G (R.family.side i per) → ℂ)(H:V → Set (Site (R.family.side i per)))
    (paid:∀v,Interior (H v) (L v))(apart:Pairwise fun v u=>Disjoint (H v) (H u)):
    let step:=backTo R.family.path N per (Nat.le_succ i)
    (∫ω:ConfigurationPath R per, (∏v∈s,(Q v (ω (i+1))-L v (ω i))) ∂path R.family R.makes N per)=
      ∫U,(∏v∈s,(Q v U-step (L v) U)) ∂scene R.family.path N per (i+1):=by
  intro step
  let μ:=path R.family R.makes N per
  let ν:=scene R.family.path N per (i+1)
  letI:IsProbabilityMeasure μ:=path_probability R.family R.makes N per
  letI:IsProbabilityMeasure ν:=probability R.makes.wilson live
  have eQ (t:Finset V):Envelope (word Q t):=Envelope.prodC t Q (fun v _=>hq v)
  have eL (t:Finset V):Envelope (word L t):=Envelope.prodC t L (fun v _=>cylinder_env (paid v))
  have eS (t:Finset V):Envelope (word (fun v=>step (L v)) t):=
    Envelope.prodC t _ (fun v _=>backTo_env R.family.path N per (Nat.le_succ i) (cylinder_env (paid v)))
  have left (t:Finset V):Integrable (fun ω:ConfigurationPath R per=>
      (-1:ℂ)^(s\t).card * (word Q t (ω (i+1))*word L (s\t) (ω i))) μ:=by
    have p:Envelope (fun ω:ConfigurationPath R per=>word Q t (ω (i+1))):=pulled (eQ t) (measurable_pi_apply (i+1))
    have q:Envelope (fun ω:ConfigurationPath R per=>word L (s\t) (ω i)):=pulled (eL (s\t)) (measurable_pi_apply i)
    exact ((p.mulC q).integrableC μ).const_mul _
  have right (t:Finset V):Integrable (fun U=>
      (-1:ℂ)^(s\t).card * (word Q t U * word (fun v=>step (L v)) (s\t) U)) ν:=
    (((eQ t).mulC (eS (s\t))).integrableC ν).const_mul _
  simp_rw [distribute]
  change (∫ω,∑t∈s.powerset,(-1:ℂ)^(s\t).card*(word Q t (ω (i+1))*word L (s\t) (ω i)) ∂μ)=
    ∫U,∑t∈s.powerset,(-1:ℂ)^(s\t).card*(word Q t U*word (fun v=>step (L v)) (s\t) U) ∂ν
  rw [integral_finsetSum _ (fun t _=>left t),integral_finsetSum _ (fun t _=>right t)]
  apply Finset.sum_congr rfl
  intro t ht
  rw [integral_const_mul,integral_const_mul,branch R live (word Q t) (eQ t) L H paid apart (s\t)]
end YM.Integration.WilsonRegisteredSealedArray
