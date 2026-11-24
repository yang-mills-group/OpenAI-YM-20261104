import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionEditedTransportTail
import YM.Next.RANK.Bordering

/-! A marked-off kinetic/loop interaction can vary only if that very atom
visits both the edited bond and an actual failed plaquette. Preserve the
original support and signed orientation of every submitted path. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace YM.Integration.FVA1Physical.Exchange.ShieldedAction
open Finset Lattice RG Wilson Precision Push.Local Push.AbsoluteSums.Paths
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{k:ℕ}
local notation "Fld" => Config G n

theorem edit_flag_set (D:Support n)(p:BudgetPoint)(U V:Fld)
    (out:∀e:Edge (Site n),e.1∉D → U e=V e)(cu:Healthy p.threshold D U)(cv:Healthy p.threshold D V)
    (s:Signed): flags p.threshold (pull s 0 U)=flags p.threshold (pull s 0 V):=by
  ext z;rw [flags_spec,flags_spec]
  apply exists_congr;intro a
  apply and_congr_right;intro _
  rcases cold_plaquette_profile D p U V out cu cv s a with eq|h
  · rw [eq]
  exact iff_of_false h.1.not_gt h.2.not_gt

def atomDefect (a:Atom G k)(p:BudgetPoint)(u:Fld)(z:Site n):ℝ:=
  a.placed p u z-a.unmasked u z

/-- Every moving omitted atom must pay for the actual distance from the
insertion to its center and for a genuine field failure outside the cold collar. -/
theorem omitted_atom_spans (p:BudgetPoint)(e:Edge (Site n))(D:ℕ)(U V:Fld)
    (same:∀b:Edge (Site n),b≠e → U b=V b)(cold:Healthy p.threshold (halo D {e.1}) U)
    (after:e.1∉flags p.threshold V)(s:Signed)(a:Atom G k)(z:Site n)
    (live:atomDefect a p (pull s 0 U) z≠atomDefect a p (pull s 0 V) z):
    separation e.1 (turnSites s 0 z)≤a.length ∧ D<2*a.length:=by
  have pre:Healthy p.threshold {e.1} U:=disjoint_left.mpr (fun x hx=>disjoint_left.mp cold (halo_subset _ _ hx))
  have post:Healthy p.threshold {e.1} V:=disjoint_left.mpr (fun x hx=>mem_singleton.mp hx ▸ after)
  have matching(b:Edge (Site n))(h:b.1∉({e.1}:Support n)):U b=V b:=same b (fun eq=>h (eq ▸ mem_singleton_self _))
  have flags_eq:=edit_flag_set _ p U V matching pre post s
  let T:Support n:=a.footprint z
  have eqH:Healthy p.threshold T (pull s 0 U) ↔ Healthy p.threshold T (pull s 0 V):=by simp only [Healthy,flags_eq]
  have off:¬Healthy p.threshold T (pull s 0 U):=by
    intro on;apply live
    unfold atomDefect Atom.placed
    rw [masked_eq _ T _ _ on,masked_eq _ T _ _ (eqH.mp on),sub_self,sub_self]
  have move:a.unmasked (pull s 0 U) z≠a.unmasked (pull s 0 V) z:=by
    intro eq;apply live
    unfold atomDefect Atom.placed
    rw [masked_ne _ T _ _ off,masked_ne _ T _ _ (mt eqH.mpr off),eq]
  let b:=turnSites s 0 z
  let actual:Support n:=T.image (turnSites s 0)
  have span(v:Site n)(hv:v∈actual):separation b v≤a.length:=by
    obtain ⟨y,hy,rfl⟩:=mem_image.mp hv
    change separation (turnSites s 0 z) (turnSites s 0 y)≤_
    rw [turn_sep]
    apply where_slot z a.leg y
    rw [←atom_foot];exact hy
  have entered:e.1∈actual:=by
    by_contra! missing
    apply move
    apply Next.Rank.Alarm.unmasked_space
    apply agrees_pull
    exact fun edge seen _=>same edge (fun eq=>missing (eq ▸ seen))
  have miss:¬Healthy p.threshold actual U:=fun yes=>off ((healthy_pull s 0 p.threshold T U).mp yes)
  obtain ⟨v,hv,flag⟩:=Finset.not_disjoint_iff.mp miss
  have ed:separation e.1 b≤a.length:=(separation_comm ..).le.trans (span e.1 entered)
  have away:D<separation e.1 v:=by
    apply lt_of_not_ge;intro near
    exact disjoint_left.mp cold (halo_spec.mpr ⟨e.1,mem_singleton_self _,near⟩) flag
  exact ⟨ed,away.trans_le ((separation_triangle e.1 b v).trans (by linarith only [ed,span v hv]))⟩

/-- Length of the actual submitted atom buys two separate exponential
reserves, one for the distance to the failure, one for summation over centers. -/
theorem omitted_atom_price (p:BudgetPoint)(e:Edge (Site n))(D:ℕ)(U V:Fld)
    (same:∀b:Edge (Site n),b≠e → U b=V b)(cold:Healthy p.threshold (halo D {e.1}) U)
    (after:e.1∉flags p.threshold V)(s:Signed)(a:Atom G k)(z:Site n){σ:ℝ}(sp:0<σ):
    |atomDefect a p (pull s 0 U) z-atomDefect a p (pull s 0 V) z|≤
      a.budget σ*((2:ℝ)^(k+1)*Real.exp (-(σ/4)*(D:ℝ))*Real.exp (-(σ/2)*(separation e.1 (turnSites s 0 z):ℝ))):=by
  let fee:=a.budget σ*((2:ℝ)^(k+1)*Real.exp (-(σ/4)*(D:ℝ))*Real.exp (-(σ/2)*(separation e.1 (turnSites s 0 z):ℝ)))
  have nn:0≤a.magnitude:=by unfold Atom.magnitude;positivity
  by_cases equal:atomDefect a p (pull s 0 U) z=atomDefect a p (pull s 0 V) z
  · rw [equal,sub_self,abs_zero];unfold Atom.budget;positivity
  obtain ⟨reach,long⟩:=omitted_atom_spans p e D U V same cold after s a z equal
  have before(W:Fld):|atomDefect a p W z|≤a.magnitude*2^k:=by
    by_cases ok:Healthy p.threshold (a.footprint z) W
    · simp only [atomDefect,Atom.placed,masked_eq _ _ _ _ ok,sub_self,abs_zero]
      positivity
    simp only [atomDefect,Atom.placed,masked_ne _ _ _ _ ok,zero_sub,abs_neg]
    exact a.unmasked_bound W z
  have r:(separation e.1 (turnSites s 0 z):ℝ)≤(a.length:ℝ):=by exact_mod_cast reach
  have d:(D:ℝ)≤2*(a.length:ℝ):=by exact_mod_cast long.le
  have spend:1≤Real.exp (σ*(a.length:ℝ))*Real.exp (-(σ/4)*(D:ℝ))*Real.exp (-(σ/2)*(separation e.1 (turnSites s 0 z):ℝ)):=by
    rw [←Real.exp_add,←Real.exp_add]
    apply Real.one_le_exp
    nlinarith only [mul_le_mul_of_nonneg_left r sp.le,mul_le_mul_of_nonneg_left d sp.le]
  calc
    _ ≤ a.magnitude*2^k+a.magnitude*2^k:=(abs_sub ..).trans (add_le_add (before _) (before _))
    _ = a.magnitude*2^(k+1):=by rw [pow_succ];ring
    _ ≤ (a.magnitude*2^(k+1))*(Real.exp (σ*(a.length:ℝ))*Real.exp (-(σ/4)*(D:ℝ))*Real.exp (-(σ/2)*(separation e.1 (turnSites s 0 z):ℝ))):=
      le_mul_of_one_le_right (by positivity) spend
    _ = _:=by unfold Atom.budget;ring

end YM.Integration.FVA1Physical.Exchange.ShieldedAction
