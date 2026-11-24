import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionShieldedAtomBank

/-! Variation on the original torus with one common mask on a physical row
and its contact subtraction. The incoming support need not be connected. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace YM.Integration.FVA1Physical.Exchange.ShieldedAction
open Finset Lattice RG Wilson Precision Push.Local Push.AbsoluteSums.Paths
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{k:ℕ}
local notation "Fld" => Config G n

def shadow (p:BudgetPoint)(X:Support n)(F:Fld→ℝ)(W:Fld):ℝ:=masked p.threshold X F W-F W

/-- A moving locally supported omitted row visits the edited edge and
reaches a point where the original physical field fails its threshold. -/
theorem moving_shadow (p:BudgetPoint)(e:Edge (Site n))(D R:ℕ)(U V:Fld)
    (same:∀b:Edge (Site n),b≠e → U b=V b)(cold:Healthy p.threshold (halo D {e.1}) U)
    (after:e.1∉flags p.threshold V)(s:Signed)(z:Site n)(X:Support n)(F:Fld→ℝ)
    (loc:LocalOn X F)(reach:∀v∈X,separation z v≤R)
    (live:shadow p X F (pull s 0 U)≠shadow p X F (pull s 0 V)):
    separation e.1 (turnSites s 0 z)≤R ∧ D<2*R:=by
  have pre:Healthy p.threshold {e.1} U:=Disjoint.mono_left (halo_subset _ _) cold
  have post:Healthy p.threshold {e.1} V:=disjoint_left.mpr (fun x hx=>mem_singleton.mp hx ▸ after)
  have matching(b:Edge (Site n))(h:b.1∉({e.1}:Support n)):U b=V b:=same b (fun eq=>h (eq ▸ mem_singleton_self _))
  have flags_eq:=edit_flag_set _ p U V matching pre post s
  have eqH:Healthy p.threshold X (pull s 0 U) ↔ Healthy p.threshold X (pull s 0 V):=by simp only [Healthy,flags_eq]
  have off:¬Healthy p.threshold X (pull s 0 U):=by
    intro on;apply live
    simp only [shadow,masked_eq _ _ _ _ on,masked_eq _ _ _ _ (eqH.mp on),sub_self]
  have move:F (pull s 0 U)≠F (pull s 0 V):=by
    intro eq;apply live
    simp only [shadow,masked_ne _ _ _ _ off,masked_ne _ _ _ _ (mt eqH.mpr off),eq]
  let b:=turnSites s 0 z
  let actual:Support n:=X.image (turnSites s 0)
  have span(v:Site n)(hv:v∈actual):separation b v≤R:=by
    obtain ⟨y,hy,rfl⟩:=mem_image.mp hv
    change separation (turnSites s 0 z) (turnSites s 0 y)≤_
    rw [turn_sep];exact reach y hy
  have entered:e.1∈actual:=by
    by_contra! missing
    exact move (loc _ _ (agrees_pull s 0 (fun edge seen _=>same edge (fun eq=>missing (eq ▸ seen)))))
  have miss:¬Healthy p.threshold actual U:=fun yes=>off ((healthy_pull s 0 p.threshold X U).mp yes)
  obtain ⟨v,hv,flag⟩:=Finset.not_disjoint_iff.mp miss
  have ed:separation e.1 b≤R:=(separation_comm ..).le.trans (span e.1 entered)
  have away:D<separation e.1 v:=by
    apply lt_of_not_ge;intro near
    exact disjoint_left.mp cold (halo_spec.mpr ⟨e.1,mem_singleton_self _,near⟩) flag
  exact ⟨ed,away.trans_le ((separation_triangle e.1 b v).trans (by linarith only [ed,span v hv]))⟩

theorem local_shadow_price (p:BudgetPoint)(e:Edge (Site n))(D R:ℕ)(U V:Fld)
    (same:∀b:Edge (Site n),b≠e → U b=V b)(cold:Healthy p.threshold (halo D {e.1}) U)
    (after:e.1∉flags p.threshold V)(s:Signed)(z:Site n)(X:Support n)(F:Fld→ℝ)
    (loc:LocalOn X F)(reach:∀v∈X,separation z v≤R){M σ:ℝ}(cost:∀W,|F W|≤M)(sp:0<σ):
    |shadow p X F (pull s 0 U)-shadow p X F (pull s 0 V)|≤
      (2*M)*Real.exp (σ*(R:ℝ))*Real.exp (-(σ/4)*(D:ℝ))*Real.exp (-(σ/2)*(separation e.1 (turnSites s 0 z):ℝ)):=by
  have mn:0≤M:=(abs_nonneg _).trans (cost U)
  by_cases equal:shadow p X F (pull s 0 U)=shadow p X F (pull s 0 V)
  · rw [equal,sub_self,abs_zero];positivity
  obtain ⟨r,d⟩:=moving_shadow p e D R U V same cold after s z X F loc reach equal
  have f(w:Fld):|shadow p X F w|≤M:=by
    by_cases ok:Healthy p.threshold X w
    · simpa only [shadow,masked_eq _ _ _ _ ok,sub_self,abs_zero] using mn
    simpa only [shadow,masked_ne _ _ _ _ ok,zero_sub,abs_neg] using cost w
  have r':(separation e.1 (turnSites s 0 z):ℝ)≤(R:ℝ):=by exact_mod_cast r
  have d':(D:ℝ)≤2*(R:ℝ):=by exact_mod_cast d.le
  have spend:1≤Real.exp (σ*(R:ℝ))*Real.exp (-(σ/4)*(D:ℝ))*Real.exp (-(σ/2)*(separation e.1 (turnSites s 0 z):ℝ)):=by
    rw [←Real.exp_add,←Real.exp_add]
    apply Real.one_le_exp
    nlinarith only [mul_le_mul_of_nonneg_left r' sp.le,mul_le_mul_of_nonneg_left d' sp.le]
  calc
    _ ≤ M+M:=(abs_sub ..).trans (add_le_add (f _) (f _))
    _ = 2*M:=by ring
    _ ≤ _:= by simpa only [mul_assoc] using (le_mul_of_one_le_right (show 0≤2*M by positivity) spend)

def contactBody (a b:Atom G k)(z:Site n)(U:Fld):ℝ:=
  if k=2 then a.unmasked U z-b.unmasked U z else a.unmasked U z

def contactSupport (a b:Atom G k)(z:Site n):Support n:=a.footprint z∪b.footprint z

theorem contact_body_bound (a b:Atom G k)(z:Site n)(U:Fld)(wallet:b.magnitude≤a.magnitude):
    |contactBody a b z U|≤2*(a.magnitude*2^k):=by
  have nn:0≤a.magnitude:=by unfold Atom.magnitude;positivity
  have ha:=a.unmasked_bound U z
  have hb:|b.unmasked U z|≤a.magnitude*2^k:=(b.unmasked_bound U z).trans
    (mul_le_mul_of_nonneg_right wallet (by positivity))
  unfold contactBody;split
  · linarith only [abs_sub (a.unmasked U z) (b.unmasked U z),ha,hb]
  linarith only [ha,show 0≤a.magnitude*2^k by positivity]

/-- The rank-two re-expression withdraws its contracted atom behind the
same union mask as the full row; either rank may have wrapping support. -/
theorem contact_atom_price (p:BudgetPoint)(e:Edge (Site n))(D:ℕ)(U V:Fld)
    (same:∀b:Edge (Site n),b≠e → U b=V b)(cold:Healthy p.threshold (halo D {e.1}) U)
    (after:e.1∉flags p.threshold V)(s:Signed)(a b:Atom G k)(z:Site n)
    (trim:b.length≤a.length)(wallet:b.magnitude≤a.magnitude){σ:ℝ}(sp:0<σ):
    |shadow p (contactSupport a b z) (contactBody a b z) (pull s 0 U)-
     shadow p (contactSupport a b z) (contactBody a b z) (pull s 0 V)|≤
    a.budget σ*((2:ℝ)^(k+2)*Real.exp (-(σ/4)*(D:ℝ))*
      Real.exp (-(σ/2)*(separation e.1 (turnSites s 0 z):ℝ))):=by
  have loc:LocalOn (contactSupport a b z) (contactBody a b z):=by
    intro U' V' eq
    have ha:=Next.Rank.Alarm.unmasked_space a z U' V' (agrees_mono eq (fun _ hy=>Finset.mem_union_left _ hy))
    have hb:=Next.Rank.Alarm.unmasked_space b z U' V' (agrees_mono eq (fun _ hy=>Finset.mem_union_right _ hy))
    simp only [contactBody,ha,hb]
  have reach(v:Site n)(hv:v∈contactSupport a b z):separation z v≤a.length:=by
    rcases mem_union.mp hv with h|h
    · apply where_slot z a.leg v;rw [←atom_foot];exact h
    apply le_trans _ trim;apply where_slot z b.leg v;rw [←atom_foot];exact h
  apply (local_shadow_price p e D a.length U V same cold after s z _ _ loc reach
    (fun W=>contact_body_bound a b z W wallet) sp).trans_eq
  unfold Atom.budget;rw [pow_succ,pow_succ]
  ring

end YM.Integration.FVA1Physical.Exchange.ShieldedAction
