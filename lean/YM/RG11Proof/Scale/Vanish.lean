import YM.RG11Proof.Scale.Vary

/-!
# FPS matrix variation vanishing from all-profile detector

Compare EXACT coefficient k incl k=0 when lower vanish. Uses the same
`Sees` on the full continuum array; regulator asymptotic inversion must not
be inferred from the hypothesis. Matrix constraints per power must hold even
for the residual lowest-order CS term; do not throw away a possibly physical /
finite projection contribution.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.RG11.Scale
open scoped BigOperators Classical Topology
open PowerSeries YM.RG11.Jets YM.PertExtension.Position

variable {R:Type*}[CommRing R] {P J:Type*}{width:P→ℕ}[Fintype J]
local notation "slots" => PertExtension.Position.insert

/-- When all degrees strictly below k vanish, INCLUDING 0 if k>0,
the extracted product with other factors at exactly k just uses their
heads. No heartbeat on proof of formal inverse needed. -/
theorem hit_coeff (n:ℕ){p:PowerSeries R}(h:∀ i<n,coeff i p=0)(Q:PowerSeries R):
    coeff n (p * Q)= coeff n p * constantCoeff Q:=by
  rw [coeff_mul, ← coeff_zero_eq_constantCoeff_apply]
  exact Finset.sum_eq_single_of_mem (n,0) (by simp) (fun ⟨i,j⟩ hi hj=>by
    have he:= Finset.HasAntidiagonal.mem_antidiagonal.mp hi
    dsimp at he ⊢; rw [h i ?_,zero_mul]
    rcases (show i≤n by omega).lt_or_eq with ht|ht
    · exact ht
    exact False.elim (hj (Prod.ext (by simpa using ht) (by simpa using (show j=0 by omega)))))

variable {A B:ArrayAt J R width}(D U:Square J (PowerSeries R))

theorem hit_varies (n:ℕ)(hU:∀ i<n,piece i U=0)(v:Mark J width):
    coeff n (varies A D U v)= varies (fun w=>constantCoeff (A w)) (piece 0 D) (piece n U) v:=by
      unfold varies
      simp_rw [Finset.mul_sum, map_sum]
      apply Finset.sum_congr rfl; intro w _; apply Finset.sum_congr rfl; intro i _
      let Q:= U (v.2 i) (w i)
      have hq k (hk:k<n) : coeff k Q=0:=congrArg (fun (u:Square J R)=>u (v.2 i) (w i)) (hU k hk)
      change coeff n (_ * (Q * _))=_
      rw [mul_left_comm, hit_coeff n hq,map_mul,map_prod]
      simp_rw [piece_apply,coeff_zero_eq_constantCoeff_apply]; rw [mul_left_comm]

theorem hit_amplitude (n:ℕ){b:PowerSeries R}(h':∀ i<n,coeff i b=0)(v:Mark J width):
     coeff n (slots J width (fun w=> b*A w) (fun i j=>D i j) v) =
      slots J width (fun w=> coeff n b * constantCoeff (A w)) (fun i j=>piece 0 D i j) v:=by
   unfold PertExtension.Position.insert; simp_rw [map_sum]
   apply Finset.sum_congr rfl; intro x _
   rw [mul_assoc,hit_coeff _ h',map_mul,map_prod]
   simp_rw [piece_apply,coeff_zero_eq_constantCoeff_apply,mul_assoc]

-- sign convention add in the combined residual
variable (b:PowerSeries R)(p:Change R J)

def leftover (v:Mark J width):PowerSeries R:=
    slots J width (fun w=>b*PowerSeries.subst p.g (derivative R (A w))) (fun i j=>p.Z i j) v +
      varies (fun w=>PowerSeries.subst p.g (A w)) p.Z U v

theorem hits_pencil (n:ℕ)(hu:∀ i<n,piece i U=0)(hb:∀ i<n,coeff i b=0)
     (hz:nearId p.Z)(hp:Anchored p.g)(v:Mark J width):
      coeff n (leftover (A:=A) U b p v) = pencil A v (piece n U,coeff n b):=by
   rw [leftover,map_add,hit_amplitude p.Z n hb,hit_varies p.Z U n hu]
   simp_rw [base_compose _ _ hp, show piece 0 p.Z=1 from hz]
   rw [varies_orbit]
   change slots J width _ (fun i j=> (if i=j then (1:R) else 0)) v+_ = _
   rw [insert_one]
   rw [← coeff_zero_eq_constantCoeff_apply,coeff_derivative]
   change _+_ = orbit (fun w=>constantCoeff (A w)) v (piece n U)+ tangent (A v)*_
   simp [tangent]; ring

section
-- `Fintype J` dependency consistent independent of series base ring
variable {K:Type*}[Field K]{A':ArrayAt J K width}{L:Constraints K J}
variable (U':Square J (PowerSeries K))(b':PowerSeries K)(d:Change K J)

theorem erase_redefs (h:Sees L A')(hU:∀ k,piece k U'∈L.vary)(hn:nearId d.Z)(hp:Anchored d.g)
     {N}(he:∀ v:Mark J width, Through N (leftover (A:=A') U' b' d v) 0):
     ∀ k ≤ N,piece k U'=0 ∧ coeff k b'=0:=by
  intro k hk
  induction k using Nat.strong_induction_on with
  | h k ih=>
    have hi i (hi:i<k):= ih i hi (hi.le.trans hk)
    let u:Step L:= (⟨piece k U',hU k⟩,coeff k b')
    suffices u = 0 from ⟨congrArg (fun z:Step L=> z.1.val) this,congrArg Prod.snd this⟩
    apply h; rw [map_zero]; funext v
    change pencil A' v (_,_)=0
    change pencil A' v (piece k U',coeff k b')=0
    rw [← hits_pencil U' b' d k (fun i hk=>(hi i hk).1) (fun i hk=>(hi i hk).2) hn hp, he v k hk,map_zero]
end

end YM.RG11.Scale
