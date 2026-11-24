import YM.Integration.WilsonIndependentPostedGrant

/-! The suspended fine action keeps exactly its original slots on both the torus and the cover. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentPostedInjection
open Function Matrix Lattice RegulatorIR RegulatorIR.Budget RegulatorIR.Budget.Packet
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Soil
open WilsonIndependentPostedGrant (insert)
open scoped Classical BigOperators
variable {U a b:Type}{r:ℕ}

def channel (U a b:Type):U×a↪U×(a⊕b) where
  toFun x:=(x.1,Sum.inl x.2)
  inj' :=by rintro ⟨x,i⟩ ⟨y,j⟩ h;exact Prod.ext (congr_arg (fun z:U×(a⊕b)=>z.1) h) (Sum.inl.inj (congr_arg (fun z:U×(a⊕b)=>z.2) h))

theorem entry [DecidableEq U][DecidableEq a](x:U×a)(y:U×(a⊕b)):
    insert U a b x y=if channel U a b x=y then 1 else 0:=by
  classical
  rcases x with ⟨x,i⟩;rcases y with ⟨y,j|j⟩
  · by_cases hx:x=y<;>by_cases hi:i=j<;>simp [WilsonIndependentPostedGrant.insert,upper,Matrix.one_apply,channel,hx,hi]
  · simp [WilsonIndependentPostedGrant.insert,upper,channel]

theorem links [DecidableEq U][DecidableEq a](x:Fin r→U×a)(y:Fin r→U×(a⊕b)):
    (∏ i,insert U a b (x i) (y i))=if channel U a b∘x=y then 1 else 0:=by
  classical
  by_cases h:channel U a b∘x=y
  · subst y;simp [entry]
  rw [if_neg h]
  obtain ⟨i,hi⟩:=Function.ne_iff.mp h
  exact Finset.prod_eq_zero (Finset.mem_univ i) ((entry (x i) (y i)).trans (if_neg hi))

theorem submit [DecidableEq U][DecidableEq a](T:Packet (U×a) r)(z:Tuple (U×(a⊕b)) r):
    (∑' y:Tuple (U×a) r,(∏ i,insert U a b (y i) (z i)) • T y)=offer (channel U a b) T z:=by
  classical
  by_cases h:z∈Set.range (acrossT (channel U a b))
  · obtain ⟨x,rfl⟩:=h
    rw [offer_eq,tsum_eq_single x]
    · rw [links,if_pos (show channel U a b∘x=acrossT (channel U a b) x from rfl),one_smul]
    · intro y hy
      have ne:channel U a b∘y≠acrossT (channel U a b) x:=by
        intro he;exact hy (funext fun i=>(channel U a b).inj' (congrFun he i))
      rw [links,if_neg ne,zero_smul]
  rw [offer_zero _ h]
  have no (y:Tuple (U×a) r):(∏ i,insert U a b (y i) (z i)) •T y=0:=by
    have ne:channel U a b∘y≠z:=fun he=>h ⟨y,he⟩
    rw [links,if_neg ne,zero_smul]
  simp only [no,tsum_zero]

theorem finite [Fintype U][Fintype a][DecidableEq U][DecidableEq a](T:Gen ℝ (U×a))(r:ℕ):
    fade (insert U a b) T r=offer (channel U a b) (T r):=by
  funext z
  simpa only [fade,tsum_fintype] using submit (T r) z

theorem cover [Fintype a][DecidableEq a](T:Gen ℝ (Cloth a))(r:ℕ):
    prism (insert Cover a b) T r=offer (channel Cover a b) (T r):=by
  funext z;rw [prism,climb_cut];exact submit (T r) z

end YM.Integration.WilsonIndependentPostedInjection
