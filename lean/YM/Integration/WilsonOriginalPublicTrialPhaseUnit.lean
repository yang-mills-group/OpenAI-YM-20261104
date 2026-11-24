import YM.Integration.WilsonOriginalPublicTrialPhaseLocated

/-! The horizon-zero split on the whole original Wilson density, including its occupied part. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseUnit
open Finset Function Lattice Wilson RG Source Labels Extra.Histories
open scoped Classical BigOperators

variable {G:Gauge}

/-- Every polynomial admitted at horizon zero is its own constant coefficient. -/
theorem label (v:Label G 0): v=v.val.coeff 0 • unit G 0:=by
  apply Subtype.ext
  change v.val = v.val.coeff 0 • (1:Pol G)
  ext b
  by_cases h:b=0
  · subst b
    simp
  · have hn:b∉v.val.support:=by
      intro hb
      have hx:height b≤0:=((MvPolynomial.mem_restrictSupport_iff ℂ).mp
        (show v.val∈limited G 0 from v.property.1)) hb
      apply h
      ext k
      by_contra bad
      have hpos:b k≠0:=by simpa using bad
      have he:b k*generation k≤height b:=by
        unfold height
        rw [Finsupp.weight_apply,Finsupp.sum]
        exact single_le_sum (f:=fun j=>b j • generation j) (fun _ _=>Nat.zero_le _)
          (Finsupp.mem_support_iff.mpr hpos)
      have hk:0<generation k:=by unfold generation; omega
      exact (Nat.not_lt_of_ge (he.trans hx)) (Nat.mul_pos (Nat.pos_of_ne_zero hpos) hk)
    have hz:=MvPolynomial.notMem_support_iff.mp hn
    simp [hz,MvPolynomial.coeff_one,Ne.symm h]

/-- This uses the actual basis in the original frame. -/
theorem vector (F:Frame G 0)(v:F.Coeff):v=v 0 • F.e0:=by
  let b:=F.coords.symm v
  have hv:=congrArg F.coords (label b)
  rw [map_smul,F.coords_unit] at hv
  change F.coords (F.coords.symm v)=_ at hv
  rw [LinearEquiv.apply_symm_apply] at hv
  have hs:=congrFun hv 0
  simp [Frame.e0] at hs
  rw [hs]
  exact hv

variable {F:Frame G 0}{n:Side}(X:Coefficient F n)

def centered:Coefficient F n:={X with x:=0}

theorem account {o:Site n}{H:Hol G}{R:Rep G n}{a b:ℝ}
    (hf:X.Format o H R)(hb:X.remBound o R a b):
    (centered X).Format o H R ∧ (centered X).remBound o R a b:=by
  obtain ⟨s,t,u,q,h,r,a,b,g⟩:=hf
  exact ⟨⟨s,t,u,q,h,r,a,b,g⟩,hb⟩

theorem unmasked (o:Site n)(S:SectionData F)(R:Rep G n)(U:Config G n):
    X.exponentialEntry o S R U=X.x 0+(centered X).exponentialEntry o S R U:=by
  have hc:F.core X.x=0:=by
    calc F.core X.x = F.core (X.x 0 • F.e0) := congrArg F.core (vector F X.x)
         _ = 0 := by rw [map_smul,Size.unit_core,smul_zero]
  change X.x 0 + _ + _ = X.x 0 + ((0:F.Coeff) 0 + _ + _)
  simp only [centered,Pi.zero_apply,zero_add,hc,map_zero]
  abel

theorem density (o:Site n)(S:SectionData F)(R:Rep G n)(U:Config G n):
    X.density o S R U=(R.eval U:ℂ)*X.x 0+(centered X).density o S R U:=by
  simp only [Coefficient.density,unmasked X o S R U]
  unfold centered Coefficient.marked
  ring

theorem hard (R:Rep G n)(s:Finset ℕ)(U:Config G n):
    (centered X).marked R s U=X.marked R s U:=rfl

end YM.Integration.WilsonOriginalPublicTrialPhaseUnit
