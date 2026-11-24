import YM.Integration.WilsonRegisteredRectangleFrameData

/-! A true two-copy exchange of all shared site tags and their incident Wilson prediction factors. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonRegisteredRectangleFrameSwap
open Lattice RG Wilson Finset WilsonRegisteredRectangleTags WilsonRegisteredRectangleFrameData
open scoped Classical
variable {G:Gauge}{c f:Side}(S:StepData c f)

def blend (J:Finset (Site c))(a b:S.SitesChoice):S.SitesChoice:=fun x=>if x∈J then a x else b x

def exchange (J:Finset (Site c)):Equiv.Perm (S.SitesChoice×S.SitesChoice) where
  toFun t:=(blend S J t.1 t.2,blend S J t.2 t.1)
  invFun t:=(blend S J t.1 t.2,blend S J t.2 t.1)
  left_inv t:=by ext x <;> by_cases h:x∈J <;> simp [blend,h]
  right_inv t:=by ext x <;> by_cases h:x∈J <;> simp [blend,h]

def crosses (J:Finset (Site c))(e:Edge (Site c)):Prop:=¬(e.1∈J ↔ e.1+step e.2∈J)

structure Separated (J:Finset (Site c))(st uv sv ut:Config G f):Prop where
  site_in (x:Site c):x∈J → SiteData S st sv x ∧ SiteData S uv ut x
  site_out (x:Site c):x∉J → SiteData S st ut x ∧ SiteData S uv sv x
  bond_in (e:Edge (Site c)):e.1∈J → BondData S st sv e ∧ BondData S uv ut e
  bond_out (e:Edge (Site c)):e.1∉J → BondData S st ut e ∧ BondData S uv sv e
  quiet_head (e:Edge (Site c)):crosses J e → quiet S st (e.1+step e.2) ∧ quiet S uv (e.1+step e.2)

theorem swap (legal:S.patch.Branches S.kernel G)(β:ℝ)(W:Config G c)(J:Finset (Site c))
    {st uv sv ut:Config G f}(seam:Separated S J st uv sv ut)(a b:S.SitesChoice):
    branch S β st W a*branch S β uv W b=
      branch S β sv W (blend S J a b)*branch S β ut W (blend S J b a):=by
  let left:=blend S J a b
  let right:=blend S J b a
  have at_site (x:Site c):site S st a x*site S uv b x=site S sv left x*site S ut right x:=by
    by_cases inside:x∈J
    · have h:=seam.site_in x inside
      rw [site_part S legal a left x h.1 (Or.inl (by simp [left,blend,inside])),
          site_part S legal b right x h.2 (Or.inl (by simp [right,blend,inside]))]
    · have h:=seam.site_out x inside
      rw [site_part S legal a right x h.1 (Or.inl (by simp [right,blend,inside])),
          site_part S legal b left x h.2 (Or.inl (by simp [left,blend,inside])),mul_comm]
  have at_bond (e:Edge (Site c)):(∑k,edge S β st W a e k)*(∑k,edge S β uv W b e k)=
      (∑k,edge S β sv W left e k)*(∑k,edge S β ut W right e k):=by
    by_cases inside:e.1∈J
    · have h:=seam.bond_in e inside
      have head: (a (e.1+step e.2)=left (e.1+step e.2) ∨ quiet S st (e.1+step e.2)) ∧
          (b (e.1+step e.2)=right (e.1+step e.2) ∨ quiet S uv (e.1+step e.2)):=by
        by_cases z:e.1+step e.2∈J
        · simp [left,right,blend,z]
        · have q:=seam.quiet_head e (fun h=>z (h.mp inside));exact ⟨Or.inr q.1,Or.inr q.2⟩
      rw [bond_part S legal β W a left e h.1 (Or.inl (by simp [left,blend,inside])) head.1,
          bond_part S legal β W b right e h.2 (Or.inl (by simp [right,blend,inside])) head.2]
    · have h:=seam.bond_out e inside
      have head: (a (e.1+step e.2)=right (e.1+step e.2) ∨ quiet S st (e.1+step e.2)) ∧
          (b (e.1+step e.2)=left (e.1+step e.2) ∨ quiet S uv (e.1+step e.2)):=by
        by_cases z:e.1+step e.2∈J
        · have q:=seam.quiet_head e (fun h=>inside (h.mpr z));exact ⟨Or.inr q.1,Or.inr q.2⟩
        · simp [left,right,blend,z]
      rw [bond_part S legal β W a right e h.1 (Or.inl (by simp [right,blend,inside])) head.1,
          bond_part S legal β W b left e h.2 (Or.inl (by simp [left,blend,inside])) head.2,mul_comm]
  unfold branch
  rw [show ∀(p q r s:ℝ),(p*q)*(r*s)=(p*r)*(q*s) by intros;ring,←prod_mul_distrib,←prod_mul_distrib]
  conv_rhs=>rw [show ∀(p q r s:ℝ),(p*q)*(r*s)=(p*r)*(q*s) by intros;ring,←prod_mul_distrib,←prod_mul_distrib]
  exact congrArg₂ (·*·) (prod_congr rfl fun x _=>at_site x) (prod_congr rfl fun e _=>at_bond e)

theorem original (legal:S.patch.Branches S.kernel G)(β:ℝ)(W:Config G c)(J:Finset (Site c))
    {st uv sv ut:Config G f}(seam:Separated S J st uv sv ut):
    S.density β st W*S.density β uv W=S.density β sv W*S.density β ut W:=by
  let a (U:Config G f)(k:S.SitesChoice):=branch S β U W k
  have pair (U V:Config G f):S.density β U W*S.density β V W=∑t:S.SitesChoice×S.SitesChoice,a U t.1*a V t.2:=by
    rw [measured,measured,Fintype.sum_prod_type];simp only [a,sum_mul,mul_sum];exact sum_comm
  rw [pair,pair]
  calc
    _ = ∑t:S.SitesChoice×S.SitesChoice,a sv ((exchange S J) t).1*a ut ((exchange S J) t).2:=
      sum_congr rfl fun t _=>swap S legal β W J seam t.1 t.2
    _ = _ :=Equiv.sum_comp (exchange S J) (fun t:S.SitesChoice×S.SitesChoice=>a sv t.1*a ut t.2)

end YM.Integration.WilsonRegisteredRectangleFrameSwap
