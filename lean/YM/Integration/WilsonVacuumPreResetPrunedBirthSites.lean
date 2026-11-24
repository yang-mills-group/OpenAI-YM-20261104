import YM.RG01Estimate.InheritedSales
import YM.RG01Estimate.ExtraVoice
import YM.UVExt.TopOrbits
import YM.Corona.Spend

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetPrunedBirthSites
open Function Set Lattice RG Wilson Precision Ovens Ovens.Pipes WilsonStartup WilsonStartup.Start
open Progress.DirectedRecipe Progress.DirectedRecipe.Rack RG01Estimate
open Push Push.AbsoluteSums AnalyticBridge ConnectedActivityE6 Coat Function Filter
open scoped Classical BigOperators

abbrev Shapes := Signed × PlaqAxes

def key {n:Side}(u:Site n × Shapes):Key n:=(u.2.1,(u.1,u.2.2))

private def realNames (n:Side):(Site n × Shapes) ↪ ℕ where
  toFun u:=Padded.index (Sum.inl (key u):Sheet n)
  inj' := by
    rintro ⟨x,s,a⟩ ⟨y,t,b⟩ h
    have h₁: (Sum.inl (key (x,s,a)):Sheet n) = Sum.inl (key (y,t,b)):=
      congrArg Prod.fst ((Padded.codec (Sheet n)).symm.injective h)
    simpa [key,and_left_comm,and_assoc] using h₁

def roster (G:Gauge)(n:Side):Evoc.Lex Shapes n:= (realNames n).trans (upE (dictionary G n))

def filed {G:Gauge}(n:Side)(W:PathData G)(clip:Clip)(P:BudgetPoint)(β:ℝ):Rep G n:=
  finish W clip P (dictionary G n) (payload clip P G n β) β 0

variable {G:Gauge}{n c:Side}(W:PathData G)(clip:Clip)(P:BudgetPoint)(β:ℝ)
local notation "U₀" => filed n W clip P β

theorem address (u:Site n×Shapes):
    (U₀).activities.reg (roster G n u)=(key u).addrE:=by
  change (drawer G n).reg (upE (dictionary G n) _)=_
  rw [reg_up]
  change eInfo (Padded.name (Sheet n) (Padded.index (Sum.inl (key u):Sheet n)))=_
  simp [Padded.name,Padded.index,eInfo]

theorem zero {i:ℕ}(off:i∉Set.range (roster G n)):
    (U₀).activities.E i=0:=by
  let X:=dictionary G n
  let d:=payload clip P G n β
  change stuff (upE X) d.regular i=0
  by_cases hi:i∈Set.range (upE X)
  · obtain ⟨j,rfl⟩:=hi
    rw [stuffed]; change (if Padded.fixed (Sheet n) j then written clip
      (Padded.name (Sheet n) j) β else 0)=0
    split_ifs with hj
    · cases hj₀:Padded.name (Sheet n) j with
      | inr v => rfl
      | inl v =>
        obtain ⟨s,x,t⟩:=v
        exfalso
        apply off
        refine ⟨(x,s,t),?_⟩
        change upE X (Padded.index (Sum.inl (s,(x,t)):Sheet n)) = upE X j
        congr 1
        apply (Padded.codec (Sheet n)).injective
        rw [Padded.index,Equiv.apply_symm_apply]
        exact Prod.ext hj₀.symm hj.symm
    · rfl
  · exact blank (upE X) d.regular hi

theorem mask (S:StepData c n):Evoc.StageMask (U₀) S (roster G n) 3:=by
  constructor
  · intro x;rw [address]; exact (key x).native_mem
  · intro x z hz;rw [address] at hz
    have fine:= (key x).nearby hz
    change separation x.1 z≤2 at fine
    have bound:=Corona.foreshorten S.ratio x.1 z
    have pos:=S.ratio.count.pos
    by_contra! hx
    have lower:=Nat.mul_le_mul_left S.ratio.count.val (show 4 ≤ separation (S.ratio.parent x.1) (S.ratio.parent z) by omega)
    omega

theorem debit :Inherit.Debits (U₀) (Set.range (roster G n))ᶜ 0:=by
  refine ⟨fun _=>0,fun i=>?_,fun z=>?_⟩
  · have hv:(Inherit.selected (U₀) (Set.range (roster G n))ᶜ).E i=0:=by
      unfold Inherit.selected; dsimp only
      split_ifs with yes
      · exact zero W clip P β yes
      · rfl
    rw [hv]
    simpa only [abs_zero] using! CouplingShape.sup_const (G:=G) (p:=(U₀).p)
      (X:=((U₀).activities.reg i).support) (o:=((U₀).activities.reg i).site) 0
  · simp only [SumBudget,BudgetPoint.mass,mul_zero,ite_self,summable_zero,true_and,tsum_zero]
    exact ⟨fun _=>le_rfl,le_rfl⟩

end YM.Integration.WilsonVacuumPreResetPrunedBirthSites
