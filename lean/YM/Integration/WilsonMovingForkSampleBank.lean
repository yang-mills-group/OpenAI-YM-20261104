import YM.Integration.WilsonMovingForkLocatedSamples

/-! Rows and their signed multiplicities for a single reflected determining
test. Every near sample and every basis comparison reuses the declared far arm. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkSampleBank
open PhysicalNext.Repeat.Legato RG17 WilsonMovingForkProbeMaster
open Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register FVA2.O MS MS.Land MS.Fleet MS.Theater
open scoped Classical BigOperators
variable {G:Gauge}{n h:ℕ}{T:Type}
def arity (n:ℕ) : Option (Dframe.Toon G h)→ℕ
  | none=>n+1
  | some _=>2

def ports (j:T)(k:Option (Dframe.Toon G h)):Fin (arity n k)→Seat G n h T:=
  match k with
  | none=>whole j
  | some i=>pair i j

variable {ι κ:Type}
abbrev Index (ι κ:Type)(G:Gauge)(h:ℕ):=ι ⊕ (Dframe.Toon G h × κ)
def kind :Index ι κ G h→Option (Dframe.Toon G h)
  | .inl _=>none
  | .inr (i,_)=>some i

def site (x:ι→Points (n+1))(z:κ→Points 2)(a:Index ι κ G h):Points (arity n (kind a)):=
  match a with
  | .inl i=>x i
  | .inr (_,b)=>z b

def mix (μ:ι→ℂ)(ν:κ→ℂ)(c:Dframe.Toon G h→ℂ):Index ι κ G h→ℂ
  | .inl i=>μ i
  | .inr (k,b)=> -(c k * ν b)

theorem contrast [Fintype ι][Fintype κ](μ:ι→ℂ)(ν:κ→ℂ)(c:Dframe.Toon G h→ℂ)
    (f:Index ι κ G h→ℂ):
    ∑a,mix μ ν c a*f a=(∑i,μ i*f (.inl i))-∑k,c k*∑b,ν b*f (.inr (k,b)):=by
  rw [Fintype.sum_sum_type,Fintype.sum_prod_type]
  simp only [mix,neg_mul,Finset.sum_neg_distrib,Finset.mul_sum,mul_assoc,sub_eq_add_neg]

theorem variation [Fintype ι][Fintype κ](μ:ι→ℂ)(ν:κ→ℂ)(c:Dframe.Toon G h→ℂ):
    (∑a,‖mix μ ν c a‖)=(∑i,‖μ i‖)+∑k,‖c k‖*∑b,‖ν b‖:=by
  rw [Fintype.sum_sum_type,Fintype.sum_prod_type]
  simp only [mix,norm_neg,norm_mul,Finset.mul_sum]

end YM.Integration.WilsonMovingForkSampleBank
end
