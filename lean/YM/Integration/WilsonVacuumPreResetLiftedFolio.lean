import YM.Integration.WilsonVacuumPreResetLiftedSite
import YM.Integration.WilsonVacuumPreResetPeriodCatalogue

/-! Finite rooted selection in the actual original printed listing. The raw
covering sequence and the signed orientation are common to different tori. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetLiftedFolio
open Function Finset Set Lattice RG Marker Wilson WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open Comparison.Density Comparison.Density.Render AnalyticBridge VerifiedReset Collection Quotes WilsonStartup
open IterationFour.Vacuum Extra.Iteration Push.AbsoluteSums WilsonVacuumPreResetLiftedSite
open WilsonVacuumPreResetPeriodEntries
open scoped Classical BigOperators
variable {G:Gauge}{n m:Side}

def legs (a:PrismA G)(t q:ℕ):Finset ℕ:=(range t).filter fun i=>(a.cells i).length≤q

def seats (n:Side)(a:PrismA G)(t q:ℕ):Finset ℕ:=
  ((univ:Finset (Seat n)) ×ˢ legs a t q).map (numbering (Cycle n)).symm.toEmbedding

def selected (n:Side)(t q:ℕ):SeriesA G→Finset ℕ
  | []=>∅
  | a::l=>((selected n t q l).disjSum (seats n a t q)).map Payload.coding.symm.toEmbedding

def reading (B:BudgetPoint)(σ C:ℝ)(k:ℕ→ℕ→ℝ)(Z:SeriesA G)(t q:ℕ)(x:Site n)(U:Config G n):ℝ:=
  let A:=entries n B σ C Z k
  ∑i∈selected n t q Z,if (A.reg i).site=x then A.E i U else 0

private theorem split (B:BudgetPoint)(σ C:ℝ)(k:ℕ→ℕ→ℝ)(a:PrismA G)(Z:SeriesA G)(t q:ℕ)(x:Site n)(U:Config G n):
    reading B σ C k (a::Z) t q x U=reading B σ C k Z t q x U+
      ∑s:Signed,∑i∈legs a t q,k a.grade (a.rise+2)*
      (FundedCorrectedPeriod.piece n B σ C a).packet.action (index x s i) U:=by
  let P:=(FundedCorrectedPeriod.piece n B σ C a).packet
  let A:=entries n B σ C Z k
  let w:=k a.grade (a.rise+2)
  change (∑j∈((selected n t q Z).disjSum (seats n a t q)).map Payload.coding.symm.toEmbedding,
    if ((P.attach w A).reg j).site=x then (P.attach w A).E j U else 0)=_
  simp only [sum_map,Equiv.toEmbedding_apply,sum_disjSum,Payload.attach,Function.comp_apply,
    Equiv.apply_symm_apply,Sum.elim_inl,Sum.elim_inr,Pi.smul_apply,smul_eq_mul]
  apply congrArg (fun b:ℝ=>reading B σ C k Z t q x U+b)
  unfold seats
  rw [sum_map,sum_product]
  simp only [Equiv.toEmbedding_apply]
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro s _
  let h (b:Site n)(i:ℕ):=w*P.action (index b s i) U
  change (∑b:Site n,∑i∈legs a t q,if (P.labels (index b s i)).site=x then h b i else 0)=_
  simp_rw [show ∀ b i,(P.labels (index b s i)).site=b from fun b i=>WilsonVacuumPreResetLiftedSite.position a B σ C b s i]
  rw [Finset.sum_comm]
  simp [h,w,P]

theorem original (B Q:BudgetPoint)(σ τ C E:ℝ)(k:ℕ→ℕ→ℝ)(Z:SeriesA G)(t q:ℕ)
    (room:4≤q)(x:Site n)(y:Site m)(U:Config G n)(V:Config G m)
    (agree:Agrees (Lattice.box q) (expandAt x U) (expandAt y V)):
    reading B σ C k Z t q x U=reading Q τ E k Z t q y V:=by
  induction Z with
  | nil=>simp [reading,selected]
  | cons a tail ih=>
    rw [split,split,ih]
    congr 1
    apply sum_congr rfl
    intro s _
    apply sum_congr rfl
    intro i hi
    rw [seated a B Q σ τ C E q i (mem_filter.mp hi).2 room s x y U V agree]

end YM.Integration.WilsonVacuumPreResetLiftedFolio
