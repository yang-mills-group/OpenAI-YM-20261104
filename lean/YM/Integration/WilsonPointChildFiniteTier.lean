import YM.Integration.WilsonPointChildFiniteSeam
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPointChildFiniteTier
open Function Finset Lattice RG Wilson Laurent Precision PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos WilsonCoeffUV.Blue
open WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Winding WilsonCoeffUV.Bank.PathCost
open WilsonCoeffUV.Embroider WilsonCoeffUV.Bank.Mosaic.Near AnalyticNext.QuarticMatch.Sheets
open WilsonVacuumPreResetFiniteHeatFinance (gross)
open WilsonVacuumPreResetFiniteHeatTable (table)
open scoped Classical BigOperators
open WilsonPointChildScalarSlot
variable {G:Gauge}

theorem original (G:Gauge)(e l:ℕ):
    ∃v:Gear G → ℝ,∃k:ℕ,∀(Q:Realm G (e+1) Credit.leanC) j N (a:Q.anchor ≤ j),
    v (Q.mint j a).gear ≤ Q.cash Credit.leanC j → j<N → ∀(n:Side)(X:Era G ℝ),Auth l X → 
    let f:=n*(loose Q.draws j).L
    let B:=gross (Q.y j) f
    ∀η δ A:ℝ,0<η → η ≤ 1 → 0<δ → 0<A → 
    table Q.draws Q.paid e N (j+1) f η → 
    (∀b ≤ e,∀t x,|X.1 f b t x-plume (X.2 b t) f x| ≤ δ) → 
    (∀b ≤ e,∀t x,|plume (X.2 b t) f x| ≤ A) → 
    (∀b ≤ e,∀t,Wig terrain (fun _:Unit=>0) (WilsonPointChildQuoteWidth.quote (Q.mint j a).gear) A {()} (X.2 b t)) → 
    ∀i ≤ e,∀r x,let Y:=verseI Q.draws Q.paid j N l X
       ‖Y.1 n i r x-plume (Y.2 i r) n x‖ ≤ 
         B^k*(δ+A*η+A*Real.exp (-(n.val:ℝ)/(512*Q.y j))):=by
  let T:=Fin (e+1)×Fin (l+e+1)
  choose u d take using fun t:T=>WilsonPointChildFiniteSeam.original G e t.1.val l t.2.val (by omega)
  let v(I:Gear G):=∑t:T,|u t I|
  let k:=∑t:T,d t
  refine ⟨v,k,?_⟩
  intro Q j N a ticket live n X clear f B η δ A p small pd pa bank previous hull width i paid r x Y
  have y:=Q.depth j a
  have B1:1 ≤ B:=y.trans (le_mul_of_one_le_right (zero_le_one.trans y)
    (one_le_pow₀ (by linarith [Nat.cast_nonneg (α:=ℝ) f.val])))
  by_cases kept:r ≤ l+i
  · let t:T:=(⟨i,by omega⟩,⟨r,by omega⟩)
    let I:=(Q.mint j a).gear
    have use:u t I ≤ v I:=(le_abs_self _).trans
      (Finset.single_le_sum (fun t _=>abs_nonneg (u t I)) (mem_univ t))
    have deg:d t ≤ k:=Finset.single_le_sum (fun t _=>Nat.zero_le (d t)) (mem_univ t)
    have act:=take t Q j N a (use.trans ticket) live n X clear η δ A p small pd pa bank previous hull width x
    apply act.trans
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ B1 deg) (by positivity)
  · have cert:Auth l Y:=clear.verse Q.draws live Q.hG Q.green
    rw [cert.span n i r (by omega),cert.coverN i r (by omega),plume_zero]
    simp only [Pi.zero_apply,sub_self,norm_zero]
    positivity

end YM.Integration.WilsonPointChildFiniteTier
