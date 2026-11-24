import YM.Integration.WilsonIndependentSpoutMasterRawSections
import YM.Integration.WilsonIndependentSpoutMasterOrbit

/-! Whole-word wages on the actual finite normalized inlet. The raw restart factors are kept in the torus term. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutMasterWordWage
open Function Filter Finset Lattice Wilson Tree RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider Source Source.Drops Labels FVA2
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonPositionProgramNormalizedMaster (fee)
open WilsonIndependentMatchedOpeningMenu (charge toll)
open WilsonIndependentSpoutNormalizedMaster (vector)
open WilsonIndependentMatchedFreshInverseIncome (age)
open scoped Classical BigOperators Topology
variable {G:Gauge}{n h H k u e:ℕ}

theorem individual {Q:Fin (n+1)→SealR G}(b:Herit Q)(i:Fin (n+1))(a:Alma (Q i).F)(j e:ℕ)(early:j ≤ e):
    ‖PowerSeries.coeff j (b i a)‖ ≤ fee b e i:=by
  let t:Fin (e+1):=⟨j,by omega⟩
  exact (Finset.single_le_sum (f:=fun r:Fin (e+1)=>‖PowerSeries.coeff r.val (b i a)‖)
    (fun _ _=>norm_nonneg _) (Finset.mem_univ t)).trans
    (Finset.single_le_sum (f:=fun a:Alma (Q i).F=>∑r:Fin (e+1),‖PowerSeries.coeff r.val (b i a)‖)
      (fun _ _=>Finset.sum_nonneg fun _ _=>norm_nonneg _) (Finset.mem_univ a))

private theorem tally (F:Cost)(q:ℕ)(S:ℝ)(pay:∀t ≤ q,‖PowerSeries.coeff t F‖ ≤ S):
    toll q F ≤ ((q+1:ℕ):ℝ)*S:=by
  have amounts (t:ℕ)(ht:t∈range (q+1)):
      ‖PowerSeries.coeff t (TaylorWick.into F)‖ ≤ S:=by
    have keep (x:ℝ):‖Complex.ofRealHom x‖=‖x‖:=Complex.norm_real x
    simpa only [TaylorWick.into,PowerSeries.coeff_map,keep] using pay t (by have:=Finset.mem_range.mp ht; omega)
  simpa only [WilsonIndependentMatchedOpeningMenu.toll,WilsonPhysicalMarkedDefect.RawProduct.belt,Finset.sum_const,Finset.card_range,nsmul_eq_mul] using
    (Finset.sum_le_sum amounts)

variable (R:Run G)(d D:Fin (n+1)→ℕ)(cut:∀i,d i<D i)
local notation "Q" => (deck (G:=G) d D cut)
local notation "L" => R.family.path.levels

def wages (A B:Fin (n+1)→Credit)(m K q:ℕ)(cap:Fin (n+1)→ℝ)(φ:∀i,Rarity (D i))
    (x:Fin (n+1)→ℝ)(y:ℝ)(M:Fin (n+1)→ℝ)(i:Fin (n+1)):ℝ:=
  let raw:=(A i).buy (age L (zz L) m K)*((Fintype.card (Alma (Q i).F):ℝ)*(B i).buy (zz L m)*cap i)
  ((q+1:ℕ):ℝ)*raw*∑a:Alma (Q i).F,|BasePrice (d i) (φ i) (x i) y| *(‖jewelBloom (cut i) a‖*|M i|)

theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (head:h<H)(rails:Rails h k u e)(cap₀:capP Q ≤ k):
    ∃A B:Fin (n+1)→Credit,∀ᶠ j:ℕ in atTop,∀m K,j ≤ m → m ≤ K → ∀(b:Herit Q)(cap:Fin (n+1)→ℝ),
    (∀i,fee b e i ≤ cap i) → ∀(φ:∀i,Rarity (D i))(x:Fin (n+1)→ℝ)(y:ℝ)(M:Fin (n+1)→ℝ)(q:ℕ),q ≤ e →
    ∀i,charge R (cut i) q (d i) (vector R d D cut b m K i) (φ i) (x i) y (M i) ≤
      wages R d D cut A B m K q cap φ x y M i:=by
  obtain ⟨A,B,priced⟩:=WilsonIndependentSpoutMasterRawSections.original R d D cut simple v funded head rails cap₀
  refine ⟨A,B,?_⟩
  filter_upwards [priced] with j rates
  intro m K awake pre b cap covered φ x y M q early i
  have nn:0 ≤ fee b e i:=by unfold fee;positivity
  let raw:=(A i).buy (age L (zz L) m K)*((Fintype.card (Alma (Q i).F):ℝ)*(B i).buy (zz L m)*cap i)
  have costs a:toll q (vector R d D cut b m K i a) ≤ ((q+1:ℕ):ℝ)*raw:=by
    apply tally
    intro t depth
    exact rates m K awake pre b i (cap i) (nn.trans (covered i)) (fun s hs a=>(individual b i a s e hs).trans (covered i))
      t (depth.trans early) a
  unfold charge wages
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun a _=>?_
  let base:=BasePrice (d i) (φ i) (x i) y
  let V:=vector R d D cut b m K i a
  have nz:0 ≤ toll q V:=by
    unfold WilsonIndependentMatchedOpeningMenu.toll WilsonPhysicalMarkedDefect.RawProduct.belt
    exact Finset.sum_nonneg fun _ _=>norm_nonneg _
  apply le_trans _ (mul_le_mul_of_nonneg_right (costs a) (mul_nonneg (abs_nonneg base) (mul_nonneg (norm_nonneg _) (abs_nonneg _))))
  apply mul_le_mul_of_nonneg_left _ nz
  apply (le_abs_self _).trans_eq
  rw [abs_mul,abs_mul,abs_of_nonneg (norm_nonneg (jewelBloom (cut i) a))]
  rfl
end YM.Integration.WilsonIndependentSpoutMasterWordWage
end
