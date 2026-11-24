import YM.Integration.WilsonSeparatedPrefixMovingFixedCapture
import YM.Integration.WilsonSeparatedPrefixMovingExteriorTaylor
import YM.Integration.WilsonSeparatedPrefixMovingNearReturn

/-! Rooted income for all finite moments of the actual common position.
The same bounded multiplier is applied to the original and comparison
rows before the financed cover capture and its original dual test. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingCenterMoments
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore MeasureTheory
open scoped BigOperators Topology Classical




variable {G:Gauge}{H:Hol G}{r d D k u e n:ℕ}{C W W' V L:Credit}

def monomial (o:CellR)(axis:Fin d → Fin 4):Lounge:=
  ⟨fun z=>∏i:Fin d,(z.val (axis i)-o.val (axis i)),by
    apply continuous_finsetProd
    intro i _
    exact ((continuous_apply (axis i)).comp continuous_subtype_val).sub continuous_const⟩

theorem bounded (o:CellR)(axis:Fin d → Fin 4)(z:CellR): |monomial o axis z|  ≤  1:=by
  change |∏i:Fin d,((z.val-o.val) (axis i))| ≤ 1
  rw [Finset.abs_prod]
  apply Finset.prod_le_one (fun _ _=>abs_nonneg _)
  intro i _
  calc |(z.val-o.val) (axis i)|  ≤  ‖z.val-o.val‖:=by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (z.val-o.val) (axis i)
       _  ≤  1:=(norm_sub_le _ _).trans (by linarith [c_norm z,c_norm o])

def paint (a:Lounge):Lounge→L[ℝ]Lounge:=(ContinuousLinearMap.mul ℝ Lounge) a

def ink (D:ℕ)(a:Lounge):Lounge→L[ℝ]Vote D:=
  (HourFace dayMeasure D).comp (paint a)

def captured {Q:Fin (n+1) → SealR G}(A:Levels G)(C:ChartRatio G)(φ:Wilt Q)(X:Herit Q)
    (m b N D:ℕ)(a:Lounge):TowerS G D:=
  tuftV (ink D a) (LodeStar A C φ X m b N (paceT A.S m b))

theorem unit (D:ℕ):(ink D 1)=HourFace dayMeasure D:=by
  ext f j
  change (HourFace dayMeasure D ((1:Lounge)*f)) j=_
  rw [one_mul]

private theorem integrate (a:Lounge)(bill:∀z:CellR,|a z|  ≤  1)(D:ℕ)(B:ℝ)
    (P:ChamberTen G Lounge r)(sale:∀z:CellR,Fruit 0 1 u (fun x=>P x z) B):
    Fruit 0 1 u (fun x=>ink D a (P x)) B:=by
  apply MintD dayMeasure D (fun x=>paint a (P x))
  intro z
  have hz:=((sale z).μ (a z)).more (mul_le_of_le_one_left (sale z).C (bill z))
  exact hz

theorem original (H:Hol G)(Q:Fin (n+1) → SealR G)(E W V W' L:Credit)(e u D:ℕ):
    ∃C:Credit,∀(R:Realm G (e+1) E),HorizonP H R W V Q → SpringD R (capP Q) u (capP Q+2) W' → 
      Dormitory R (capP Q) u L → ∀ m b c N M (φ:Wilt Q)(X Y:Herit Q)(A B:Fin (n+1) → ℝ)(Z δ:ℝ),
      R.anchor ≤ b → b ≤ m → m ≤ c → c ≤ N → c ≤ M → PadRank R b m Z → Bough Q φ (paceT R.draws.S m b) Z B → 
      R.tempC m c ≤ δ → Sitting Q A e δ X Y → ∀(a:Lounge), (∀z:CellR,|a z| ≤ 1) → ∀i ≤ e,∀j:ℕ,
        YieldP 0 1 u (C.buy Z * ∏i,B i*A i) δ
          ((captured R.draws R.paid φ X m b N D a).2 i j)
          ((captured R.draws R.paid φ Y m b M D a).2 i j):=by
  obtain ⟨C,h⟩:=Captures H Q E W V W' L e u
  refine ⟨C,?_⟩
  intro R home v t m b c N M F X Y A B Z δ hv hm hb hn hM hz hy hδ l a bill i hi j
  let η:=paceT R.draws.S m b
  let S:=LodeStar R.draws R.paid F X m b N η
  let T:=LodeStar R.draws R.paid F Y m b M η
  have hh (z:CellR):=(h R home v t m c b N M F X Y A B Z η δ z hv hm hb hn hM hz hy hδ l).heapS i j hi
  change YieldP _ _ _ _ _ (fun x=>ink D a (S.2 i j x)) (fun x=>ink D a (T.2 i j x))
  refine ⟨integrate a bill D _ (S.2 i j) (fun z=>(hh z).wax),
    integrate a bill D _ (T.2 i j) (fun z=>(hh z).wane),?_⟩
  have he:(fun x=>ink D a (S.2 i j x))-(fun x=>ink D a (T.2 i j x))=
    fun x=>ink D a ((S-T).2 i j x):=funext fun x=>(map_sub (ink D a) _ _).symm
  rw [he]
  exact integrate a bill D _ ((S-T).2 i j) (fun z=>(hh z).toll)

end YM.Integration.WilsonSeparatedPrefixMovingCenterMoments
