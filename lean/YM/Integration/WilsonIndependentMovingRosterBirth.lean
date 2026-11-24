import YM.Integration.WilsonSeparatedPrefixMovingOldPair
import YM.WilsonCoeffUV.Product.Report.WaveMark

/-! The complete first deposit of a finite near roster. The native first-join
theorem uses the ordinary conditional product on the actual finite top. Its
last block converts the coarse gain into powers of the incoming child mesh. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMovingRosterBirth
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open Finset
open scoped BigOperators Topology Classical
variable {G:Gauge}{n e:ℕ}{E:Credit}

def charge (Q:Fin (n+1)→SealR G)(X:Herit Q)(e:ℕ)(B:Fin (n+1)→ℝ):ℝ:=
  ∏s,B s*WilsonSeparatedPrefixMovingOwnDate.fee (Q s) e (X s)

private lemma entered (Q:Fin (n+1)→SealR G)(X:Herit Q)(e:ℕ){δ:ℝ}(pos:0≤δ):
    Sitting Q (fun s=>WilsonSeparatedPrefixMovingOwnDate.fee (Q s) e (X s)) e δ X X:=by
  constructor
  · intro s;unfold WilsonSeparatedPrefixMovingOwnDate.fee;positivity
  · intro s j hj v
    refine twain.one _ _ pos ?_
    exact (Finset.single_le_sum (f:=fun i:Fin (e+1)=>‖coeff i.val (X s v)‖)
      (fun _ _=>norm_nonneg _) (Finset.mem_univ (⟨j,by omega⟩:Fin (e+1)))).trans
        (Finset.single_le_sum (f:=fun v:Alma (Q s).F=>∑i:Fin (e+1),‖coeff i.val (X s v)‖)
          (fun _ _=>Finset.sum_nonneg fun _ _=>norm_nonneg _) (Finset.mem_univ v))

/-- The two actual finite tops and their full signed first deposits. The
registered angular discrepancy on the inputs is tested on the same births. -/
theorem twins (H:Hol G)(Q:Fin (n+1)→SealR G)(E W V S:Credit)(e u d:ℕ):
    ∃C:Credit,∀(R:Realm G (e+1) E),HorizonP H R W V Q →
    SpringD R (capP Q) u (capP Q+d) S →
    ∀(m j b N M:ℕ)(φ:Wilt Q)(X Y:Herit Q)(A B:Fin (n+1)→ℝ)(Z y δ:ℝ)(o:CellR),
    R.anchor≤m → m≤j → j<b → b≤N → b≤M → Compar R.draws.S R.y m (j+1)≤Z →
    Bough Q φ y Z B → δWarm R j b≤δ → Sitting Q A e δ X Y →
    let w:=paceT R.draws.S m (j+1)
    Fringed (capP Q) e u (paceT R.draws.S m j) (C.buy Z*w^d*(∏s,B s*A s)) δ
      (Ash R.draws R.paid φ X m j N y o) (Ash R.draws R.paid φ Y m j M y o):=by
  obtain ⟨fee,first⟩:=waveMark H Q E W V S e u d
  refine ⟨fee.prodC (E.powC d),?_⟩
  intro R home spring m j b N M φ X Y A B Z y δ o gate start edge capN capM clock geo allowed paid w
  have born:=first R home spring m j b N M φ X Y A B Z y δ o gate start edge capN capM clock geo allowed paid
  apply born.pay
  have timed:R.y j≤Z:=((PadRank.frugal R gate (start.trans (Nat.le_succ _))).year _ start (Nat.le_succ _)).trans clock
  have length:((R.draws.S.block j).val:ℝ)≤E.buy Z:=
    ((R.taxes j (gate.trans start)).height).trans (E.elder (R.depth _ (gate.trans start)) timed)
  have zero:0≤∏s,B s*A s:=Finset.prod_nonneg fun s _=>mul_nonneg (geo.lanes s).1 (paid.stock s)
  have nonneg:0≤fee.buy Z:=zero_le_one.trans (fee.purchase geo.pos)
  have hw:0<w:=pace_pos ..
  have step:w*(R.draws.S.block j).val=paceT R.draws.S m j:=pace_step ..
  change fee.buy Z*(paceT R.draws.S m j)^d*(∏s,B s*A s)≤_
  rw [Credit.products,Credit.power,←step,mul_pow]
  apply mul_le_mul_of_nonneg_right _ zero
  calc
    _≤fee.buy Z*(w^d*(E.buy Z)^d):=by gcongr
    _=_:=by ring

/-- All angular ranks, including the previously deposited scalar. A natural
root moment costs one child power per requested moment. -/
theorem original (H:Hol G)(Q:Fin (n+1)→SealR G)(E W V S:Credit)(e u extra:ℕ):
    ∃C:Credit,∀(R:Realm G (e+1) E),HorizonP H R W V Q →
    SpringD R (capP Q) u (capP Q+(u+extra)) S →
    ∀(m j N:ℕ)(φ:Wilt Q)(X:Herit Q)(B:Fin (n+1)→ℝ)(Z y:ℝ)(o:CellR),
    R.anchor≤m → m≤j → j<N → Compar R.draws.S R.y m (j+1)≤Z → Bough Q φ y Z B →
    let w:=paceT R.draws.S m (j+1)
    let D:=Ash R.draws R.paid φ X m j N y o
    Auth (capP Q) D ∧ Flush e u (paceT R.draws.S m j) D (C.buy Z*w^(u+extra)*charge Q X e B) ∧
      Flush e u 1 D (C.buy Z*w^extra*charge Q X e B):=by
  obtain ⟨C,sold⟩:=twins H Q E W V S e u (u+extra)
  refine ⟨C,?_⟩
  intro R home spring m j N φ X B Z y o gate start edge clock geo w D
  let bill:=fun s=>WilsonSeparatedPrefixMovingOwnDate.fee (Q s) e (X s)
  have enrolled:=entered Q X e (le_max_left 0 (δWarm R j (j+1)))
  have paid:=sold R home spring m j (j+1) N N φ X X bill B Z y (max 0 (δWarm R j (j+1))) o
    gate start (Nat.lt_succ_self j) edge edge clock geo (le_max_right _ _) enrolled
  refine ⟨paid.pen,paid.f_l,?_⟩
  have rent:=WilsonSeparatedPrefixMovingOldPair.promote (pace_pos R.draws.S m j)
    (pace_le R.draws.S start) paid.f_l
  have hr:0<paceT R.draws.S m j:=pace_pos ..
  have hw:0<w:=pace_pos ..
  have step:w*(R.draws.S.block j).val=paceT R.draws.S m j:=pace_step ..
  have big:1≤((R.draws.S.block j).val:ℝ):=by exact_mod_cast (R.draws.S.block j).pos
  have smaller:w≤paceT R.draws.S m j:=by rw [←step];exact le_mul_of_one_le_right hw.le big
  have ratio:(paceT R.draws.S m j ^ u)⁻¹*w^u≤1:=
    (inv_mul_le_one₀ (pow_pos hr u)).mpr (pow_le_pow_left₀ hw.le smaller _)
  have cq:0≤C.buy Z:=zero_le_one.trans (C.purchase geo.pos)
  have jq:0≤charge Q X e B:=Finset.prod_nonneg fun s _=>mul_nonneg (geo.lanes s).1 (enrolled.stock s)
  have wage:0≤C.buy Z*w^extra*charge Q X e B:=by positivity
  have lower:(paceT R.draws.S m j^u)⁻¹*(C.buy Z*w^(u+extra)*charge Q X e B)≤C.buy Z*w^extra*charge Q X e B:=by
    rw [pow_add]
    calc
      _=((paceT R.draws.S m j^u)⁻¹*w^u)*(C.buy Z*w^extra*charge Q X e B):=by ring
      _≤1*(C.buy Z*w^extra*charge Q X e B):=mul_le_mul_of_nonneg_right ratio wage
      _=_:=one_mul _
  exact ⟨wage,fun a ha r hh=>(rent.2 a ha r hh).more lower⟩

end YM.Integration.WilsonIndependentMovingRosterBirth
