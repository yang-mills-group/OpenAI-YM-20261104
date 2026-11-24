import YM.Integration.WilsonIndependentMatchedMixBudget

/-! Exact raw-minus-fitted two-source decomposition on the actual compact
top profile, with all three marked terms inside the same normalized Wilson
continuation at the same declared rank. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedTotalTop
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical
open WilsonIndependentMatchedSeatedIncome WilsonIndependentMatchedCoveredSeats
variable {G:Gauge}{h D k e u₀:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}
    {v:Rails h k u₀ e}{E W K U:Credit}

open WilsonIndependentMatchedCutBudget WilsonIndependentMatchedFittedSeat

open WilsonIndependentMatchedMixBudget
variable {V W':Type*}[NormedAddCommGroup V][NormedSpace ℝ V]
  [NormedAddCommGroup W'][NormedSpace ℝ W']

private lemma tuft_add (f:V→L[ℝ]W')(P Q:Era G V):tuftV f (P+Q)=tuftV f P+tuftV f Q:=
  Prod.ext (funext fun n=>(ply f.toLinearMap).map_add (P.1 n) (Q.1 n))
    ((ply f.toLinearMap).map_add P.2 Q.2)

private lemma shoe_add (P Q:TowerS G D)(φ:Rarity D)(x y:ℝ)(b:Cover):
    shoe (P+Q) φ x y b=shoe P φ x y b+shoe Q φ x y b:=by
  unfold shoe;rw [tuft_add];rfl

private lemma pupil_add (P Q:TowerS G D)(φ:Rarity D)(x y:ℝ)(d:ℕ):
    pupil d (P+Q) φ x y=pupil d P φ x y+pupil d Q φ x y:=by
  simp only [pupil,shoe_add,smul_add,Finset.sum_add_distrib]

theorem placed (X:CutsP H T p v E W K U)(a:ℝ)(φ:Rarity D)(y:ℝ)(o:CellR):
    word (a • X.pt) φ (paceT X.ax.S X.m (X.m+X.i)) y o h=
      seat X a φ y o X.i+receiving X a φ y o X.i:=by
  rw [WilsonIndependentMatchedFittedSeat.inlet,←WilsonIndependentMatchedFittedSeat.taken X a,WilsonIndependentMatchedFittedSeat.scaled]
  unfold WilsonIndependentMatchedCoveredSeats.seat word locale
  rw [pupil_add,tuft_add]

private lemma web_add {Z:Type*}{i j:ℕ}(P Q:Ten ℝ Z i)(S:Ten ℝ Z j)(r:ℕ):
    webT (P+Q) S r=webT P S r+webT Q S r ∧
    webT S (P+Q) r=webT S P r+webT S Q r:=by
  constructor <;> funext x <;> unfold webT <;> split <;> simp_all [add_mul,mul_add]

private lemma swirl_plus {Z:Type*}{r:ℕ}(P Q:Ten ℝ Z r):swirl (P+Q)=swirl P+swirl Q:=by
  funext x
  simp only [swirl,Pi.smul_apply,Finset.sum_apply,Pi.add_apply,Finset.sum_add_distrib,smul_add]

private lemma knit_add {Z:Type*}(P Q S:Gen ℝ Z):
    knitS (P+Q) S=knitS P S+knitS Q S ∧ knitS S (P+Q)=knitS S P+knitS S Q:=by
  constructor <;> funext i
  · simp only [knitS,Pi.add_apply,(web_add ..).1,Finset.sum_add_distrib,swirl_plus]
  · simp only [knitS,Pi.add_apply,(web_add ..).2,Finset.sum_add_distrib,swirl_plus]

private lemma woad_add {Z:Type*}(P Q S:Pal ℝ Z):
    woad (P+Q) S=woad P S+woad Q S ∧ woad S (P+Q)=woad S P+woad S Q:=by
  constructor <;> funext i
  · simp only [woad,Pi.add_apply,(knit_add ..).1,Finset.sum_add_distrib]
  · simp only [woad,Pi.add_apply,(knit_add ..).2,Finset.sum_add_distrib]

theorem binary (P Q S:Era G ℝ):
    agateV (P+Q) S=agateV P S+agateV Q S ∧ agateV S (P+Q)=agateV S P+agateV S Q:=
  ⟨Prod.ext (funext fun n=>(woad_add (P.1 n) (Q.1 n) (S.1 n)).1) (woad_add P.2 Q.2 S.2).1,
   Prod.ext (funext fun n=>(woad_add (P.1 n) (Q.1 n) (S.1 n)).2) (woad_add P.2 Q.2 S.2).2⟩

private lemma linear {e₀ m n N:ℕ}{C:Credit}(R:Realm G (e₀+1) C)(live:m ≤ n)(top:n ≤ N)
    (P Q:Era G ℝ)(hP:Auth k P)(hQ:Auth k Q):
    cruises R.draws R.paid N k n m (P+Q)=
      cruises R.draws R.paid N k n m P+cruises R.draws R.paid N k n m Q:=by
  have delta:=cruisePlus R.draws live R.hG R.green top (hP.add hQ) hQ
  rw [add_sub_cancel_right] at delta
  exact sub_eq_iff_eq_add.mp delta.symm

/-- The signed full product is a sum of exactly the two single residual
rows and the double residual row on every receiving date. -/
theorem transferred {e₀ m n N:ℕ}{C:Credit}(R:Realm G (e₀+1) C)(live:m ≤ n)(top:n ≤ N)
    (X Y P Q:Era G ℝ)(hx:Auth k X)(hy:Auth k Y)(hp:Auth k P)(hq:Auth k Q):
    let read:=fun A B:Era G ℝ=>cruises R.draws R.paid N (k+k) n m (agateV A B)
    read (X+P) (Y+Q)-read P Q=read X Y+read X Q+read P Y:=by
  intro read
  dsimp only [read]
  rw [(binary X P (Y+Q)).1,(binary Y Q X).2,(binary Y Q P).2]
  rw [linear R live top _ _ ((hx.manor hy).add (hx.manor hq)) ((hp.manor hy).add (hp.manor hq)),
    linear R live top _ _ (hx.manor hy) (hx.manor hq),linear R live top _ _ (hp.manor hy) (hp.manor hq)]
  abel

end YM.Integration.WilsonIndependentMatchedTotalTop
