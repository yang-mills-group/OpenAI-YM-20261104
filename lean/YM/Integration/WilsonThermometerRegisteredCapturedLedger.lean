/- One common before-test account for all original face partitions, including the unit. -/
import YM.Integration.WilsonThermometerRegisteredCapturedBucket

noncomputable section
namespace YM.Integration.WilsonThermometerRegisteredCapturedLedger
open RG Marker Multi Lattice Wilson QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Earn.Scene Finset
open Push Push.AbsoluteSums Push.Local Paths Comparison.RG02.Cumulants
open WilsonThermometerRegisteredCapturedBucket WilsonThermometerRegisteredCapturedNames
open scoped Classical BigOperators
variable {G:Gauge} {n:Side} {P:Earn.Passport n (Fin 3)} {R:Census (Fin 3)} {α ξ ι:Type}
variable {B:Earn.Passport n Unit} {D:Census Unit} (X:ι→Earn.Row P R G α)
variable {σ C:ℝ} {ord seats shelf:ℕ} (ages:Fin 3→ℕ) (w:Fin 3→ℝ)
variable (sold:Scene.Armada X w ages σ C ord seats shelf) (spent:∑v:Fin 3,ages v≤14)
variable (paths:Fin 3→Walk) (S:Earn.Binder B D) (t:α) (χ:R.Mode→ℂ) (test:ξ→ℂ)
abbrev Name := Σ s:R.Mode, Σ q:↥(shards R s), Names X q.val

def material (u:Name X):Earn.Row B D G ξ:=
  deposited X ages w sold spent paths S t (χ u.1) test u.2.1.val u.2.1.property u.2.2

def total (K:ℕ):ℝ:=∑s:R.Mode,∑q:↥(shards R s),
  invoice (ord:=ord) (σ:=σ) (C:=C) w S (χ s) q.val K

local notation "M"=>material X ages w sold spent paths S t χ test
theorem counted [Countable ι]:Countable (Name X):=by
  classical
  infer_instance

theorem paid (K:ℕ) (hσ:0≤σ) (reach:∀v,(paths v).length≤K) :
    SumBudget (fun u:Name X=>(M u).height σ) (total (ord:=ord) (σ:=σ) (C:=C) w S χ K):=by
  let f(s:R.Mode)(q:↥(shards R s)):ℝ:=invoice (ord:=ord) (σ:=σ) (C:=C) w S (χ s) q.val K
  have charter(s:R.Mode)(q:↥(shards R s)):
      SumBudget (fun u:Names X q.val=>(M ⟨s,q,u⟩).height σ) (f s q):=
    price X ages w sold spent paths S t (χ s) test q.val q.property K hσ reach
  have pos(s:R.Mode)(q:↥(shards R s)):0≤f s q:=
    (tsum_nonneg (charter s q).1).trans (charter s q).2.2
  apply sumBudget_sigma (a:=fun s=>∑q,f s q)
  · intro s
    exact sumBudget_sigma (charter s) (budget_finite (pos s) le_rfl)
  · exact budget_finite (fun s=>sum_nonneg fun q _=>pos s q) le_rfl

theorem original (K:ℕ) (hσ:0≤σ) (reach:∀v,(paths v).length≤K)
    (x:ξ) (incidence:∀v,stop S.center (paths v)=P.origin v) (unit:∀v,‖test v‖≤1)
    {capacity horizon:ℕ} (hc:1≤capacity) (hh:21≤horizon):
    Scene.Armada M (fun _=>1) (fun _=>21) σ (total (ord:=ord) (σ:=σ) (C:=C) w S χ K)
      (3*ord) capacity horizon :=by
  have home:(S.mode.val:Finset Unit)=univ:=by
    apply eq_univ_of_forall
    intro v
    exact (Subsingleton.elim v S.front) ▸ S.east
  have service(u:Name X):=(WilsonThermometerRegisteredCapturedBucket.original X ages w sold spent
    paths S t (χ u.1) test u.2.1.val u.2.1.property 1 one_ne_zero x 1 incidence unit u.2.2).2
  have priceAll:=paid X ages w sold spent paths S t χ test K hσ reach
  refine ⟨⟨?_,?_⟩,fun _=>zero_lt_one,?_,⟨fun u=>(service u).1,?_⟩,fun u=>(service u).2.1⟩
  · intro p
    exact (card_le_univ p.val).trans (by simpa using hc)
  · intro p
    calc
      _≤∑ _:Unit,21:=Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _=>by decide)
      _≤horizon:=by simpa using hh
  · intro y
    apply sumBudget_mono priceAll _ _ le_rfl
    · intro u
      split_ifs
      · simpa [Poly.toll] using (priceAll.1 u)
      · exact le_rfl
    · intro u
      dsimp only
      split_ifs
      · simp [Poly.toll]
      · exact priceAll.1 u
  · intro u
    refine ⟨(service u).2.2.1,?_⟩
    change (M u).lamp.toll=∑ _v∈S.mode.val,21
    simpa only [material,home,Finset.sum_const,Finset.card_univ,Fintype.card_unit,one_smul] using
      (service u).2.2.2
end YM.Integration.WilsonThermometerRegisteredCapturedLedger
