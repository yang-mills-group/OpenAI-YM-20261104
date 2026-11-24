import YM.FormalOPE.RG10.Profile.Crowns
/-! # Real tested linearity, pre-adjustment. Underlying re smeared convention. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Profile
open Function Maxwell Labels Extraction Filter Finset Extra.FD PertExtension MeasureTheory
    Topology Metric PertExtension.Position PertExtension.Physical PowerSeries Triangle
    InversionTop LatticePT Lattice Grid FlatFeed RG10.Position
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}{F:Frames G}{n d:ℕ}(P : Plan F)(q:ℕ+)(m j:ℕ)
local notation "Ω" => PertExtension.Physical.Profile
local notation "T" => offsets q
local notation "Fₛ" => Deck F d
variable (t: Test n)(u: Fin n → Deck F d)

def weigh (x:T n m) : Test n →L[ℝ] ℝ where
 toFun f:= (f (Grid.sample q m x)).re
 map_add' _ _:= rfl
 map_smul' _ _:= by simp
 cont:= Complex.continuous_re.comp (by fun_prop)

def press : Test n→L[ℝ] ℝ:= ∑ x:T n m, (nodes P q m j u x) • weigh (n:=n) q m x
lemma enter : press P q m j u t= coeff j (P.begins q m d (task t u)) := by
 rw [bill]; unfold press; rw [_root_.sum_apply]; apply sum_congr rfl; intro i _; change nodes _ _ _ _ _ _ * _= _; exact mul_comm ..

private def wrap (i:Fin n→Deck F d) : fps := ∏ k,P.poses q m d (u k) (i k)
local notation "S" => Finset.HasAntidiagonal.antidiagonal j
def firstGather : Test n→L[ℝ] ℝ:= ∑ i:Fin n→ Deck F d, ∑ z∈ S, coeff z.2 (wrap P q m u i) • press P q m z.1 i
lemma first_sum : firstGather P q m j u t= coeff j (P.dressed q m d (task t u)) := by
 unfold firstGather; rw [_root_.sum_apply]; change _=coeff j (∑ i:Fin n→ Deck F d, P.begins q m d (task t i)* wrap P q m u i)
 simp_rw [_root_.map_sum,coeff_mul]; apply sum_congr rfl; intro i _; rw [_root_.sum_apply]; apply sum_congr rfl; intro p _
 rw [smul_apply, enter]; exact mul_comm ..

def counted : Test n→L[ℝ] ℝ:= ∑ k∈range (j+1), coeff j (Peal.older F (P.dressed q m 6)^k) • firstGather P q m k u
lemma close : counted P q m j u t= coeff j (Plan.collect F P q m d (task t u)):=by
 rw [Plan.collect,Peal.action_on, AlignSeries.subst_finite (p:=Peal.older F (P.dressed q m 6)) (Triangle.inverse_zero _), counted, _root_.sum_apply]; apply sum_congr rfl; intro i _; rw [smul_apply, first_sum]; exact mul_comm ..

variable {P} {Y : Drivers}(Z: Patience P Y)
def owed : Test n→ₗ[ℝ] ℝ where
 toFun t:= coeff j (Z.Yield (task t u))
 map_add' a b:= by
   have hv: ∀ t : Test n, Y.Harvest (fun q m=>counted P q m j u t) (coeff j (Z.Yield (task t u))):=by intro t; simp_rw [close]; exact Z.collected _ j
   apply (hv _).ext; unfold Drivers.Harvest; simp_rw [_root_.map_add]; filter_upwards [hv a, hv b] with k hk hq; exact hk.add hq
 map_smul' x a:= by
   obtain hv:= Z.collected (task a u) j
   apply (Z.collected _ j).ext; unfold Drivers.Harvest; filter_upwards [hv] with k hk
   simp_rw [← close,_root_.map_smul]; simp_rw [← close] at hk; exact hk.const_mul x
@[simp] lemma owes : owed j u Z t = coeff j (Z.Yield (task t u)):= rfl
end YM.FormalOPE.RG10.Profile
