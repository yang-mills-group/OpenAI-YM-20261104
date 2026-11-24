import YM.FVAAlt2.Home.Stage
/-!
# Upper forecasts from exactly `LatticePT`
Weight-respecting polynomial extension to arbitrary real profiles in the
Position interface FIRST, assemble full multilinear basis. Top-regulator
only (conditioned period in another module). Coeff comparisons in SY.Estate
refer to true moment not logging on whole period.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Home.Profiles
open Lattice Function Finset Filter Topology Wilson Labels Source
open PertExtension PertExtension.LatticePT PertExtension.LatticePT.Mixed PertExtension.Orb PertExtension.Orb.SlotEvaluation PertExtension.Series PertExtension.Series.Tested Precision Pert.Orb
open Extra.FD Maxwell Extraction
open FormalOPE
open RG10.Position (Plan Loft)
open PowerSeries (C coeff)
open MeasureTheory MS MS.Koszul MS.Native MS.Menus MS.Book MS.Plane MS.Theater
open MS.Lifting MS.Local.Physical MS.Native.Paint MS.Native.Wilsonian
open scoped BigOperators Topology ContDiff PowerSeries
variable {W:Type}[Fintype W][LinearOrder W]{G:Gauge}{d m:ℕ}{n:Side}{B:Deck G}{L:Frames G}{H:Hol G}
set_option linter.unusedSectionVars false
lemma AspirSc (φ:ℝ→ℝ)(a:ℕ→ℝ)(c:ℝ)(h:Aspiration φ a): Aspiration (c • φ) (c • a):=by
  -- private LatticePT scale_price
  intro j;obtain ⟨A,hA,T⟩:=h j
  refine ⟨‖c‖*A,mul_nonneg (norm_nonneg _) hA,?_⟩; filter_upwards [T] with t ht
  have hp : (c • φ - peval (c • a) j) t=c*((φ-peval a j) t):=by dsimp [peval,Zone.eval,Pi.sub_apply];rw [mul_sub,Finset.mul_sum];congr 1; apply Finset.sum_congr rfl;intro;intro;ring
  rw [hp,norm_mul]; exact (mul_le_mul_of_nonneg_left ht (norm_nonneg _)).trans_eq (mul_assoc _ _ _).symm
variable (D: ChartRatio G) (hD : LocalRatio D) (R: Lobby.Registry L H)
local notation "V"=> Rake.Label B
local notation "rV"=> tray G
local notation "Φs"=> PowerSeries ℂ
local notation "X₀"=> (Config G n)

include hD in
lemma diag_sm (e:X₀→ℝ)(c:ℝ)(he:Even n.val)(he':PreTest e)(hp: PreTest (c • e)) : diagonalWith rV (restrictedO (c • e)) = c • diagonalWith D (restrictedO e):=by
  have h(k:ℝ): preExpectation (c • e) k=c*preExpectation e k:= by unfold preExpectation preNum; simp only [Pi.smul_apply,smul_eq_mul,mul_assoc, MeasureTheory.integral_const_mul, mul_div_assoc]
  exact (before_tree_formula he (traySpec G) hp).unique (show Aspiration (preExpectation (c • e)) _ from (funext h).symm ▸ AspirSc _ _ c (before_tree_formula he hD he'))

-- Primary unscaled extension off shell (p of potentially different pure slot types at each site)
-- v : h, profile point.weight in continuous.Man.L.
def start (d:ℕ)(p : Labels.Label G d)(a: (L.level d).Index): ℂ:= ∑ i:(L.level d).Index, (L.level d).coords p i * (↑(topBasis (R.use d) H (R.owns d) (R.bid d) i a):ℂ)
variable (h:W→ℕ)(x:W→Site n)
def age (d:ℕ)(p: Site n)(i:(L.level d).Index): X₀→ℝ:= fieldAt (R.use d) i p
def stops (d:ℕ)(i:(L.level d).Index):= ((L.level d).grades i).2
abbrev Sbox := (i:W)→ (L.level (h i)).Index

def FullT (p: (i:W)→Labels.Label G (h i)) : Φs:= ∑ u:Sbox (L:=L) h, ( PowerSeries.C (∏ i, start R (h i) (p i) (u i)) ) * Lobby.ΦbaseT D Finset.univ (fun i=>stops (L:=L) (h i)) (fun i=>age R (h i) (x i)) u
lemma linkHome (p:W→Rake.Label B) : FullT D R (fun i:W=> (p i).h) x (fun i:W=> popTag (p i))= Lobby.WilsonPoint D R n x p:=rfl

lemma distribute {J:W→Type}[∀ i,Fintype (J i)](f: (i:W)→ J i→ ℂ)(P: (i:W)→ J i→ Label G (h i)):
    FullT D R h x (fun i=>∑ j:J i,f i j • P i j)= ∑ k: (i:W)→ J i, C (∏ i,f i (k i)) * FullT D R h x (fun i=> P i (k i)):= by
   have hv (d:ℕ)(j:W)(a:(L.level d).Index)(Q:J j→ Label G d): start R d (∑ k:J j,f j k • Q k) a = ∑ k:J j,f j k * start R d (Q k) a:=by
     unfold start; rw [map_sum]; simp_rw [Finset.sum_apply,map_smul,Pi.smul_apply, Finset.sum_mul,Finset.mul_sum]; rw [Finset.sum_comm]; simp_rw [smul_eq_mul,mul_assoc]
   unfold FullT; simp_rw [hv,Fintype.prod_sum,map_sum,Finset.sum_mul,Finset.mul_sum]; rw [Finset.sum_comm]; refine sum_congr rfl fun j _=> sum_congr rfl fun k _=>?_ ; rw [Finset.prod_mul_distrib,map_mul,mul_assoc]
-- unscaled lexical reading
lemma start_basis(i:(L.level d).Index)(j:(L.level d).Index): start R d ((L.level d).basis i) j=(↑(topBasis (R.use d) H (R.owns d) (R.bid d) i j):ℂ):= by unfold start; rw [(L.level d).coords_basis]; simp only [Pi.single_apply, ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',mem_univ,if_true]
lemma frameKeys(p: Sbox (L:=L) h)(x:W→Site n)(hn:Admissible n):
    PreTest (∏ i:W,age R (h i) (x i) (p i)):= Fixed.preT _ hn (fun i:W=> Shop.field_ok (R.use _) (p i) (R.owns _) (R.bid _) (x i)) (fun i _=> Complex.continuous_re.comp ( (R.use (h i)).continuous_places _ _ )) -- args
-- ε of Mixed notation.Native coordinates. first table with powers of ε^d. Need hn for funded proof (`fixed preT`).
-- match generic basis given OWN weights
include hD
lemma bunker (p:Sbox (L:=L) h)(hp:∀ i,((L.level (h i)).grades (p i)).1=h i)(ε:ℝ)(he:Admissible n):
    let w : W→Word G:= fun i=> ⟨h i,L.level (h i),R.use _, H,R.owns _,R.bid _, p i,hp i⟩
    PowerSeries.C (∏ i:W, ((ε^4/ε^(h i):ℝ):ℂ))* FullT D R h x (fun i=> (L.level _).basis (p i))= ∑ u:Mixed.Task w, PowerSeries.mk (fun k=> (↑(diagonalWith rV (restrictedO (Mixed.product w Finset.univ u x ε)) (Mixed.number w u + k)):ℂ)):=by
  intro w; ext1 k; rw [PowerSeries.coeff_C_mul, FullT,map_sum,map_sum,Finset.mul_sum]; refine sum_congr ?_ fun j _=>?_ -- Finset typed mismatch Mixed.Task vs box?
  · rfl
  rw [PowerSeries.coeff_mk,PowerSeries.coeff_C_mul,Lobby.ΦbaseT,PowerSeries.coeff_mk]
  let Ξ(i:W):= ((w i).cost (j i) ε); let T:= ∏ i:W, age R (h i) (x i) (j i)
  have hp':Mixed.product w Finset.univ j x ε=(∏ i,Ξ i) • T:=by ext a; unfold Mixed.product; rw [Finset.prod_mul_distrib]; unfold T; simp only [Pi.smul_apply,Finset.prod_apply]; rfl
  rw [hp',diag_sm D hD T (∏ i,Ξ i) (even_iff_two_dvd.mpr he.2) (frameKeys R h _ _ he) (hp' ▸ Mixed.product_good w j x ε|>.1)] -- works
  -- casts
  change _ = Complex.ofReal ((∏ i,Ξ i) * diagonalWith D (restrictedO T) (Mixed.number w j+k)); rw [Complex.ofReal_mul]; simp_rw [ Complex.ofReal_prod ]; unfold Fixed.treeMom; rw [← mul_assoc,← Finset.prod_mul_distrib,show ∑ i∈(univ:Finset W), stops _ _= Mixed.number w j from rfl]; congr! 2; swap; congr 1; omega; unfold Ξ; rw [start_basis, Word.cost]; push_cast; rfl
end YM.FVAAlt2.Home.Profiles
