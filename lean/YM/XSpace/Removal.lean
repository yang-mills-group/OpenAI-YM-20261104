import YM.XSpace.Melting
import YM.XSpace.Lodges

/-!
# Estimate for using the first-order infinite-lattice formula to read the orbit PT

Utilities compatible with `Regulated`, and all before shifting to renormalized coupling.
Future users will postcompose this estimate with shape normalizations and counterterm
cancellations. Includes stress if given label (doesn't identify exact stress).
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Comets
open Function Set Filter Lattice RG Wilson Source Source.Drops Labels Next.Rank.Normal Contraction Chart2 JetGauge Outline Outline.Given PowerSeries Feynman
open Sail (reach)
open scoped Topology BigOperators
variable {G:Gauge} {R:Period} {H:Hol G} {Z S:Type*}[AddCommGroup S][One S]{d:Z→ℕ} {n:ℕ}

-- specialized compression of layout query into budget constants. No quotient operations on labels during IR removal
namespace Input
variable (s:Finset Z) (L: ∀ i:Z,Survey G H (d i))(K: Z→Labels.Pol G)

def crop (x:Z→Four S):= ∏ i∈s,toy (L i) (x i) (K i)
def work : Music (Z:=Z) (G:=G):= ∏ i∈s,MvPolynomial.rename (Prod.mk i) (script (L i) (0:Cover) (K i))
def polynomials : PowerSeries (Shadow (G:=G) (Z:=Z)):= ∏ i∈s, PowerSeries.map (MvPolynomial.rename (Prod.mk i)).toRingHom (toy (L i) (0:Cover) (K i))
lemma election (g:Given G S) (x: Z→Four S) : constantCoeff (crop s L K x) = shroud g x (work s L K):=by
  rw [crop, work,map_prod,map_prod]; refine Finset.prod_congr rfl fun i _=>?_ ; rw [shroud_turn,bolt, Chart.pull0, Given.gone]; rfl
lemma steam (g:Given G S) (x:Z→Four S):
    constantCoeff (crop s L K x)=motor g x (constantCoeff (polynomials s L K)) ∧
    coeff 1 (crop s L K x)=motor g x (coeff 1 (polynomials s L K)):=by
  classical
  induction s using Finset.induction_on with
  | empty=> simp [crop,polynomials]
  | insert i s h ih=>
    unfold crop polynomials at *; rw [Finset.prod_insert h,Finset.prod_insert h]
    have he : ∀ p:PowerSeries (St ℤ G),∀ n:ℕ,motor g x (coeff n (PowerSeries.map (MvPolynomial.rename (Prod.mk i)).toRingHom p)) = (g.points (x i)).pull (coeff n p) :=by intro p n; rw [coeff_map]; exact motor_at ..
    set p:= toy (L i) (0:Cover) (K i)
    have hk : constantCoeff (toy (L i) (x i) (K i))= motor g x (constantCoeff (PowerSeries.map (MvPolynomial.rename (Prod.mk i)).toRingHom p)):= by rw [← coeff_zero_eq_constantCoeff_apply (PowerSeries.map _ _),he,coeff_zero_eq_constantCoeff_apply,show constantCoeff p=p0 (L i) 0 (K i) from rfl, Chart.pull0,Given.gone]; rfl
    have hx : coeff 1 (toy (L i) (x i) (K i))= motor g x (coeff 1 (PowerSeries.map (MvPolynomial.rename (Prod.mk i)).toRingHom p)):= by rw [he,show coeff 1 p= p1 (L i) (0: Cover) (K i) from rfl, Chart.pull1, Given.gone]; rfl
    simp only [map_mul,coeff_one_mul,map_add,hk,hx,← ih.1, ← ih.2,and_self]

lemma enter (R:Period)(x: Z→ R.Sites): E (wide (meet G R)) (price1 (R:=R) (crop s L K x))=
    E (dawn G R).grant (motor (dawn G R) x (coeff 1 (polynomials s L K)))-∑ p:PlaqAxes, interact p R x (work s L K):=by
  let g:=dawn G R; rw [price1,election s L K g,(steam s L K g x).2, cubic,map_sub]; congr 1
  rw [smul_mul_assoc, Finset.sum_mul,map_smul,map_sum,Fintype.sum_prod_type_right]; simp only [interact,smul_eq_mul,Finset.mul_sum]; rfl

def expo (x:Z→Cover):ℂ:= E (dusk G).grant (coeff 1 (crop s L K x))-∑ p:PlaqAxes, bulk p x (work s L K)

/-- Quantitative estimate before `α` engineering normalization on the marks. -/
theorem first (G:Gauge) (s: Finset Z) {H:Hol G} (L: ∀ i:Z,Survey G H (d i)) (k:∀ i,Label G (d i)): ∃ C:ℝ, 0≤C∧∀ R:Period,∀ T:R.Tree, ∀ o:Cover,Tall R o→∀ r:ℕ,512*(1+r)≤ R.side.val →∀ z:Z→Cover,(∀ i,reach (z i-o)≤r)→
    let P:=(∏ i∈s,Bare.column T (L i) (wrap R.side (z i)) (k i))
    ‖coeff 1 (Bare.normalized T G P)-expo s L (fun i=> ((L i).insertW (-1) (k i)).val) z‖ ≤ C*allowance R r:=by
  let K i:=((L i).insertW (-1) (k i)).val; obtain ⟨C,hC,H⟩:= (arc (coeff 1 (polynomials s L K))).1; choose C' h' hp using interaction_price (work s L K)
  refine ⟨C+∑ i,C' i,add_nonneg hC (Finset.sum_nonneg fun i _=>h' i),?_⟩; intro R T o ho r hr z hz P; let x:=wrap R.side ∘ z; let A:=allowance R r
  rw [show coeff 1 (Bare.normalized T G P)= E (wide (meet G R)) (price1 (R:=R) (crop s L K x)) from order1_always T (meet G R) L k x s]
  change ‖_ - expo s L K z‖ ≤ _; rw [enter,expo,(steam s L K (dusk G) _).2]; rw [show ∀ a b c d:ℂ, a-b-(c-d)=(a-c)-(b-d) by intros; abel, ← Finset.sum_sub_distrib,add_mul,Finset.sum_mul]; apply (norm_sub_le ..).trans; apply add_le_add (le_trans (H R o ho r z hz) (mul_le_mul_of_nonneg_left (permit ..) hC)); exact (norm_sum_le ..).trans (Finset.sum_le_sum fun i _=>hp i R o ho r hr z hz)
end Input

namespace Probes
variable (A:Initialize G) (q: Fin n→ℕ) (u: ∀ i,On.Grade G (q i))
def degree (q:Fin n→ℕ) := ∑ i,q i
def sections (i:Fin n) := A.surveys (q i)
def resetV (i:Fin n): Labels.Label G (q i):= (sections A q i).insertW (-1) (Price.preparedL (u i))
def prediction (g:ℝ) (z:Fin n→Cover) := (g:ℂ)⁻¹ ^ degree q * Input.expo Finset.univ (sections A q) (fun i=>(resetV A q u i).val) z
lemma predicts (p:Mesh) (x:Fin n→ p.Sites):
    coeff 1 (A.atTuple p q x u)= (p.spacing:ℂ)⁻¹ ^ degree q * coeff 1 (Bare.normalized (A.tree p.p) G (∏ i,Bare.column (A.tree p.p) (sections A q i) (x i) (Price.preparedL (u i)))):=by
  rw [A.atTuple_eq]; let F (i:Fin n):= Bare.column (A.tree p.p) (sections A q i) (x i) (Price.preparedL (u i)); let z:ℂ:=(p.spacing:ℂ)⁻¹
  have hs (s:Finset (Fin n)): (∏ i∈s,A.atSite p _ (x i) (u i))=z^(∑ i∈s,q i) • ∏ i∈s,F i :=by
    induction s using Finset.induction_on with
    | empty=> simp
    | insert i s hi ih=> rw [Finset.prod_insert hi,Finset.prod_insert hi,Finset.sum_insert hi,pow_add, mul_smul,ih, show A.atSite p _ (x i) (u i)=z^(q i) • F i from ?_,smul_mul_assoc,mul_smul_comm]
                         rw [Initialize.atSite,LinearMap.smul_apply,inv_pow]; rfl
  rw [hs,map_smul,map_smul]; rfl
open Expense
variable {ι: Type*}{p:ι→Mesh}{L:Filter ι}
-- cluster purchase. accommodates random joint points, far scaler or bounded shells.
def Overhead (L:Filter ι)(p:ι→Mesh)(o:ι→Cover)(z:ι→ Z→Cover): Prop:=∃ C:ℝ,∃ d:ℕ,1≤C∧∀ᶠ i in L, Tall (p i).p (o i)∧∀ j, (↑(reach (z i j-o i)):ℝ) ≤ C*(a p i)^(-(d:ℤ))

private lemma leverage (p:Mesh) (r k:ℕ)(B:ℝ) (h:1≤ B)(hx:p.spacing≤1)
    (ht: B*(p.spacing^k)⁻¹ ≤ (r:ℝ)) (hs: (r:ℝ)< B*(p.spacing^k)⁻¹+1) (hm:(8*B)^5 ≤ p.spacing^(k*6)*Expense.nodes p):
    512*(1+r) ≤ p.p.side.val ∧ allowance p.p r ≤ 2*p.spacing^k := by
  let a:=p.spacing^k; have ha : 0<a:= pow_pos p.positive _; have h1 : a≤1:= pow_le_one₀ p.positive.le hx; let n:ℝ:=p.p.side.val; have hn : 0<n:=Bloch.side_pos _
  have hg : (8*B)^5 ≤ a^6*n:=by rw [pow_mul] at hm; exact hm
  have he : (1+(r:ℝ))*a≤ 3*B :=by
    have ht : (r:ℝ) ≤ B/a+1:=hs.le.trans_eq (by rw [div_eq_mul_inv])
    have hh : (r- (1:ℝ))*a ≤ B:=(le_div_iff₀ ha).1 (le_trans (by linarith) le_rfl);
    linarith
  have h₀: p.spacing^k≥a:=le_rfl
  have hh : (↑r:ℝ)≤ 3*B/a:=(le_div_iff₀ ha).2 (by linarith); have hA : (1+(r:ℝ))^5 ≤ a*n:=by
    have he := pow_le_pow_left₀ (by positivity : 0≤(1+(r:ℝ))*a) he 5; rw [mul_pow] at he; have ht : (3*B)^5≤(8*B)^5:= by gcongr; linarith
    apply le_of_mul_le_mul_right _ (pow_pos ha 5); exact (he.trans (ht.trans hg)).trans_eq (by ring)
  constructor
  ·
    suffices H:512*(1+(r:ℝ))≤(p.p.side.val:ℝ) by exact_mod_cast H
    change _≤ n; apply le_of_mul_le_mul_right _ ha
    have hb : a^6 ≤ a:= by simpa using pow_le_pow_of_le_one ha.le h1 (show 1≤6 by decide)
    rw [mul_assoc]; apply (mul_le_mul_of_nonneg_left he (by norm_num : (0:ℝ)≤512)).trans
    -- even generous seam constants are harmless
    have he : B≤B^5:= le_self_pow₀ h (by decide)
    calc _ ≤ (8*B)^5:=by rw [mul_pow]; linarith
         _ ≤ a^6*n:= hg
         _ ≤ _:= by rw [mul_comm n]; gcongr
  unfold allowance; rw [two_mul]; apply add_le_add
  · change Outline.saving r ≤ a; unfold Outline.saving; apply (inv_le_iff_one_le_mul₀ (by positivity : (0:ℝ)<1+r)).2; have hi : B/a ≤ (r:ℝ):=by rw [div_eq_mul_inv]; exact ht
    have hu:= (div_le_iff₀ ha).1 hi; linarith
  change _/n ≤ a; exact (div_le_iff₀ hn).2 hA

lemma lets (h:Expense.Stretched L p)(z:ι→Fin n→ Cover) (o:ι→Cover)(he:Overhead L p o z) (j:ℕ):∃ k:ℕ,∃ r:ι→ℕ,j≤k ∧ ∀ᶠ i in L, Tall (p i).p (o i) ∧ (∀ s,reach (z i s-o i)≤r i) ∧ 512*(1+r i)≤ (p i).p.side.val ∧ allowance (p i).p (r i)≤ 2*(p i).spacing^k:=by
  obtain ⟨B,d,hB,H⟩:=he; set k:=j+d; let r i:= ⌈B*((a p i)^k)⁻¹⌉₊; refine ⟨k,r,by omega,?_⟩; filter_upwards [H,h.smaller,(h.pay (k*6)).eventually_ge_atTop ((8*B)^5)] with i hi hv hh
  have ht:B*((a p i)^k)⁻¹ ≤ r i:=Nat.le_ceil _; have hu:=actual p i; refine ⟨hi.1,fun s=>?_ , leverage (p i) (r i) k B hB hv ht (Nat.ceil_lt_add_one (by positivity : (0:ℝ) ≤ B*((a p i)^k)⁻¹)) hh⟩
  have hs : (↑(reach (z i s-o i)):ℝ) ≤ (r i:ℝ):=by refine (hi.2 s).trans (le_trans ?_ ht); rw [zpow_neg, zpow_natCast]; apply mul_le_mul_of_nonneg_left _ (by linarith); exact inv_le_inv₀ (pow_pos hu d) (pow_pos hu k)|>.2 (pow_le_pow_of_le_one hu.le hv (by unfold k; omega))
  exact_mod_cast hs

lemma seams (x:Lattice.Cover) (R:Period) (hℓ : (R.side.val:ℤ)≤ 16*x 0) (hu : 16*x 0 ≤5*R.side.val): Tall R x:=by
  set n:=R.side; let t:=x+x; let y:= Lattice.wrap n t
  have hv : (n.val:ℤ) ∣ (lift y 0)-t 0 := (ZMod.intCast_eq_intCast_iff_dvd_sub ..).mp (show ((↑(lift y 0):ZMod n.val)) = ↑(t 0) from congr_fun (wrap_lift _) 0).symm
  have hp:= component_le y 0; have hpos:=n.pos; have hh:t 0=x 0+x 0:=rfl; change (n.val:ℤ)≤16*x 0 at hℓ; change 16*x 0 ≤ 5*n.val at hu
  change n.val≤16*pdist y
  by_cases H: lift y 0=t 0
  · omega
  have hs:n.val ≤ (lift y 0-t 0).natAbs:= by
    apply Nat.le_of_dvd (by omega)
    exact_mod_cast (Int.natAbs_dvd_natAbs.mpr hv)
  omega
theorem blank (z:ι→Fin n→Cover) (S:Stretched L p) (o:ι→ Cover)(h:Overhead L p o z) : Cross.Blank L p (fun i=> coeff 1 (A.atTuple (p i) q (wrap (p i).p.side ∘ z i) u)- prediction A q u (a p i) (z i)):=by
  let d:= degree q; intro w; obtain ⟨C,hC,H⟩:= Input.first G Finset.univ (sections A q) (fun i=> Price.preparedL (u i)); obtain ⟨k,r,hR,K⟩:=lets S z o h (d+w)
  apply Asymptotics.IsBigO.of_bound (2*C); filter_upwards [K,S.smaller] with i hi hk; set g:=p i
  let x:=a p i; have hx: 0<x:=actual p i; have hh: x≤1:=hk
  rw [predicts,prediction,show a p i= g.spacing from rfl,← mul_sub, norm_mul]
  rw [norm_pow,norm_inv,Complex.norm_real]; simp only [Real.norm_of_nonneg g.positive.le]; rw [Real.norm_of_nonneg (pow_nonneg g.positive.le _)]
  apply le_trans (mul_le_mul_of_nonneg_left (H _ (A.tree (p i).p) _ hi.1 _ hi.2.2.1 _ hi.2.1) (by positivity : (0:ℝ)≤x⁻¹^d)); apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hi.2.2.2 hC) (show 0≤ x⁻¹^d by positivity)); change x⁻¹^d * (C*(2*x^k))≤ _; calc
    _ ≤ x⁻¹^d * (C*(2*x^(d+w))) := by gcongr _ * (_ * (_ * ?_)); apply pow_le_pow_of_le_one hx.le hk hR
    _ = 2*C*x^w:=by rw [pow_add,inv_pow]; field_simp
end Probes
end YM.XSpace.Comets
