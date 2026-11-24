import YM.MSbar.Parma.Vetta
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Parma
open Function Filter Whisk Lis Measuring Cacao CrossH Push Uniform Lattice RG Pressure Matrix
open Precision Gauge Midpoint Rolling Tramp Exterior Tree Wilson Laurent Bloch Wave
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge} {c n:Side}(g:Ratio c n)(P:Cross g.count (TypeFace 1) (TypeFace 1))
local notation "X"=>Primary n G
local notation "Y"=>Primary c G
local notation "ℓ"=>Measuring.chart n G
local notation "T"=>Measuring.chart c G
local notation "L"=>(g.count.val:ℝ)
local notation "R'"=>installed g P
open MvPolynomial Cane
variable (f:Nesting G n)(F:ℝ → Wilson.Config G n→ℝ)(R:PathData G)(l:Clip)(v:G.ColorIndex){a η B C b H Z D w A:ℝ}{r m p k N:ℕ}
variable (hG:G.Simple)(hf:Trend F f R l p)(hK: Keeps f p (sun G v)) (hr:r≤p)(hx:0<r)(hb:0≤b)(hη:6≤N)
local notation "T₀"=>teethT f r
local notation "F₁"=>clue (teethT f r)
variable (hZ:Tin (Measuring.chart n G) b N (r+1) w (teethT f r) Z) (hw:1≤ w) (he:∀ i<r, Tokew (Measuring.chart n G) b N 3 0 (PowerSeries.coeff i (tariff n p l R f)) A)
local notation "d"=> (4*100^3/(n.val:ℝ)^3)
variable (h:Cane P D η a H k N) (hp:3≤k) (hg:2≤g.count.val)(hT:a/(g.count.val:ℝ) ≤ b) (ha:0≤ A)
local notation "ν"=>Cane.value a D η H N k
local notation "E"=> crownB G H η D k
local notation "M"=>Rolling.rail (maple R' G) T₀
-- costs pre: function of η strip etc.C includes.D.Stack Hyper origin.Genuine L gain. output sum.
local notation "C'"=> fixP G r a D η H N k
local notation "s'"=> fixedG G g.count r a D η H N k
include h hw hZ hT ha
lemma priceH (m:ℕ)(hm:m≤r+1)(he:4 ≤ m)(x:Y): cog T a N M m x ≤ (C'/L*Z+s'*(w^4*A))/w^(m+1):=by
    have hs(i:ℕ):=valueG (G:=G) g P h i g.count; have hx:=(hs r).1; have hb':= (hs r).2.2.2.1; have ht':=(hs r).2.2.2.2 r; have hv:=hZ.dec; have hL: 1≤ L:=by exact_mod_cast g.count.property
    apply le_trans (high g P h hT hw hZ m hm x) (div_le_div_of_nonneg_right _ (by positivity)); have ht : ν^(m+1) ≤ C':=by
       have he:0 ≤∑ i∈Finset.Icc 1 3, lowP G i a D η H N k:= Finset.sum_nonneg fun i hi=>by unfold lowP; have ht:=(hs i).2.1; have hv:=(hs i).2.2.1; positivity
       exact (Finset.single_le_sum (s:=Finset.Icc 4 (r+1)) (f:=fun i=> highP i a D η H N k) (fun i hi=> pow_nonneg hx _) (Finset.mem_Icc.mpr ⟨‹_›,hm⟩)).trans (le_add_of_nonneg_left he)
    apply le_trans _ (le_add_of_nonneg_right (by positivity : 0≤ s'*(w^4*A))); calc
       _ ≤ Z*L^4*(C'/L^5):=by rw [div_pow]; exact mul_le_mul_of_nonneg_left (div_le_div₀ hb' ht (show 0<L^5 by positivity) (pow_le_pow_right₀ hL (by omega))) (by positivity); -- denominator orientation check
       _ = _:=by field_simp
include hf hK hG hr hx he hb hη hp hg
lemma hard : Tin T a N (r+1) w M (C'/L*Z+s'*(w^4*A)):=by
    have hs(i:ℕ):=valueG (G:=G) g P h i g.count; have hx':=(hs r).1; have hb':= (hs r).2.2.2.1; have ht':=(hs r).2.2.2.2 r; have h₀:=hZ.dec; have hv:0 ≤ C'/L*Z+s'*(w^4*A):=by positivity
    refine ⟨hv,fun i hi j=>?_⟩
    by_cases hh:i=0
    · subst i; apply le_trans _ (div_nonneg hv (by positivity : 0 ≤ w^(0+1))); rw [← scored M j,twillz]; rw [show buoy (clue M) 0 [j] =0 from ?_,abs_zero,zero_mul]; let f':= joy (tariff n p l R f) r
      rw [show clue M=clue T₀ ∘ (roll g P G) from funext (fun x=>levy g P x T₀), pose f R l (p:=p) hx]
      let m:= Lis.roll g P G; change fderiv ℝ (f' ∘ m) 0 _=0; have hp:ContDiffAt ℝ 2 f' 0:= (Cacao.vent ..).contDiffAt.of_le le_top; have hh: fderiv ℝ f' 0=0:=by apply zero_hit hp hG (fun i=>Filter.Eventually.of_forall fun x=>?_); exact inh R l f p hf r hr i _
      rw [fderiv_comp _ _ m.differentiableAt, m.map_zero,hh]; rfl; rw [m.map_zero]; exact hp.differentiableAt (by simp)
    rcases lt_or_ge i 4 with ht|ht; exact currency g P f F R l v hG hf hK hr hx hb hη hZ hw he h hp hg hT ha i hi ⟨by omega,by omega⟩ _
    exact priceH g P f hZ hw h hT ha i hi ht _
end YM.MSbar.Parma
