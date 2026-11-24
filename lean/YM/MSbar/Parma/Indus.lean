import YM.MSbar.Parma.Paces
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
open MvPolynomial
variable (f:Nesting G n) (F:ℝ → Wilson.Config G n→ℝ) (R:PathData G)(l:Clip)(v:G.ColorIndex){a η C b p' s E Z D σ w Φ A:ℝ}{r m p k N:ℕ}
variable (hG:G.Simple)(hf:Trend F f R l p)(hK: Keeps f p (sun G v)) (hr:r≤p)(hx:0<r)(hb:0≤b)(hη:6≤N)
noncomputable def teethT (f:Nesting G n)(r:ℕ) := PowerSeries.coeff r f
local notation "T₀"=>teethT f r
local notation "F₁"=>clue (teethT f r)
include hx
lemma pose : clue (teethT f r)= Lis.atlas f p r R l:=by unfold teethT Lis.atlas tariff; ext x; unfold clue joy; simp [PowerSeries.coeff_C_of_ne_zero hx.ne']
variable (hZ:Tin (Measuring.chart n G) b N (r+1) w (teethT f r) Z) (hw:0<w) (he:∀ i<r, Tokew (Measuring.chart n G) b N 3 0 (PowerSeries.coeff i (tariff n p l R f)) A)
local notation "d"=> (4*100^3/(n.val:ℝ)^3)
variable (h:Cane P D η a E k N) (hp:3≤k) (hg:2≤g.count.val)(hT:a/(g.count.val:ℝ) ≤ b)
local notation "ν"=> Cane.value a D η E N k
local notation "B"=>crownB G E η D k
local notation "μ"=> (2:ℝ)
local notation "Q"=> Rolling.rail (maple R' G) (teethT f r)
variable (ha:0≤ A)
include h hf hK hG hp he ha hb hw hη hr hZ hT hg -- fix
lemma price₁ (i:ℕ)(hv:i≤ r+1)(hh:i ∈ Set.Icc 1 3) (K':ℝ)(hC:0≤K')(hM:∀ j :Primary n G,Conde (target j) K' i (4-i) (fun l=>buoy (clue (teethT f r)) 0 (j::l)))(j:Y) : cog T a N Q i j ≤ L^4*(ν/L)* (2*(feed a η E D N k i/L^i)*((4/L)^(4-i))*(Z/w^(i+1))+(B/L)^i*K'):=by
    have htag := (CrossH.pressed i ℓ _ _ _ _ _ hw).mpr ⟨hZ.dec, hZ.fan i hv⟩
    let p:=4-i; have he':p≤k:=by obtain ⟨hv,hb⟩:=hh; omega
    have hp:p=4-i:=rfl
    have hc:= Lis.sparkle g P (clue _) h hT hg hw hw htag rfl hM (show ContDiffAt ℝ (↑(i+1:ℕ)) _ 0 from (helm _ _).contDiffAt) le_rfl hC (show 0<4-i by obtain ⟨hp,hk⟩:= hh; omega) (show 4-i ≤k from he') (show 4-i≤N from by omega) -- args check
    rw [← show clue Q=clue T₀ ∘ Lis.roll g P G from funext (fun x'=>levy g P x' T₀)] at hc; -- comp
    have ht:=(CrossH.pressed i T _ _ _ _ _ hw).mp hc|>.2 j
    rw [mul_div_cancel_right₀ _ (pow_pos hw _|>.ne')] at ht; exact ht
-- accounting formulas explicit. goal uniform if these preL≤ξ at all sites.
noncomputable def slopeY (n:Side)(k:ℕ) (D:ℝ):= D*((4*100^3)/(n.val:ℝ)^3 * (if k=1 then 64*100 else 1)) -- coarse handles k1 Tumbler. currently actual factor 400 vs? actually64*100*100^3≤4*100^3*64*100.
lemma ropes (i:ℕ)(hv:i≤r+1)(hh:i∈ Set.Icc 1 3)(x:X) : Conde (target x) (slopeY n i (Z/w^(i+1))+Lis.statue G r (i-1)*A) i (4-i) (fun k=>buoy (clue (teethT f r)) 0 (x::k)) :=by
    let t(i:ℕ):=Z/w^(i+1); have ht':0≤Z:=hZ.dec
    have ht(i:ℕ)(hi:i≤ r+1)(x:Primary n G) : Yarn i (fun k:List X=>|buoy (Lis.atlas f p r R l) 0 (x::k)| *swipe ℓ b N (x::k))≤t i:=by rw [← pose f R l hx, scored]; exact hZ.fan i hi x -- hx shadow
    have hh' : ∀ a'<r,∀ x':Primary n G,∀ l'≤3,Yarn l' (fun k:List X=>|buoy (Lis.atlas f p a' R l) 0 (x'::k)| *swipe ℓ b N (x'::k)) ≤ A:=by intro i hi x j hj; unfold Lis.atlas; rw [show joy _ _=clue _ from rfl,scored]; exact (token _).mp (he _ hi)|>.2 j hj x
    obtain ⟨h1,h2⟩:=hh
    interval_cases i
    · intro l₁ z he; have hp:=(Lis.billy f R l x hf hr hb hη v hK hG (Nat.ne_of_gt ‹0<r›) (ht 1 hv)) l₁ z he
      -- unfold target Defeq
      rw [pose f R l hx]; refine (show |_|≤ _ from hp).trans ?_
      apply le_trans _ (le_add_of_nonneg_right (a:=slopeY n 1 (Z/w^(1+1))) (mul_nonneg (Lis.statue_pos ..) ha)); unfold slopeY t tumbler; field_simp; norm_num; linarith
    · rw [pose f R l hx]; have hi:= Lis.annual f R l x hf hr hb hh' hη (ht 2 hv x); unfold slopeY; convert hi using 1 <;> norm_num [t, Midpoint.tumbler]<;> ring
    · rw [pose f R l hx]; have hi:= Lis.quad f R l x hf hr hb hh' hη (ht 3 hv x); unfold slopeY; convert hi using 1 <;> norm_num [t] <;> ring
end YM.MSbar.Parma
