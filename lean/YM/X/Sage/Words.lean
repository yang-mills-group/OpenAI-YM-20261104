import YM.X.Sage.Spin
/-!
# rational prices of tri stencils. Ω calibration. tape:X-image from Stomp. Use Herm(Q−χ). color.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Sage
open Lattice Wilson Next.Rank Normal LiftMark PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Shelf Tot
open Filter Function Reed Ocean Hinge Haze Fielding Print Tri Plate Gravity Chir
open Stems hiding X
open MvPolynomial Hue Set
open scoped Topology BigOperators Classical
variable {G:Gauge} {m d k:ℕ} {V:Type*} {q:ℕ+} {r R:ℝ}
local notation "Kₚ"=> Poly PlaqAxes G
local notation "H"=> Reed.Horizontal G
local notation "U"=> G.ColorIndex
local notation "P"=> PlaqAxes
local notation "T"=>Tet
local notation "Ω"=> Foam G
variable (p t v:Tet) (x y z:G.ColorIndex)
def centerF (q:ℕ+) (d:ℕ):Curly G→ₗ[ℂ] Foam G:= priceL q (-(d:ℤ))
lemma center_mul (p w:Curly G) : centerF q (m+d) (p*w)=centerF q m p*centerF q d w:= by
    ext1 i; let a:=epsilon q i; change (↑(a^(-((↑(m+d)):ℤ))) :ℂ) • (p*w)= ((↑(a^(-(↑m):ℤ)):ℂ) • p)*((↑(a^(-(↑d):ℤ)):ℂ) • w); -- power parentheses
    have hh:a≠0:= (epsilon_pos ..).ne'; rw [smul_mul_assoc,mul_smul_comm,smul_smul,Nat.cast_add,neg_add, zpow_add₀ hh,Complex.ofReal_mul]
def ξ (q:ℕ+)(r:ℝ)(p:T)(x:U):Foam G:= credit q (Chir.spin r p x)
def topA (q:ℕ+)(i:Axis)(x:U):Foam G:= credit q (columnA i x)
lemma reciter (r:ℝ): dialF (Emitter r p x)= glyph (com (Chir.slope r p x)):= by
    unfold Emitter dialF Chir.slope; simp_rw [map_sum,map_smul,exchange_x]; unfold Stems.com; rw [map_sum,map_sum]; refine Finset.sum_congr rfl fun i hi=> ?_; rw [map_smul]; change _ • glyph _= ((glyph (V:=Hair G)).restrictScalars ℝ) (form _ _ _ _ • _); rw [map_smul]; exact (RCLike.real_smul_eq_coe_smul («K»:=ℂ) ..).symm -- quotient κ notation
lemma center_x (r:ℝ) : centerF q 2 (dialF (Emitter r p x))= ξ q r p x:= by ext1 i; unfold ξ; rw [labelP,reciter];rfl
lemma center_A (i:Axis) : centerF q 1 (X ((0,i),x))= topA q i x:= by ext1 k; unfold topA; rw [labelP]; unfold docB columnA; rw [com_text,blade,Finsupp.linearCombination_single,one_smul]; rfl
local notation "P₀"=> centerF q 2
def bcomp (q:ℕ+)(r:ℝ)(p:T)(x:U):Foam G:= centerF q 2 (call dialF glove (Emitter r p x))
def foame (q:ℕ+)(w:P)(x:U): Foam G:= ∑ a:U,∑ b:U, (ff x a b:ℂ) • (topA q w.val.1 a * topA q w.val.2 b)
lemma foame_eq (w:P) : centerF q 2 (glove (w,x))=foame q w x:= by unfold glove foame; simp_rw [map_sum,map_smul,center_mul (m:=1) (d:=1), center_A] -- †
lemma compb (r:ℝ): bcomp q r p x= ∑ v:P,(dataF r p v:ℂ) • foame q v x:= by unfold bcomp Emitter; simp_rw [map_sum, map_smul, call_X,foame_eq]
-- Prototype foam leading
local notation "Vₜ"=> call dialF glove -- avoid collision V!! rename
abbrev βm (q:ℕ+)(p:T):= ξ (G:=G) q 1 p
abbrev μm (q:ℕ+)(p:T):= ξ (G:=G) q (-1) p
def headP (q:ℕ+)(d:ℕ)(p: poly (CoverC G)):= centerF q d (dialF p)
def coronaP (q:ℕ+)(d:ℕ)(p:poly (CoverC G)):= centerF q d (call dialF glove p)
abbrev βDeck (q:ℕ+)(G:Gauge):= headP q 6 (ward G)
abbrev μDeck (q:ℕ+)(G:Gauge):= headP q 4 (tune G)
abbrev βLift (q:ℕ+)(G:Gauge):= coronaP q 6 (ward G)
abbrev μLift (q:ℕ+)(G:Gauge):= coronaP q 4 (tune G)
lemma ward_deck : βDeck q G= cubicP (G:=G) (βm q 0) (βm q 1) (βm q 2) := by
    unfold βDeck headP ward cubicP; simp_rw [map_sum,map_smul,map_mul,center_mul (m:=2) (d:=4),center_mul (m:=2) (d:=2), center_x]
lemma tune_deck : μDeck q G= ∑ p:T,∑ x:U,μm q p x*μm q p x:= by unfold μDeck headP tune; simp_rw [map_sum,map_mul,center_mul (m:=2) (d:=2),center_x]
-- crowns. for β rotation of chosen slot first. keep sums unexpanded except by formula.
lemma expand_turn (x y z:Kₚ): centerF q 6 (call dialF glove (x*(y*z)))=centerF q 2 (Vₜ x)*(centerF q 2 (dialF y)*centerF q 2 (dialF z)) + centerF q 2 (dialF x)*(centerF q 2 (Vₜ y)*centerF q 2 (dialF z) + centerF q 2 (dialF y)*centerF q 2 (Vₜ z)) := by simp_rw [call_mul,map_mul,map_add, center_mul (m:=2) (d:=4), center_mul (m:=2) (d:=2),map_add,center_mul (m:=2) (d:=2)] -- V open
lemma βcrown : βLift q G= ∑ p:T, cubicP (bcomp q 1 p) (βm q (loop p)) (βm q (ℓ p)):= by
    let A(i:T):=βm (G:=G) q i; let B(i:T):=bcomp (G:=G) q 1 i; unfold βLift coronaP ward; have h0:loop 0=1:=rfl; have h1:loop 1=2:=rfl; have h2:loop 2=0:=rfl;
    change _=∑ p:T,cubicP (B p) (A (loop p)) (A (ℓ p)); rw [sum3]; simp only [h0,h1,h2,ℓ]; rw [← crest (A 0), crest (B 2)]; unfold cubicP; simp_rw [map_sum,map_smul,expand_turn, center_x,← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun a _=> Finset.sum_congr rfl fun b _=> Finset.sum_congr rfl fun c _=>?_ ; simp only [← smul_add]; apply congr_arg (_ • ·); unfold A B bcomp βm; ring -- rotation?
lemma μcrown : μLift q G= ∑ p:T,∑ x:U,(2:ℂ) • (μm q p x*bcomp q (-1) p x):= by
     unfold μLift coronaP tune bcomp; simp_rw [map_sum,call_mul,map_add,center_mul (m:=2) (d:=2),center_x]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>?_ ; unfold μm; rw [two_smul,mul_comm]
end YM.PositionX.Sage
