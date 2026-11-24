import YM.X.Sage.Rear
/-!
# Roots.Arc slots held along atom sequences. Tint and transport.Trape.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Sage
open Lattice Wilson Next.Rank Normal LiftMark PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Shelf Tot
open Filter Function Reed Ocean Hinge Haze Fielding Print Tri Plate Gravity Chir
open Stems hiding X
open MvPolynomial Set
open scoped Topology BigOperators Classical
variable {G:Gauge} {m d k:ℕ} {V:Type*} {q:ℕ+} {r t R:ℝ}
local notation "L"=> (atTop:Filter ℕ)
local notation "U"=> G.ColorIndex
local notation "K"=> Reed.Horizontal G
local notation "T"=>Tet
local notation "H"=> Hair G
local notation "σ"=> H →₀ ℂ
local notation "o"=> side q k
local notation "ε"=> epsilon q k
local notation "Q"=> qu q G k
variable (x y z:Cover) -- k shadow? remove binder k notation bug.
abbrev psiF (q:ℕ+)(k:ℕ)(x:Cover)(r:ℝ)(p:Tet)(a:G.ColorIndex):= Vane q (Chir.spin r p a) k x
def psiA (q:ℕ+)(k:ℕ)(x:Cover)(i:Axis)(a:G.ColorIndex):= Vane q (columnA i a) k x
variable (s:ℝ) (p v:Tet) (i:Axis)(a b:G.ColorIndex)
lemma ψ_meetPP (t:ℝ): treats Q (psiF q k x r p a) (psiF q k y t v b) = if a=b then ↑(Wpp ε r p t v o (wrap o x) (wrap o y)) else 0:=
    (stamps (n:=o) (e:=ε) x y (Chir.spin r p a) (upMark (Chir.spin t v b))) |>.trans (entrym_ce _ _ _ _ _ _ _ _ (epsilon_pos q k)) -- pass underscores
lemma ψ_meetPV : treats Q (psiF q k x r p a) (psiA q k y i b)= if a=b then ↑(Wpv ε r p i o (wrap o x) (wrap o y)) else 0:=
    stamps (n:=o) (e:=ε) x y (Chir.spin r p a) (columnA i b) |>.trans (entryp_ce _ _ _ _ _ _ _ (epsilon_pos q k))
lemma ψ_A : psiA q k x i a= Complex.ofReal (ε⁻¹) • Finsupp.single ((x,i),a) 1:= by
   unfold psiA Vane tack columnA; rw [leads_single,show pointB x ((0,i),a) = ((x,i),a) from by simp [pointB]]; unfold Stems.com; rw [map_smul, RCLike.real_smul_eq_coe_smul («K»:=ℂ)]; change (↑((ε^_)⁻¹):ℂ) • com _= _; simp [com_six]
lemma ψ_X : Finsupp.single ((x,i),a) (1:ℂ)= Complex.ofReal (ε) • psiA q k x i a := by rw [ψ_A,smul_smul]; rw [← Complex.ofReal_mul,mul_inv_cancel₀ (epsilon_pos q k|>.ne'),Complex.ofReal_one, one_smul]
lemma ψ_paint (x:H) (h:x.2≠a): treats Q (Finsupp.single x 1) (psiF q k z r p a)=0:= by
    rcases x with ⟨⟨x,i⟩,j⟩; rw [treats_comm,ψ_X,treats,map_smul, ← treats]; rw [ψ_meetPV,if_neg (Ne.symm h), smul_zero]
lemma pass_f : dress x (ξ q r p a k)=glyph (psiF q k x r p a):= gen ..
lemma pass_A : dress x (topA q i a k)=glyph (psiA q k x i a):= gen ..
local notation "δ"=> Braid.edge Q
lemma rise_spin (s:Tops G)(R:Curly G): δ (Vane q s k z) (glyph (psiF q k x r p a)*R) = entryK o ε x (Chir.spin r p a) z s • R+glyph (psiF q k x r p a)*δ (Vane q s k z) R:= by rw [Derivation.leibniz,link,treats_comm, show treats Q (psiF q k x r p a) (Vane q s k z)=_ from stamps (n:=o) (e:=ε) x z (Chir.spin r p a) s]; simp only [smul_eq_mul]; rw [mul_comm R (C _), C_mul'];ring
variable {X Y Z:Fielding.Walk}
local notation "Fℕ"=> fades ℂ
lemma same_wire(h:Clear q R X Y)(hr:0≤R)(hq:1<q.val): Lined (G:=G) q (terminals G (-1)) (terminals G (-1)) X Y:= by
     rintro _ ⟨p,x,rfl⟩ _ ⟨v,y,rfl⟩; obtain ⟨a,b,ha,hb,h⟩:=h; unfold meets; change (fun k=>treats _ (psiF q k (X k) (-1) p x) (psiF q k (Y k) (-1) v y))∈ Fℕ; simp_rw [ψ_meetPP]; by_cases ht:x=y
     · simp only [if_pos ht]; have he:= turbine_same hq (sub_ne_zero.mp (norm_pos_iff.mp (lt_of_le_of_lt hr h))) ha hb p v; exact Complex.continuous_ofReal.continuousAt.tendsto.comp he
     simp only [if_neg ht]; exact Submodule.zero_mem _
end YM.PositionX.Sage
