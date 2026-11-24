import YM.X.Chili.Jam
import YM.X.Grow.Tele
/-!
# Finite combinations of graded probe monomials. for global construction: keep horizontal & not isolated samplings. supports axial transformations later.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Clove
open Lattice Wilson Next.Rank CellsInt Beamer Interval PertExtension LatticePT Normal Filter Set Function Metric MeasureTheory Asymptotics
open Reed Stems Fielding Print Braid Grow Haze MvPolynomial Finset LiftMark Tensor Ocean
open scoped Topology ContDiff BigOperators Classical
variable {q : ℕ+} (hq:1<q.val) {k m n d w:ℕ} {G:Gauge} {R T':ℝ}
local notation "Fℕ"=>(atTop:Filter ℕ)
-- translation

def dress (x:Cover): Curly G→ₐ[ℂ] Curly G:= rename (pointB x)
lemma dress_glyph (x:Cover)(p:Fan G): dress x (glyph (Stems.com p))= glyph (Stems.com (leadsL x p)):= by
   rw [com_text,com_text,dress]; induction p using Finsupp.induction_linear with
   | zero=> simp [blade]
   | add a b h g=> unfold blade at *; simp only [map_add,h,g] -- map b map ℝ abbreviation blade
   | single i c=> rw [leads_single]; unfold blade; rw [Finsupp.linearCombination_single,Finsupp.linearCombination_single]; change (((rename (pointB x)).toLinearMap).restrictScalars ℝ) (c • MvPolynomial.X i) =c • MvPolynomial.X (pointB x i); rw [map_smul]; exact congr_arg _ (rename_X ..) -- instead smul coe
lemma dress_eval (x:Cover)(p:Curly G)(f:Brush G) : snap f (dress x p)=snap (lowerP x f) p:= by
   apply DFunLike.congr_fun (f:=(snap f).comp (dress x)); ext1 i; rw [AlgHom.comp_apply,dress,rename_X, snap,snap,aeval_X,aeval_X];rfl
lemma dress_addT (x y:Cover)(p:Curly G): dress x (dress y p)= dress (x+y) p:= by
   apply DFunLike.congr_fun (f:=(dress x).comp (dress y)); ext1 i; simp only [AlgHom.comp_apply,dress,rename_X, pointB,add_assoc]
lemma dress_zero (p:Curly G) : dress 0 p=p:= by
   unfold dress; rw [show pointB (G:=G) 0 = id from funext fun i=>by simp [pointB], MvPolynomial.rename_id_apply] -- id name

def floatP (b:Bool): Curly G→ₐ[ℂ] Deck G where
    toFun p i z:= dress (pace b z) p; map_zero':= by ext1 i; ext1 z; exact map_zero _
    map_add' a c:=by ext1 i; ext1 z; exact map_add _ _ _
    map_one':= by ext1 i; ext1 z; exact map_one _
    map_mul' a c:=by ext1 i; ext1 z; exact map_mul _ _ _
    commutes' r:= by ext1 i;ext1 z; exact (dress _).commutes r
lemma float_glyph (b:Bool)(p:Fan G): floatP b (glyph (Stems.com p))=fresh b p:= funext (fun i=>funext fun z=> dress_glyph _ _)
lemma float_false (p: Curly G): floatP false p=fun _ _=> p:= by funext i z; exact dress_zero _
structure Bone (G:Gauge) (T:Submodule ℝ (Fan G)) where
    k:ℕ
    x:Fan G
    order : x∈Reed.grads G k
    sector: x∈T
variable {T:Submodule ℝ (Fan G)}
def tipB (a:Bone G T):= a.k+1
def docB (a:Bone G T):= glyph (com a.x)
def feelB (p:List (Bone G T)) : ℕ:= (p.map tipB).sum
def playB (p:List (Bone G T)):= (p.map docB).prod
def verse (T:Submodule ℝ (Fan G))(k:ℕ): Submodule ℂ (Curly G):= Submodule.span ℂ {p|∃ z:List (Bone G T),k≤feelB z∧ p=playB z}
lemma play_verse {p:List (Bone G T)}(h:k≤feelB p): playB p∈ verse T k:= Submodule.subset_span ⟨p,h,rfl⟩
lemma weaken_v (h:k≤n): verse T n ≤ verse T k:= by apply Submodule.span_le.mpr; rintro _ ⟨l,ht,rfl⟩; exact play_verse (h.trans ht)
lemma tier_v {S:Submodule ℝ (Fan G)}(h:T≤S): verse T n ≤ verse S n:= by
   apply Submodule.span_le.mpr; rintro _ ⟨z,ht,rfl⟩; let t(p:Bone G T): Bone G S:= ⟨p.k,p.x,p.order,h p.sector⟩; have he: feelB (z.map t)= feelB z:= by rw [feelB,feelB,List.map_map];rfl
   rw [show playB z=playB (z.map t) from by rw [playB,playB,List.map_map];rfl]; exact play_verse ((ht.trans_eq he.symm))
lemma verse_mul (T:Submodule ℝ (Fan G)){p s:Curly G}(h:p∈verse T n)(hx:s∈verse T k):p*s∈verse T (n+k):= by
   induction h using Submodule.span_induction with
   | mem i h=>
       obtain ⟨l,h,rfl⟩:=h; induction hx using Submodule.span_induction with
       | mem p hp=> obtain ⟨d,g,rfl⟩:=hp; rw [show playB l*playB d=playB (l++d) from by simp [playB]]; exact play_verse ((Nat.add_le_add h g).trans_eq (by simp [feelB])) -- symm
       | zero=>simp
       | add x y _ _ a b=> rw [mul_add]; exact Submodule.add_mem _ a b
       | smul a i _ h=> rw [mul_smul_comm];exact Submodule.smul_mem _ _ h
   | zero=>simp
   | add x y _ _ a b=>rw [add_mul];exact Submodule.add_mem _ a b
   | smul x y _ a=> rw [smul_mul_assoc];exact Submodule.smul_mem _ _ a
lemma verse_one : (1:Curly G)∈ verse T 0:= play_verse (p:=[]) le_rfl
lemma verse_glyph {f:Fan G}(hx:f∈Reed.grads G k)(hp:f∈T):glyph (com f)∈verse T (k+1):= by rw [← mul_one (glyph _)]; exact play_verse (p:=[⟨k,f,hx,hp⟩]) le_rfl -- nat trailing?
set_option maxHeartbeats 600000 in
lemma verse_C (c:ℂ): MvPolynomial.C (σ:=Hair G) c∈verse T 0:= by rw [← mul_one (MvPolynomial.C c),C_mul']; exact Submodule.smul_mem _ _ verse_one
lemma verse_top : verse (G:=G) ⊤ 0=⊤:= by
    rw [eq_top_iff]; intro p _; induction p using MvPolynomial.induction_on with
    | C x=> apply verse_C
    | add a b h g=> exact Submodule.add_mem _ (h (by simp)) (g (by simp)) -- assumption carried?
    | mul_X a i h=>
       rw [show MvPolynomial.X i= glyph (com (Finsupp.single i 1)) from by rw [com_text,blade,Finsupp.linearCombination_single,one_smul]]; refine verse_mul (k:=0) (n:=0) ⊤ (h (by simp)) ?_; apply weaken_v (T:=(⊤ : Submodule ℝ (Fan G))) (show 0≤0+1 by omega); exact verse_glyph (k:=0) (by rw [grade0]; simp) (by simp)
end YM.PositionX.Clove
