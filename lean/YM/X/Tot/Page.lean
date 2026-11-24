import YM.X.Tot.Atom
import YM.X.Tot.Abacus
/-!
# Travel budget program for leading mark/vertex. Arbitrary slot count possible and set of pins. Used for remembering helicity and colors at highest classical data only. Signed displacements path-indexed.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Tot
open Lattice Wilson Next.Rank Normal MvPolynomial Function Filter Set MeasureTheory Asymptotics
open PertExtension LatticePT Heat.Top Crate Porch Rays Clove Interval Size Braid Reed Shelf
open Stems hiding X
open Ocean Haze Friend Fielding Print Fund Tri
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{q:ℕ+}{d k m l:ℕ} {V W I:Type*} {r R:ℝ} {n:Side}{e:ℝ}
variable (q:ℕ+)
local notation "Fℕ"=>(atTop:Filter ℕ)
local notation "ε"=> epsilon q
abbrev Foam (G:Gauge):= Code (Hair G) ℕ
local notation "R₁"=> Foam G
variable {T:Submodule ℝ (Fan G)} (B:Set (Bone G T))
variable {A:Set ℕ}(x:Fielding.Walk)(y: List (Bone G T))
def priceCo (q:ℕ+)(n:ℤ)(f:Curly G): Foam G :=fun i=> Complex.ofReal (epsilon q i ^ n) • f
def textA (q:ℕ+)(x: List (Bone G T)): Foam G:= priceCo q (-(feelB x:ℤ)) (playB x)
def credit (a:Bone G T)(k:ℕ):= glyph (com (normF (ε k) a))
def Page (q:ℕ+) (A:Set ℕ)(B:Set (Bone G T)):Submodule ℂ (Foam G):= Submodule.span ℂ {f| ∃ (l:List (Bone G T))(g:ℕ→ℂ), Released g ∧ (∀i∈l,i∈B)∧ l.length∈A ∧ f=g • textA q l}
@[simp] lemma empty :textA q ([]:List (Bone G T))=1:= by ext1 i; change ↑(_ ^(-(0:ℕ):ℤ):ℝ) • (1:Curly G)=1; simp
lemma labelP (a:Bone G T)(k:ℕ) :credit q a k= Complex.ofReal (epsilon q k ^(-(tipB a:ℤ))) • docB a:= by unfold credit docB; rw [normF, com_text,com_text]; unfold blade; rw [map_smul,zpow_neg,zpow_natCast]; exact RCLike.real_smul_eq_coe_smul (K:=ℂ) ..
@[simp] lemma text_cons (a:Bone G T): textA q (a::y)=credit q a*textA q y := by ext1 i; rw [Pi.mul_apply,labelP, textA]; let e:=ε i; let x:=tipB a; change (↑(e ^(-(↑(x+feelB y)):ℤ)):ℂ) • (docB a * playB y)=(_ • _)* ((↑(e ^(-(↑(feelB y)):ℤ)):ℂ) • playB y); rw [smul_mul_assoc,mul_smul_comm, smul_smul, Nat.cast_add,neg_add,zpow_add₀ (epsilon_pos q _).ne',Complex.ofReal_mul]
lemma text_len (a:Bone G T)(k:ℕ): credit q a k=textA q [a] k:= by rw [text_cons,empty,mul_one]
lemma page_live (p:ℕ→ℂ)(h:Released p)(ht:∀ b∈ y,b∈ B)(he:y.length∈A): p • textA q y∈ Page q A B:= Submodule.subset_span ⟨_,_,h,ht,he,rfl⟩
lemma page_spec (hp:∀ b∈y,b∈B)(he:y.length∈A): textA q y∈ Page q A B:= (one_smul (ℕ→ℂ) (textA q y) ) ▸ page_live q B y (fun _=>1) (constell 1) hp he
lemma credit_lean (a:Bone G T)(hp:a∈B)(hv:1∈A): credit q a∈Page q A B:= by rw [funext (text_len q a)]; exact page_spec q B _ (by simpa using hp) hv
lemma page_scale {a:ℕ→ℂ}(h:Released a){f:Foam G}(he:f∈ Page q A B): a • f∈ Page q A B:= by
    induction he using Submodule.span_induction with
    | mem i hi=> obtain ⟨v,g,hv,h',hh,rfl⟩:=hi; rw [smul_smul]; exact page_live q B _ _ (breaths h hv) h' hh
    | zero=> rw [smul_zero]; exact Submodule.zero_mem _
    | add a b h hv x y=> rw [smul_add]; exact Submodule.add_mem _ x y
    | smul c x hv h => rw [smul_comm]; exact Submodule.smul_mem _ c h
lemma home_close {X: Set ℕ}(h:A⊆ X){W}(hp:B⊆W):Page q A B ≤ Page q X W:= by apply Submodule.span_le.mpr; rintro _ ⟨l,g,h',hw,hy,rfl⟩; exact page_live q W l g h' (fun i hi=>hp (hw i hi)) (h hy)
lemma echelon (k:ℕ): HC (textA q y k) y.length:= by
   induction y with
   | nil=> rw [empty, List.length_nil]; exact isWeightedHomogeneous_one ..
   | cons i t IH=> rw [text_cons,Pi.mul_apply,List.length_cons,mul_comm]; exact IH.mul (HCglyph _)
def liftCut (d:ℕ): Module.End ℂ R₁:= LinearMap.pi (fun i:ℕ=> (Heat.Top.cut d) ∘ₗ LinearMap.proj i)
lemma cut_acc (p : Foam G)(k:ℕ): liftCut d p k=Heat.Top.cut d (p k):= rfl
lemma through {d} {p:Foam G}(h:p∈Page q A B): liftCut d p∈Page q {d} B:= by
    induction h using Submodule.span_induction with
    | mem i hp=> obtain ⟨l,g,h,hp,h',rfl⟩:=hp; by_cases hv:d=l.length; · rw [show liftCut d (g • textA q l)=g • textA q l from ?_]; exact page_live q B l g h hp hv.symm; ext1 i; change Heat.Top.cut d (g i • _) = _; rw [map_smul, hv, leafy.mp (echelon q l i)]; rfl
                 rw [show liftCut d (g • textA q l)=0 from ?_]; exact Submodule.zero_mem _; ext1 i; change Heat.Top.cut d (g i • _) = _; rw [map_smul,HCne (echelon q l i) hv,smul_zero]; rfl
    | zero=> rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ x y=> rw [map_add]; exact Submodule.add_mem _ x y
    | smul a f _ x=> rw [map_smul]; exact Submodule.smul_mem _ _ x
lemma fares_h (a:ℤ)(ha:0≤a)(hq:1<q.val): Released (fun i=> Complex.ofReal (ε i^a)):= by lift a to ℕ using ha; push_cast; exact ⟨(0:ℂ)^a,(Complex.continuous_ofReal.continuousAt.tendsto.comp (paths hq).cutoff).pow _⟩
lemma verse_page (hq:1<q.val){p:Curly G}(h:p∈ verse T d): priceCo q (-(d:ℤ)) p∈ Page q Set.univ (Set.univ (α:=Bone G T)) := by
    induction h using Submodule.span_induction with
    | mem t ht=> obtain ⟨l,h,rfl⟩:= ht; let c(i:ℕ):=Complex.ofReal (ε i^((feelB l:ℤ)-d)); rw [show priceCo q _ _=c • textA q l from ?_]; exact page_live q _ _ c (fares_h q _ (by omega) hq) (fun _ _=>Set.mem_univ _) (Set.mem_univ _);
                 ext1 i; change _=c i • priceCo q _ _ i; unfold priceCo c; rw [smul_smul, ←Complex.ofReal_mul,← zpow_add₀ (epsilon_pos q _).ne',show (((feelB l):ℤ)-d)+-(↑(feelB l):ℤ)=-(↑d:ℤ) by omega]
    | zero=>rw [show priceCo q (-(d:ℤ)) (0:Curly G)= (0:R₁) from funext fun i=> smul_zero _]; exact Submodule.zero_mem _
    | add a b _ _ x y=> unfold priceCo; simp_rw [smul_add]; exact Submodule.add_mem _ x y
    | smul a b _ h=> unfold priceCo; simp_rw [smul_comm _ a]; exact Submodule.smul_mem _ _ h
lemma page_hor {a:ℤ}{T:Submodule ℝ (Fan G)}{p:Foam G}(h:p∈Badge (Curly G) (Vanished q) (verse T 0))(hq:1<q.val): (fun i=> priceCo q a (p i) i)∈ Page q Set.univ (Set.univ (α:=Bone G T)):= by
   induction h using Submodule.span_induction with
   | mem i hp=> obtain ⟨c,v,h,hp,rfl⟩:=hp; let b(i:ℕ):= epsilon q i ^ a • c i; rw [show (fun i=> _)=b • priceCo q (-(↑(0:ℕ):ℤ)) v from ?_]; exact page_scale q _ (late hq (eps_supp h)) (verse_page q hq hp);
                ext1 i; change priceCo q _ _ _= b i • _; unfold priceCo b; rw [smul_smul,Complex.real_smul]; simp
   | zero=> unfold priceCo;simp_rw [Pi.zero_apply,smul_zero];exact Submodule.zero_mem _
   | add a b _ _ x y=> unfold priceCo;simp_rw [Pi.add_apply,smul_add]; exact Submodule.add_mem _ x y
   | smul a v _ h=> unfold priceCo;simp_rw [Pi.smul_apply,smul_comm _ a]; exact Submodule.smul_mem _ _ h
end YM.PositionX.Tot
