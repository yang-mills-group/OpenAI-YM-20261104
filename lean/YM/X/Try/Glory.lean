import YM.X.Try.Spire
/-! # valuations for histogram products. Longitudinal ∗owned weight∗ and translated curvature comparisons. -/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Tri
open Lattice Wilson Next.Rank Normal LiftMark CellsInt Beamer MvPolynomial Function Filter Set Asymptotics
open Reed Source PertExtension LatticePT Plate Clove Braid Fielding Print
open Stems hiding X
open Heat.Top
open scoped Topology ContDiff BigOperators Pointwise Classical
variable {G:Gauge} {d n m k:ℕ} {V W I:Type*}
local notation "H"=> Hair G
-- Stone changes on leading symbol. S is ⊤ (general) or Horizontal (costly).
def Stone (S:Submodule ℝ (Fan G))(d:ℕ) (p q:Curly G):Prop:= q∈verse S d∧ p-q ∈ verse S (d+1)
namespace Stone
variable {S:Submodule ℝ (Fan G)}{p p' q q':Curly G}
lemma sta (h:Stone S d p q):p∈verse S d:=by obtain ⟨h,h'⟩:=h; exact sub_add_cancel p q ▸ (verse S d).add_mem (weaken_v d.le_succ h') h
lemma tier {T:Submodule ℝ (Fan G)} (ht:S≤T)(h:Stone S d p q):Stone T d p q:= ⟨tier_v ht h.1,tier_v ht h.2⟩
lemma along (he:p∈verse S d):Stone S d p p:= ⟨he,by rw [sub_self];exact Submodule.zero_mem _⟩
lemma quiet (he:p∈verse S (d+1)): Stone S d p 0:=⟨Submodule.zero_mem _,by rwa [sub_zero]⟩
lemma compose (h:Stone S d p q)(ht:Stone S d q p') : Stone S d p p':=⟨ht.1,by
   rw [show p-p'=(p-q)+(q-p') by ring]; exact (verse S (d+1)).add_mem h.2 ht.2⟩
lemma swap(h:Stone S d p q):Stone S d q p:= ⟨h.sta,by rw [← neg_sub]; exact (verse S _).neg_mem h.2⟩
lemma weaker (h:Stone S d p q)(hi:k≤d): Stone S k p q:= ⟨weaken_v hi h.1,weaken_v (Nat.succ_le_succ hi) h.2⟩
lemma scalp (a:ℂ)(h:Stone S d p q):Stone S d (a • p) (a • q):= ⟨(verse S d).smul_mem a h.1, by rw [← smul_sub];exact (verse S _).smul_mem a h.2⟩
lemma add (h:Stone S d p q)(he:Stone S d p' q'):Stone S d (p+p') (q+q'):=⟨(verse S _).add_mem h.1 he.1,by rw [add_sub_add_comm]; exact (verse S _).add_mem h.2 he.2⟩
lemma sub (h:Stone S d p q)(he:Stone S d p' q'):Stone S d (p-p') (q-q'):= by have ht:= h.add (he.scalp (-1)); rwa [neg_one_smul,neg_one_smul,←sub_eq_add_neg,←sub_eq_add_neg] at ht
lemma mul (h:Stone S d p q)(g:Stone S n p' q'):Stone S (d+n) (p*p') (q*q'):= by
    refine ⟨verse_mul _ h.1 g.1,?_⟩; rw [show p*p'-q*q'=(p-q)*p'+q*(p'-q') by ring]; apply Submodule.add_mem; · rw [show d+n+1=d+1+n by omega]; exact verse_mul _ h.2 g.sta
    rw [Nat.add_assoc]; exact verse_mul _ h.1 g.2
lemma sums {p q:I→Curly G}(t:Finset I)(h:∀i∈t,Stone S d (p i) (q i)):Stone S d (∑ i∈t,p i) (∑ i∈t,q i):= by induction t using Finset.induction_on with| empty=> simp only [Finset.sum_empty]; exact along (Submodule.zero_mem _) | insert i t he IH=> rw [Finset.sum_insert he, Finset.sum_insert he]; exact (h i (by simp)).add (IH (fun j hj=>h j (by simp [hj])))
lemma pow (h:Stone S d p q)(n:ℕ):Stone S (n*d) (p^n) (q^n):=by induction n with| zero=> rw [pow_zero,pow_zero,Nat.zero_mul];exact along verse_one|succ n IH=>rw [pow_succ,pow_succ,add_mul,Nat.one_mul]; exact IH.mul h
lemma prod {p q:I→Curly G}(d:I→ℕ)(t:Finset I)(h:∀i∈t,Stone S (d i) (p i) (q i)):Stone S (∑ i∈t,d i) (∏ i∈t,p i) (∏ i∈t,q i):= by induction t using Finset.induction_on with| empty=> rw [Finset.prod_empty,Finset.prod_empty,Finset.sum_empty];exact along verse_one| insert i t he IH=> rw [Finset.prod_insert he,Finset.prod_insert he,Finset.sum_insert he]; exact (h i (by simp)).mul (IH (fun j hj=> h j (by simp [hj])))
lemma mono (F T:poly V→ₐ[ℂ] Curly G)(h:∀i:V,Stone S d (F (X i)) (T (X i)))(a:V→₀ℕ)(c:ℂ): Stone S (d*degree a) (F (monomial a c)) (T (monomial a c)):= by
     rw [MvPolynomial.monomial_eq,map_mul,map_mul, show F (C c)=C c from F.commutes _, show T (C c)=C c from T.commutes _, C_mul',C_mul',degree_eq,Finsupp.prod,Finsupp.sum,Finset.mul_sum,map_prod,map_prod]; apply Stone.scalp _; apply prod; intro i _; rw [map_pow,map_pow,mul_comm d]; exact (h i).pow _
lemma hom (F T:poly V→ₐ[ℂ] Curly G)(h:∀i:V,Stone S d (F (X i)) (T (X i)))(p:poly V)(hg:HC p m): Stone S (d*m) (F p) (T p):= by
    rw [p.as_sum,map_sum,map_sum]; refine Stone.sums _ (fun i hi=>?_); rw [← show degree i=m from hg (mem_support_iff.mp hi)]; exact mono _ _ h _ _
end Stone
-- all local curvature stencils and prototype
local notation "Hθ"=> (Reed.Horizontal G)
lemma by_lane (f:Cover→V)(h:∀ (z:Cover)(i:Axis), f (z+step i)=f z)(z:Cover): f z=f 0:= by
    have he (z:Cover)(l:Lattice.Walk): f (stop z l)=f z:= by
        induction l generalizing z with
        | nil=> rfl
        | cons a l IH=> rw [stop,IH]; unfold Step.vec; split
                        next=> rw [← sub_eq_add_neg,← h (z-step a.dir) a.dir,sub_add_cancel]
                        next=> exact h ..
    exact route_end 0 z 1 ▸ he _ _
lemma coalesced (A:Brush G)(h:Cloudless 1 A)(i:Axis)(z:Cover):A (z,i)= A (0,i):= by
    exact by_lane (raising i A) (fun u k=>sub_eq_zero.mp (congr_fun (h (fun _=>k) i) u)) z
lemma still_curl (A:Brush G)(h:Cloudless 2 A)(i j:Axis)(z:Cover): curl A z i j=curl A 0 i j:= by
   rw [← curling,← curling]; apply by_lane; intro z k; apply sub_eq_zero.mp;
   have hp (i j:Axis): stepValue (raising j A) i (z+step k)-stepValue (raising j A) i z=0:= congr_fun (h ![i,k] j) z -- check steps order
   change (_-_) - (_-_)= (0:G.Color); rw [sub_sub_sub_comm]; rw [hp,hp,sub_zero]
lemma arc_move (p:Address G) : signal_arc p - signal_arc (0,p.2)∈grads G 2:= by apply (cloud_ann _).mpr; intro A h; simp only [map_sub,arc_flat, sub_eq_zero]; change curlL _ _ _ _ _=curlL _ _ _ _ _; simp only [curling, still_curl A h _ _ p.1] -- h instantiate
abbrev CoverC (G:Gauge):= PlaqAxes × G.ColorIndex
def bindB(x:CoverC G):= signal_arc (0,x.1,x.2)
def dialF : Normal.poly (CoverC G)→ₐ[ℂ] Curly G:= exchange (Stems.com ∘ bindB)
def drop (x:Atom G): CoverC G:= (x.1.plaq,x.2)
def lump := MvPolynomial.rename (R:=ℂ) (drop (G:=G))
lemma stone_arc (p:Atom G): Stone Hθ 2 (loom (X p)) ((dialF.comp lump) (X p)):= by
     let y:= Heat.Ray.address p; let Z: Address G:=(0,y.2); rw [loom, AlgHom.comp_apply,lump, rename_X,dialF,exchange_x,exchange_x]; change Stone Hθ 2 (glyph (Stems.com (signal_arc y))) (glyph (Stems.com (signal_arc Z))); have hs(x:Address G): signal_arc x∈Horizontal G:= Submodule.subset_span ⟨_,rfl⟩
     refine ⟨verse_glyph (k:=1) (arc_occ Z) (hs _),?_⟩; unfold Stems.com; rw [← map_sub,← map_sub]; exact verse_glyph (k:=2) (arc_move y) (Horizontal G|>.sub_mem (hs y) (hs Z))
lemma stoneF {p: poly (Atom G)}(h:HC p d) : Stone Hθ (2*d) (loom p) (dialF (lump p)):= Stone.hom _ (dialF.comp lump) stone_arc _ h
-- analogous evaluation-kernel statement for open highest symbol C A
local notation "L"=> (⊤:Submodule ℝ (Fan G))
def vanishZ (p:Hair G):Hair G:= ((0,p.1.2),p.2)
def pressP := MvPolynomial.rename (R:=ℂ) (vanishZ (G:=G))
lemma press_eval (A:Brush G)(p:Curly G): snap A (pressP p)=snap (fun u=> A (0,u.2)) p:= by rw [pressP,snap,aeval_rename]; rfl
lemma ystar (b:H): Stone L 1 (X b) (X (vanishZ b)):= by
   let f:= Finsupp.single b (1:ℝ); let g:=Finsupp.single (vanishZ b) (1:ℝ); refine ⟨verse_x _,?_⟩; rw [show X b-X (vanishZ b)=glyph (com (f-g)) from ?_] -- notation
   · refine verse_glyph (k:=1) ((cloud_ann _).mpr (fun A hx=>?_)) (by simp); rw [map_sub,flat₁,flat₁]; exact sub_eq_zero.mpr (congr_arg (fun x:G.Color=>x b.2) (coalesced A hx b.1.2 b.1.1))
   rw [com_text]; unfold blade f g; rw [map_sub,Finsupp.linearCombination_single,Finsupp.linearCombination_single,one_smul,one_smul]
lemma pressureP (p: Curly G)(h:HC p d): Stone L d p (pressP p):= by
   have he (i:H) : Stone L 1 ((AlgHom.id ℂ _) (X i:Curly G)) (pressP (X i)):= by rw [pressP,MvPolynomial.rename_X]; exact ystar i
   simpa using! Stone.hom _ _ he p h
end YM.PositionX.Tri
