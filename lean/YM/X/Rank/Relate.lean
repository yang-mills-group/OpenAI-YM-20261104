import YM.X.Rank.View
/-!
Finite list of color assignments and real Wick observables. If related point
functions preserve all free expectations, all polynomial products of separately
named, possibly repeated probes can be used with a Kronecker color draw.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Rank
open Function Set Filter MeasureTheory Matrix Screen Maxwell Wick Maxwell.Free
open Next.Rank.Normal MvPolynomial
open scoped Topology BigOperators Classical
variable {G : Gauge} {n : ℕ} {x : Points n}
structure Relation (r : WickPol G → WickPol G→Prop) : Prop where
  team (v : Flavor 0): r (Maxwell.Free.team G v v) (Maxwell.Free.team G v v)
  match_ (n : ℕ) (x : Points n)(p q : Fin n→ WickPol G) : x∈conf n → (∀ i,r (p i) (q i)) → moment G x p=moment G x q

def fuse (x : Points n)(p:Fin n→WickPol G) : Canvas G:= ∏ i, prim (x i) (p i)
def look (x:Points n) : Finset E4:= Finset.univ.image x.ofLp
lemma fuse_cons (x : Points n)(y : E4)(a:WickPol G)(p) : fuse (Points.cons y x) (Fin.cons a p)=prim y a*fuse x p:= by rw [fuse,Fin.prod_univ_succ]; rfl -- simp
lemma look_step (x:Points n)(y:E4): look (Points.cons y x)=insert y (look x):= by ext i; simp [look,Fin.exists_fin_succ,Points.cons,points,eq_comm]
lemma fuse_fits (x:Points n)(p) : Fits (look x) (fuse (G:=G) x p):= by
  let u:= supported ℂ {j:Fiber G| j.1.1∈look x}; apply u.prod_mem; intro i _; rw [prim, AlgHom.comp_apply, mem_supported]; intro v hv; obtain ⟨j,hj,rfl⟩:= mem_vars_rename _ _ hv; exact Finset.mem_image_of_mem x.ofLp (Finset.mem_univ i)
variable (c : G.ColorIndex) {r:WickPol G→WickPol G→Prop} (hr: Rank.Relation r)
include hr
lemma Relation.silent {p q} (hx:x∈conf n)(he:∀ i:Fin n,r (p i) (q i)): Silent c (fuse x p-fuse x q) (look x):= by
   intro W hW
   induction W generalizing n with
   | nil=> rw [clothe,List.map_nil,List.prod_nil,one_mul,map_sub]; exact sub_eq_zero.mpr ((wick_prim c hx p).symm.trans ((hr.match_ n x p q hx he).trans (wick_prim c hx q)))
   | cons a W ih=>
     obtain ⟨h,hv,hU⟩:= (adm_cons ..).mp hW
     let y:=Points.cons a.1 x
     have hy:y∈conf (n+1):= by
       change Injective (Fin.cons (α:=fun _ : Fin (n+1)=> E4) a.1 x.ofLp); exact Fin.cons_injective_iff.mpr ⟨fun ⟨i,hi⟩=> h (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi⟩),hx⟩
     let t:= Maxwell.Free.team G a.2 a.2; have ht:=ih (x:=y) (p:=Fin.cons t p) (q:= Fin.cons t q) hy (fun i=> Fin.cases (hr.team a.2) he i) (by unfold y; rw [look_step]; exact ⟨hU.1,Finset.disjoint_insert_right.mpr ⟨hv,hU.2⟩⟩)
     simp only [y,fuse_cons] at ht
     rw [clothe_cons,patch_eq a a.2]; change E c ( (prim a.1 t*clothe W)*_)=_; rw [mul_right_comm _ (clothe W),mul_comm _ (clothe W),mul_sub]; exact ht
include c
lemma Relation.mirrorWords {p q:Fin n→ WickPol G} (he:∀ i:Fin n,r (p i) (q i))(A:Fin n→ Sample G) : Mirrors (fun x:Tile G.ColorIndex=> (∏ i,helps (coatV (folio x) (A i)) (p i)) - ∏ i,helps (coatV (folio x) (A i)) (q i)) := by
   let x (i:Fin n):E4:= ((↑i.val:ℝ)) • YM.basis 0; have h: Injective x:= by intro i j hij; have he:= congr_arg (fun (x:E4)=>x 0) hij; simp [x] at he; exact Fin.ext he -- edit
   let Y:=points x; have hY:Y∈conf n:=h
   let F := fuse Y p-fuse Y q; have ht:= Relation.silent c hr hY he
   have hh: Fits (look Y) F := Subalgebra.sub_mem _ (fuse_fits (G:=G) Y p) (fuse_fits (G:=G) Y q)
   let B (z:Stroke): G.Color:= Function.extend x A (fun _ _=>0) z.1 z.2
   have hb (i k):B (x i,k)=A i k:= by unfold B; rw [h.extend_apply]
   have hE i (T:Tile G.ColorIndex) (p:WickPol G): helps (coatV (folio T) (A i)) p=foul T (prim (x i) p) B:= by
      unfold foul prim pluck helps; simp only [AlgHom.comp_apply]
      -- cross cost
      suffices H:(aeval (fun k:Key G=> (coatV (folio T) (A i) k.1 k.2:ℂ)):Poly G →ₐ[ℂ]ℂ)=(aeval _).comp (rename (pin (x i))) from DFunLike.congr_fun H (paint G p)
      ext1 u; rw [AlgHom.comp_apply,rename_X,aeval_X,aeval_X]; unfold pin; dsimp only; rw [hb]; rfl
   have heq(T:Tile G.ColorIndex): foul T F B=(∏ i,helps (coatV (folio T) (A i)) (p i))-∏ i,helps (coatV (folio T) (A i)) (q i):= by unfold F fuse; simp_rw [hE]; unfold foul; simp only [_root_.map_sub,_root_.map_prod]; rfl
   convert Mirrors.fires F c B hh ht using 1; exact funext fun T=> (heq T).symm
end YM.PositionX.Rank
