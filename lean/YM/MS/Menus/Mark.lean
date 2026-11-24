import YM.MS.Menus.Tape
/-!
# Power-poly tune Wake: integrity and order change

Given log-polynomial dictionary, here use an elementary patch of lower labels and
 calculate exactly the change in momentum stencils at a single order. `Switch` for lift later.
 No scales or positions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Menus
open Function Filter Set Finset Plane Koszul Cylinder Lab Taylor Lattice Native Bare Focus Landau Momentum Orient Draft Sew Native.Chart Tone Tone.Frame
open Color Lifting Local Local.Physical Submodule Logarithm High Ghost
open Book Convolve Program Flux Native.Wilsonian Native.Studio Paint
open Complex (I)
open scoped Topology ContDiff
variable {G:Gauge}{B: Deck G}(V : LitBook B)(p:Team) {d n:ℕ} (x:ℝ)
section close
variable (A:Acts B d)(H:G.Simple)
lemma olio {E E' E'':Type}[AddCommGroup E][AddCommGroup E'][AddCommGroup E''][Module ℂ E][Module ℂ E'][Module ℂ E''](L:E→ₗ[ℂ] E'→ₗ[ℂ] E'')(F: T E)(f:T E')(p:T ℂ): pairW L F (pairW (LinearMap.lsmul ℂ E') p f)=pairW (LinearMap.lsmul ℂ E'') p (pairW L F f):= by
   funext n; let g (i j k:ℕ): E'':= p i • L (F j) (f k);
   simp only [paired,map_sum,LinearMap.lsmul_apply,map_smul]; change (∑ i∈antidiagonal n,∑ j∈antidiagonal i.2,g j.1 i.1 j.2)=∑ i∈antidiagonal n,∑ j∈antidiagonal i.2,g i.1 j.1 j.2; rw [Convolve.associate (fun i j k=> g j i k) n,Convolve.associate]; refine Finset.sum_congr rfl fun i _=>?_ ; exact Finset.Nat.sum_antidiagonal_swap (n:=i.1) (f:=fun j=> g j.1 j.2 i.2)
include H
lemma rented : Weightless (Spectrum G) (style G p x) (rent V p A x):= by
    let P:=Spectrum G; let T:Glyph B d→ T (Dot G Cover):= fun i=> Glyph.preamble V p i x;
    let U (ζ:Glyph B d)(n:ℕ) := oil A ζ n x; let X := style G p x; let D:=actB (Spectrum G)+ pairW (Spectrum G).touch X; let J:= pairW (LinearMap.lsmul ℂ (Dot G Cover));
    have he c f: actB P (J c f)=J c (actB P f):= by funext n; unfold actB J; simp only [paired,promised, LinearMap.lsmul_apply,map_sum,map_smul]
    have hd (i:Glyph B d): D (J (U i) (T i)) =0:= by rw [show D (J (U i) (T i))=J (U i) (D (T i)) from ?_,show D (T i)=0 from Glyph.pre_free V p i x H,map_zero]; unfold D; simp only [LinearMap.add_apply, olio, J,map_add]; rw [show actB (Spectrum G) _ =_ from he (U i) (T i)] -- lint
    change D _=0; rw [show rent V p A x=∑ g:Glyph B d,J (U g) (T g) from funext fun n=> by unfold rent; simp only [Finset.sum_apply]; rfl,map_sum]; simp_rw [hd,Finset.sum_const_zero]
lemma law : Weightless (Spectrum G) (style G p x) (score V p A x):= by
    let Q := actB (Spectrum G)+ blocks (Spectrum G) (style G p x); change Q (rent V p A x+motto p A x)=0
    have hh : Q (motto p A x)=0 := steady_squares (style G p x) _ (main_law G p x H) (fun i=> ((core_circle G p).actual i x).symm) (fun i=> Tune.parity ((core_circle G p).actual i x) ghostParity) (fun i=> ((A i).proof.actual x).symm)
    rw [map_add,hh,show Q (rent V p A x)=0 from rented V p x A H,zero_add]
end close
-- prepare powers changes
namespace Power
def negate (F:Power G) : Power G:={
   input:=-F.input
   polyn:=F.polyn.neg
   calm:=fun i u=>by simp only [Pi.neg_apply,map_neg,F.calm i u]
   actual:=fun i=>by convert (F.actual i).cash (-1:ℂ) (by simp) using 1; exact (neg_one_smul ℂ _).symm
   allowance:=F.allowance
   ranks:=fun i=>by simpa only [Pi.neg_apply,Submodule.coe_neg,neg_smul,one_smul] using (F.ranks i).smul (-1:ℂ) }
def sub (x y:Power G) : Power G where
   input:=x.input-y.input
   polyn:=x.polyn.sub y.polyn
   actual i:=(x.actual i).sub (y.actual i)
   calm i:= (x.calm i).sub (y.calm i)
   allowance:= max x.allowance y.allowance
   ranks i:= Limit.sub ((x.ranks i).up (by omega)) ((y.ranks i).up (by omega))
end Power

abbrev Price (B:Deck G)(d:ℕ):= Glyph B d→Polynomial ℝ

def lighting (Q: Price B d) (x:ℝ): Dot G Cover:= ∑ c:Glyph B d, (↑((Q c).eval x):ℂ) • Glyph.preamble V p c x 0

def advance (E:Dot G Cover): Dot G Cover:= (Spectrum G).Lap E+(Spectrum G).touch (core G 0) E

variable (A:Acts B d)(Q:Price B d)(X:Power G)
def patch (i:ℕ): Acts B d:= fun j=> if j=i then {register:=(A j).register-Q, proof:=(A j).proof.sub X} else A j
lemma patch_bef {j:ℕ}(h:j≠n): patch A Q X n j=A j:= if_neg h
lemma repair : score V p A x n-score V p (patch A Q X n) x n= lighting V p Q x + advance (X.input x):= by
   let S:= patch A Q X n; have hc : (A n).proof.input x-(S n).proof.input x = X.input x:= by simp [S,patch,Power.sub] -- may `sub_sub`
   have hs (i:Glyph B d) : ∑ j∈antidiagonal n,(oil A i j.1 x - oil S i j.1 x) • Glyph.preamble V p i x j.2= (↑((Q i).eval x):ℂ) • Glyph.preamble V p i x 0:= by
        rw [Finset.sum_eq_single (n,0)]; simp [oil,S,patch] -- check
        · intro j hj hne; by_cases h : j.1=n; · obtain ht:=mem_antidiagonal.mp hj; exact (hne (Prod.ext h (by dsimp; omega))).elim
          simp_rw [oil, show S j.1= A j.1 from patch_bef A Q X h,sub_self,zero_smul]
        simp
   rw [score,score,Pi.add_apply,Pi.add_apply, add_sub_add_comm,lighting]; congr 1
   · unfold rent; simp_rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro c _; rw [← hs c]; exact Finset.sum_congr rfl (fun k _=> (sub_smul (oil A c k.1 x) (oil S c k.1 x) (Glyph.preamble V p c x k.2)).symm)
   rw [sky, sky, add_sub_add_comm, ← map_sub,hc,advance]; congr 1
   rw [← Finset.sum_sub_distrib, Finset.sum_eq_single (0,n)]; dsimp only; rw [← map_sub,hc, style,whoZero]; -- check
   · intro j hj hne; obtain h :=mem_antidiagonal.mp hj; have h' : j.2≠n:= fun g=> hne (Prod.ext (by dsimp; omega) g); rw [patch_bef _ _ _ h', sub_self]
   simp
end YM.MS.Menus
