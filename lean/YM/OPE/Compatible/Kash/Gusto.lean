import YM.OPE.Compatible.Kash.Stencil
import YM.OPE.Compatible.Kash.Lease
import YM.OPE.Compatible.Kash.Sump
import YM.OPE.Compatible.Glim.Xpand
/-! # Uniform supplies of finite-angular scripts. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion
open Flock Libra.Shell Next.Foundations Weir Score Exterior Bloch Next.Free Frequency Streamer AnalyticNext.QuarticMatch.Joint Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Page
variable {i j d k m r l:ℕ}{Z I J:Type}
variable {n:Side}{x t:ℝ}
local notation "C!"=> Curtain (Shade G)
local notation "Φ" n:arg=>Bid.Dir G n
variable {T:Z→ℝ}{g: Filter Z}{A B: Z→ Status G}
-- costs may feed polynomial Θ; anytime along order
structure Gusto (T:Z→ℝ)(g:Filter Z)(A:Z→ Status G)(k m:ℕ): Prop where
        pays : ∃ f:Z→ℝ, RateLE g T f 0 ∧∀ᶠ i in g,UnitL (f i) (A i) k m
namespace Gusto
lemma Congurs (h:Gusto T g A k m)(he:∀ᶠ i in g, ∀ᶠ n in atTop,A i n=B i n):Gusto T g B k m:=by obtain ⟨f,hf,H⟩:=h.pays; exact ⟨_,hf,(H.and he).mono fun i hi=> hi.1.congrZ hi.2⟩
lemma up (h:Gusto T g A k m)(hp:k ≤  d):Gusto T g A d m:=by obtain ⟨f,hf,H⟩:=h.pays; exact ⟨_,hf,H.mono fun _ hi=> hi.taller le_rfl hp⟩
variable (ht:Tendsto T g atTop)
include ht
lemma Zero : Gusto T g (fun _:Z=> (0: Status G)) k m:=⟨fun _=>0,RateLE.const _ ht, Eventually.of_forall fun _=> UnitL.blaze_zero⟩
lemma merge (h:Gusto T g A k m)(hp:Gusto T g B k m):Gusto T g (A+B) k m:=by obtain ⟨f,hf,H⟩:=h.pays; obtain ⟨v,hv,hV⟩:=hp.pays; exact ⟨_,hf.add hv ht,(H.and hV).mono fun _ hh=> hh.1.added hh.2⟩
lemma prod (h:Gusto T g A k m)(hp:Gusto T g B d m):Gusto T g (A*B) (k+d) m:=by obtain ⟨f,hf,H⟩:=h.pays; obtain ⟨v,hv,hV⟩:=hp.pays; refine ⟨fun i=> ((k:ℝ)+1)*((d:ℝ)+1)*f i*v i,?_,(H.and hV).mono fun _ hh=> hh.1.product hh.2⟩; exact (((RateLE.const _ ht).mul hf).mul hv).mono (by norm_num)
lemma importK {v:Z→ℝ}(h:RateLE g T v 0)(hp:Take v A k m):Gusto T g A k m:=by obtain ⟨c,hc,H⟩:=hp.available; exact ⟨_,((RateLE.const c ht).mul h).mono (by norm_num),Eventually.of_forall fun _=> ⟨H _⟩⟩
omit ht in
lemma Down (h:Gusto T g A k m):Gusto T g (-A) k m:=by
        obtain ⟨f,hf,H⟩:=h.pays; refine ⟨f,hf,H.mono (fun i hi=>?_)⟩; have hp:= UnitL.color (-1) hi; change UnitL _ (-(A i)) _ _; refine ?_; rw [show (-1:ℝ) • A i= -(A i) by ext n a b; simp] at hp; simpa only [norm_neg,norm_one,mul_one,one_mul] using hp
lemma purseQ (s:Finset I)(P:I→ Z→ Status G)(hp:∀ i∈s, Gusto T g (P i) d m):Gusto T g (∑ i∈s,P i) d m:=by
       induction s using Finset.induction_on with
       | empty=> rw[sum_empty]; exact Gusto.Zero ht
       | insert i s hi ih=> rw[sum_insert hi]; exact merge ht (hp i (mem_insert_self ..)) (ih (fun j hj=>hp j (mem_insert_of_mem hj)))
end Gusto
abbrev Usher (T:Z→ℝ)(g:Filter Z)(A:Z→ foliage G)(k m:ℕ):Prop:=∀ i:Phase,Gusto T g (fun t n x y=> (A t n x y).seq i.val) (k+i.val) m
namespace Usher
variable {q v:Z→ℝ}{A B:Z→ foliage G} (ht:Tendsto T g atTop)
include ht
lemma adds (h:Usher T g A k m)(hp:Usher T g B k m):Usher T g (A+B) k m:=by intro i;fin_cases i<;>first|exact Gusto.merge ht (h 0) (hp 0)| exact Gusto.merge ht (h 1) (hp 1)|exact Gusto.merge ht (h 2) (hp 2)
lemma sumX (s:Finset I)(P:I→ Z→ foliage G)(hp:∀ i∈s,Usher T g (P i) k m):Usher T g (∑ i∈s,P i) k m:=by induction s using Finset.induction_on with
       | empty=> rw [sum_empty]; intro i; fin_cases i<;> exact Gusto.Zero ht
       | insert i s he ih=> rw[sum_insert he]; exact adds ht (hp i (mem_insert_self ..)) (ih fun i hi=>hp i (mem_insert_of_mem hi))
lemma product (h:Usher T g A k m)(hp:Usher T g B l m):Usher T g (A*B) (k+l) m:=by
     have hv(p s t:Phase)(he:p.val+s.val=t.val): Gusto T g (fun i n x y=> tooth (A i n x y) p * tooth (B i n x y) s) (k+l+t.val) m:= (Gusto.prod ht (h p) (hp s)).up (by omega); intro j; fin_cases j; exact hv 0 0 0 rfl; exact Gusto.merge ht (hv 0 1 1 rfl) (hv 1 0 1 rfl); exact Gusto.merge ht (Gusto.merge ht (hv 0 2 2 rfl) (hv 1 1 2 rfl)) (hv 2 0 2 rfl)
omit ht in lemma grown (h:Usher T g A k m)(hp:k  ≤  d): Usher T g A d m:=fun i=> (h i).up (Nat.add_le_add_right hp _)
lemma less (h:Usher T g A k m)(hp:Usher T g B k m):Usher T g (A-B) k m:=by
     rw[sub_eq_add_neg]; refine adds ht h ?_; intro i; fin_cases i<;> first| exact Gusto.Down (hp 0)|exact Gusto.Down (hp 1)|exact Gusto.Down (hp 2)
variable {e:RootEdge}
lemma Tug (u:G.ColorIndex)(b:Bool)(hp:∀ u:G.ColorIndex,Usher T g (fun i n x=> Pry (functorE x e u) (A i n x)) k m): Usher T g (fun i n x=>Topper (sett n x e) ((Phone G) u) b (A i n x)) k m:=by
     let F(j:G.ColorIndex)(i:Z)(n:Side)(x:Site n):= Mount (sett n x e) ((Phone G) u) b j * Pry (functorE x e j) (A i n x); have he(j): Usher T g (F j) k m:= by rw[← Nat.zero_add k]; refine product (A:=fun _ n x=>Mount (sett n x e) ((Phone G) u) b j) ht (fun i=> Gusto.importK ht (RateLE.const (1:ℝ) ht) ((HeadSet e j _ b) i)) (hp j)
     rw [show (fun i n x=>Topper _ _ _ _)=∑ j,F j from ?_]; exact sumX ht _ _ (fun i _=> he i); funext i n x; rw [Finset.sum_apply,Finset.sum_apply,Finset.sum_apply]; rfl
end Usher
end YM.OPE.Variance
