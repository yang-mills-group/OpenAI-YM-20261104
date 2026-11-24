import YM.FormalBulk08.Broc.Dent

/-!
Order-one normalized coordinate tensors; keep volume factor explicitly. This
works on non-shrinkable torus links regardless of period, as unmasked Laurent
identities on the trivial branch.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Broc
open Function Filter Lattice RG Laurent Bloch Exterior
open Reef Lava Gorge Mesa Shore Lotus Wick Series Jets
open Stationary hiding shine Rays
open scoped Topology ENNReal BigOperators Classical
variable {I:Type}{G:Gauge}{n:Side}{t:ℕ}{A σ:ℝ}

def portal (n:Side)(p:Shift (Keys t)):chain (Site n) t:= fun i=>wrap n (fun j=>p (i,j))
def pouchD (x:chain I (t+1))(v:chain (Site n) t):chain (Tor n I) (t+1):= fun i=>(Fin.cons (α:=fun _=>Site n) 0 v i,x i)
lemma portal_eq (x:chain I (t+1))(p:Shift (Keys t)): drip n ∘ packSlot x p=pouchD x (portal n p) := by
    funext j; induction j using Fin.cases
    · simp [Lotus.drip,pouchD]
    next j=> rfl
lemma from_portal (T: Tile (Biglot I) (t+1))(h: Up T)(x:chain I (t+1))(y: chain (Site n) t):
    cum 0 n T (pouchD x y) = ∑' v:{p:Shift (Keys t)// portal n p=y}, allele T x v.val:= by
    rw [cum_near 0 n h _ ((0:Cover),x 0) (by simp [Lotus.drip,pouchD])]
    let F (v:{p:Shift (Keys t)// portal n p=y}): Picks 0 n (0,x 0) (pouchD x y):=⟨packSlot x v.val,rfl,(portal_eq x v.val).trans (congr_arg (pouchD x) v.property)⟩
    have he:Bijective F:=by
        constructor
        · intro a b e; exact Subtype.ext ((pack_shift x a.val).symm.trans ((congr_arg (fun p=>arcSlot p.val) e).trans (pack_shift x b.val)))
        intro w; let p:=arcSlot w.val; have hp: arcType w.val=x:= funext fun k=> congr_arg Prod.snd (congr_fun w.property.2 k)
        have hh:=pack_back w.val; rw [w.property.1,hp] at hh; have hx:packSlot x p=w.val:= by
            rw [←hh]
            funext i;ext <;> simp [p]
        have hz:pouchD x (portal n p)=pouchD x y:= (portal_eq x p).symm.trans ((congr_arg (drip n ∘ ·) hx).trans w.property.2)
        exact ⟨⟨p,funext fun i=> congr_arg Prod.fst (congr_fun hz i.succ)⟩,Subtype.ext hx⟩
    exact (Equiv.tsum_eq (Equiv.ofBijective F he) (fun w=>T w.val)).symm
lemma phase_panel (p: chain (Site n) (t+1))(x:Shift (Keys t)): mode (outphase p) x=∏ i:Fin t,cell (p i.succ) (portal n x i):= by
    unfold mode;rw [Fintype.sum_prod_type,Finset.mul_sum,Complex.exp_sum];symm;unfold portal;simp_rw [cell_wrap];rfl
lemma phase_sheet (T:Tile (Biglot I) (t+1))(h:Up T)(x:chain I (t+1))(p: chain (Site n) (t+1))(H:Width σ A (allele T x))(hs:0≤σ) : readable (allele T x) (outphase p)=∑ v: chain (Site n) t,(∏ i:Fin t,cell (p i.succ) (v i))*(cum 0 n T (pouchD x v):ℂ) := by
   let f y := mode (outphase p) y*(allele T x y:ℂ)
   have he : Summable f:= by
      apply Summable.of_norm
      unfold f;simp_rw [norm_mul, mode_real _ _ (out_real p),one_mul,Complex.norm_real]; exact (H.summable hs).norm
   rw [readable,Laurent.read]; change (∑' y,f y)=_;rw [←(he.hasSum.tsum_fiberwise (portal n)).tsum_eq,tsum_fintype];refine Finset.sum_congr rfl fun v _=>?_
   rw [from_portal T h,Complex.ofReal_tsum,←tsum_mul_left]; unfold f;simp_rw [phase_panel]; exact tsum_congr fun i=> by have ht:portal n i.val=v:= i.property;rw [ht]
lemma phases_sum (p : chain (Site n) t)(y: Site n): cell (∑ j,p j) y=∏ i,cell (p i) y := by
   rw [cell_duality]; conv_rhs=>arg 2; intro i; rw [cell_duality]
   generalize Finset.univ (α:=Fin t)=S; induction S using Finset.induction_on with
   | empty=> simp
   | insert i s h ih=> rw [Finset.sum_insert h, Finset.prod_insert h, cell_add, ih]

lemma positions (a: Site n)(v:chain (Site n) t)(x:chain I (t+1)): (fun i:Fin (t+1)=> ((a+Fin.cons (α:=fun _=>Site n) 0 v i),x i))= Lotus.tint a ∘ (pouchD x v):= by funext i; rw [Function.comp_apply]; apply Prod.ext _ _; exact add_comm ..;rfl
lemma through_port (T: Tile (Biglot I) (t+1))(h: Up T)(x: chain I (t+1))(p:chain (Site n) (t+1))(H:Width σ A (allele T x))(hs:0≤σ): (∑ y:chain (Site n) (t+1),(∏ i,cell (p i) (y i))*(cum 0 n T (fun i=>(y i,x i)):ℂ)) = if ∑ j,p j=0 then (Fintype.card (Site n):ℂ)*readable (allele T x) (outphase p) else 0 := by
    let e := Fin.consEquiv (fun _:Fin (t+1)=>Site n); rw [← Equiv.sum_comp e,Fintype.sum_prod_type]
    let g (q:chain (Site n) (t+1)):=(∏ j,cell (p j) (q j))*(cum 0 n T (fun i=>(q i,x i)):ℂ); let C:=readable (allele T x) (outphase p)
    have he (a: Site n): (∑ v: chain (Site n) t,g (e (a,v)))=cell (∑ i,p i) a * C:= by
        rw [←Equiv.sum_comp (Equiv.addLeft (fun _:Fin t=>a))]; unfold C;rw [phase_sheet T h _ _ H hs, Finset.mul_sum]; apply Finset.sum_congr rfl; intro v _
        have he : e (a, (Equiv.addLeft (fun _:Fin t=>a)) v)=fun i=> a+Fin.cons (α:=fun _=>Site n) 0 v i:= by ext1 j; induction j using Fin.cases <;> simp [e]
        unfold g; rw [he,positions,Up.stir _ _ h _ _,phases_sum]; simp_rw [cell_add,Finset.prod_mul_distrib];rw [mul_assoc];congr 2;rw [Fin.prod_univ_succ (f:=fun i=> cell (p i) (Fin.cons (α:=fun _=>Site n) 0 v i))];simp
    change (∑ a: Site n,∑ v:chain (Site n) t,g (e (a,v)))=if ∑ j,p j=0 then (Fintype.card (Site n):ℂ)*C else 0; simp_rw [he];rw [←Finset.sum_mul];split
    next ht=> rw [ht]; simp [cell]
    next ht=> rw [sum_cell ht,zero_mul]
section project
variable [Fintype I][DecidableEq I]
omit [Fintype I] in
lemma harlot  (y : chain (Site n) t)(p:chain (Site n) t)(c b:chain I t)(h:c≠b):
    (∏ i,relay (p i) (b i) (y i,c i))=0:= by
    obtain ⟨a,ha⟩:= Function.ne_iff.mp h; exact Finset.prod_eq_zero (Finset.mem_univ a) (by simp [relay,tune,ha] : relay (p a) (b a) (y a,c a)=0)
lemma cinema (T: Tile (Biglot I) (t+1))(h: Up T)(x: chain I (t+1))(p:chain (Site n) (t+1))(H:Width σ A (allele T x))(hs:0≤σ):
    recording (fun v=>(cum 0 n T v:ℂ)) (fun i=> relay (p i) (x i)) = if ∑ j,p j=0 then (Fintype.card (Site n):ℂ)*readable (allele T x) (outphase p) else 0:= by
   rw [recording_apply, ← through_port T h x p H hs]; let e:= (Equiv.arrowProdEquivProdArrow (Fin (t+1)) (fun _=>Site n) (fun _=> I)).symm; rw [← Equiv.sum_comp e,Fintype.sum_prod_type,Finset.sum_comm,Finset.sum_eq_single x]
   · refine Finset.sum_congr rfl fun y _=> ?_; congr 1; exact Finset.prod_congr rfl fun j _=> by simp [relay,tune,e]
   · intro b _ hb; apply Finset.sum_eq_zero; intro a _; have he:=harlot a p b x hb;rw [show ∏ i,relay (p i) (x i) (e (a,b) i)= _ from he,zero_mul]
   simp
end project

def pixel (T : Tile (edgeL G) (t+1)): Picture G t := fun a b=>readable (allele T fun j=>(b j,a j))
lemma lit_pixel (T : Tile (edgeL G) (t+1))(h: Up T)(p:chain (Site n) (t+1))(H:Bail (fame _) σ T A)(hs:0≤σ)(a b): recording (fun v=>(cum 0 n T v:ℂ)) (glyph p a b)=collected (pixel T) p a b:= cinema T h _ p (allele_width T H hs _) (by positivity)
lemma pitch (T : Tile (edgeL G) (t+1))(h:Bail (fame _) σ T A)(hs:0<σ)(x i): Firm (σ/((t:ℝ)+1)) A (pixel T x i):= by
   unfold pixel readable; apply Firm.of_series;swap;· positivity
   simpa only [Width,Complex.norm_real] using allele_width T h hs.le (fun j=>(i j,x j))
end YM.FormalBulk08.Broc
