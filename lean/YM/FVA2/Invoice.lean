import YM.FVA2.Coupling
/-!
# Normalized coefficients for pure selection of representatives

In particular their identity after combining interactions on the root. Tail-first:
calls to sectors will receive original finite `integrandSeries`, not hasty
rescaled insertion. Supports open coarse tests on the original observables.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Inversion
open Function Set Finset Filter Lattice MS MS.Koszul MS.Swirl MS.Native MS.Orbit MS.Orbit.Cog
open MS.Orbit.LogReal MS.Bare MS.Cylinder MS.Cylinder.Taylor MS.Puff MS.Puff.Mom MS.Book
open MS.Book.Convolve MS.Swirl.Near MS.Cylinder.Lab MS.Native.Wilsonian MS.Puff.Actors
open PertExtension PertExtension.Orb Substitute Matrix Coupling Ends Inserted
open scoped Classical Topology ContDiff

variable {G:Gauge} {n:Side} (h:Even n.val)
local notation "A"=> Choice.allLetters G n
local notation "P"=> Words G n
local notation "Z!"=> Z G (OEdge n)
local notation "F"=> rootedVertex G n
local notation "V"=> fullRoot G n
local notation "R"=> baseProp G n
local notation "L"=> baseFix G n
local notation "σ"=> Letter.p
local notation "H"=> Letter.grain R L
local notation "S"=> BackRoot (n:=n) (G:=G)
local notation "X!"=> Bplane G n
set_option quotPrecheck false
local infixr:70 " ⋄ "=> (PermV σ).core

variable {W : Type}[LinearOrder W] (s:Finset W) (ι:W→ Unscaled G)(x:W→ Cover)

def unscaleTot (s:Finset W)(ι:s → Unscaled G) := ∑ i:s,(ι i).degree
def unscaleFull (s:Finset W) (ι:s→ Unscaled G)(x:W→ Cover)(n:Side): Wilson.Config G n→ℝ:= ∏ i:s,(ι i).carries (x i.val) n

def expenditure (G : Gauge)(n:Side)(O:Wilson.Config G n→ℝ) : Sc:= fun i=> (Orb.diag (Orb.restrictedO O) i:ℂ)
/-- **No mention of MS inputs**. Uses exactly the normalized tree costs, with Laurent prefactor. -/
def pureVia (n:Side)(s:Finset W)(ι:s→Unscaled G)(x:W→ Cover) : Sc :=
    cutg (unscaleTot s ι) (expenditure G n (unscaleFull s ι x n))

abbrev order_g := ∑ i∈s,(ι i).degree
abbrev invoice (n:Side) := ∏ i∈s,(ι i).nativeMark (x i) n
lemma real_price (n:Side) (ι:W→Unscaled G) : unscaleFull s (fun i=> ι i.val) x n = ∏ i∈s,(ι i).carries (x i) n:= Finset.prod_coe_sort s (fun i=> (ι i).carries (x i) n)
lemma degree_price : unscaleTot s (fun i=> ι i.val)=order_g s ι:= Finset.sum_coe_sort s (fun i=> (ι i).degree)
lemma actual : invoice s ι x n=unscaleFull s (fun i:s=> ι i.val) x n ∘ liftLinks ∘ Ends.exp_A:= by
   funext a; rw [real_price]; simp only [invoice, Function.comp_apply,Finset.prod_apply]
lemma original_inv : (root n).invariant (unscaleFull s (fun i:s=> ι i.val) x n∘ liftLinks):=by
   rw [real_price]; intro u p; simp only [Function.comp_apply,Finset.prod_apply]; exact Finset.prod_congr rfl fun i _=> (ι i).native_invariant (x i) u p
lemma invoice_germ : germ (invoice s ι x n):= by
   induction s using Finset.induction_on with
   | empty=> simp [invoice]; exact contDiffAt_const
   | insert i s hi IH=> unfold invoice; rw [Finset.prod_insert hi]; exact ( (ι i).native_smooth (x i) ).mul IH

abbrev home (n:Side)(x: Cover)(k:Unscaled G): SpecB (Choice.allLetters G n) := rankLevel k.degree (ink tangentVec (k.nativeMark x n))

abbrev spars (T:W→ SpecB (Choice.allLetters G n)): Mate (Choice.allLetters G n) W := fun p=> if h:p.Nonempty then if p.card=1 then T (p.min' h) else 0 else 0
lemma sp_here (T:W→ SpecB A)(i: W): spars T {i}= T i:= by simp [spars]
lemma sp_e (T:W→ SpecB A)(i:Finset W)(h:i.card≠1): spars T i=0:= by unfold spars; split <;> first | exact if_neg h | rfl

lemma invoice_step {v : W} (hv:v∉s) : invoice (insert v s) ι x n= (ι v).nativeMark (x v) n * invoice s ι x n:= by rw [invoice,Finset.prod_insert hv]
local notation "Ω" => (ink (tangentVec («A»:=OEdge n) («P»:=Vert n) (G:=G)))
local notation "θ" => spars (fun i=> home n (x i) (ι i))

lemma ink_step {v:W}(hv:v∉s) : Ω (invoice (insert v s) ι x n)=
    product σ (Ω ((ι v).nativeMark (x v) n)) (Ω (invoice s ι x n)):= by rw [invoice_step s ι x hv]; exact ink_mul tangentVec (glowGraph.never) ((ι v).native_smooth _) (invoice_germ s ι x)
lemma min_invoice : From (Ω (invoice s ι x n)) (order_g s ι):= by
    induction s using Finset.induction_on with
    | empty=> unfold order_g; rw [Finset.sum_empty,Nat.cast_zero]; intro _ he; omega
    | insert i s hi IH=> rw [ink_step s ι x hi,order_g, Finset.sum_insert hi, Nat.cast_add]; exact ((ι i).root_degree (x i)).pair IH

lemma Font_invoice : Font σ θ s= rankLevel (order_g s ι) (Ω (invoice s ι x n)):= by
    induction s using Finset.induction_on with
    | empty=> rw [show Font σ θ (∅:Finset W)=(PermV (σ: Sector A)).unit from Puff.Stencil.simple_E _ θ (SplitP.marked W) (sp_e _ _ (by change (∅:Finset W).card≠1; simp)),invoice,Finset.prod_empty,order_g,Finset.sum_empty] -- may goal differently i binds
              rw [show Ω 1=coin (1:ℂ) from ink_const _ 1]

              unfold rankLevel; funext v;
              by_cases he:v=0
              · subst v; rw [show (PermV (σ : Sector A)).unit 0=coin (1:ℂ) from if_pos rfl]; ext l; cases l <;> simp [mask,coin]
              rw [show (PermV (σ : Sector A)).unit v=0 from if_neg he]; ext l; cases l <;> simp [mask,coin,Ne.symm he]
    | insert i s hi IH=>
       have hp(T:Finset W) : EvenSeries σ (θ T):= by
          by_cases h:T.card=1
          · obtain ⟨z,rfl⟩:= Finset.card_eq_one.mp h; rw [sp_here]; apply (even_coeff _).mpr; intro j; exact pure_mask (ink_p _ (glowGraph.never) _) _
          rw [sp_e _ _ h]; exact Submodule.zero_mem _
       rw [ Font, Puff.Stencil.cheers _ hp (sp_e _) s i hi, sp_here ];
       change home n (x i) (ι i) ⋄ Font σ θ s=_; rw [IH,show order_g (insert i s) ι= (ι i).degree+order_g s ι from Finset.sum_insert hi,Nat.cast_add, ink_step s ι x hi]; exact funext (fun j=> pairLevel j ( (ι i).root_degree (x i) ) (min_invoice s ι x) )

include h
lemma nakedC : (∀ i,i<order_g s ι→ expenditure G n (unscaleFull s (fun i=>ι i.val) x n) i=0) ∧
   Endμ H σ F (Font σ θ s) (pureVia n s (fun i=>ι i.val) x) := by
    unfold pureVia; rw [degree_price,Font_invoice]; apply divide_E (show Matrix A A ℂ from H) σ (order_g s ι) (rfl) -- nil maybe
    rw [powers_mask _ _ (min_invoice s ι x)];
    refine Cone.WickOnRoot h _ (actual s ι x) (invoice_germ s ι x) ?_ R L gauge_sym (gauge_left h) (master_hes h)
    rw [actual]; have hv:=invoice_germ (n:=n) s ι x; rw [actual] at hv; exact inert_from (root n) _ (original_inv s ι x) hv
-- companion application to Orb.Rows. proof through acyclic merge
end YM.FVA2.Inversion
