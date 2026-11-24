import YM.OPE.Compatible.Channel.Vert
/-!
# Slot masks giving plane recovery at end heights
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Set Lattice Laurent MeasureTheory RG Finset Next.Free
open scoped Topology BigOperators Classical
variable {I:Type*} {r d j:ℕ} {T:Type*}[Fintype T]
namespace Script
open Page
abbrev hand (p:Page T r)(n:Side)(i:Fin r):deck T n:=Pi.single (wrap n (p i).1,(p i).2) 1
abbrev circle (p:Page T r)(n:Side):Fin r→ Site n × T:=fun i=> (wrap n (p i).1,(p i).2)
omit [Fintype T]
lemma soloH (p:Page T r)(n:Side)(q:Page T r):render (0:Site n) q (hand p n)= if circle p n=circle q n then 1 else 0:=by
   split
   next h=>
      unfold render hand; simp only [zero_add,show ∀ i,(wrap n (p i).1,(p i).2)=(wrap n (q i).1,(q i).2) from congr_fun h, Pi.single_eq_same, prod_const_one]
   next h=>
      obtain ⟨i,hi⟩:= not_forall.mp (show ¬ ∀ i,circle q n i=circle p n i from fun H=> h (funext H).symm)
      apply prod_eq_zero (mem_univ i); exact (show Pi.single _ _ _=0 by rw [zero_add]; exact Pi.single_eq_of_ne hi _)
lemma centerH {p q:Page T (r+1)} (h:primary p=0)(g:primary q=0)(n:Side)(i:Site n)(he:i≠0): render i q (hand p n)=0:=by
   have hh(z:Page T (r+1)):primary z=(z 0).1:=rfl
   apply prod_eq_zero (mem_univ (0:Fin (r+1))); change hand p n 0 (i+wrap n (q 0).1,(q 0).2)=0
   unfold hand; refine Pi.single_eq_of_ne ?_ _; intro hk; have heq:= Prod.mk.inj hk|>.1; rw [← hh p, ← hh q,h,g,map_zero,add_zero] at heq; exact he heq
lemma centerSync (p:Script T (r+1))(h:pinned p){x:Page T (r+1)}(g:primary x=0)(n:Side): library n p (hand x n)=scribe 0 p (hand x n):=by
    unfold library; rw [Finset.sum_eq_single 0]; swap; · simp
    intro i _ hi; unfold scribe; have hx(j:Page T (r+1)):p j * render i j (hand x n)=0:=by
        by_cases he:p j=0; rw [he,zero_mul]
        rw [centerH g (h j he) n i hi,mul_zero]
    simp_rw [hx,tsum_zero]
lemma segment {x y:Page T r} (h:x≠y) (V:I→ Side){l:Filter I}(H:Tendsto (fun i=>(V i).val) l atTop):∀ᶠ i in l,circle x (V i)≠circle y (V i):=by
    obtain ⟨i,hi⟩:= not_forall.mp (show ¬ ∀ i,x i=y i from fun g=> h (funext g))
    filter_upwards [eventually_unfold V H (x i).1, eventually_unfold V H (y i).1] with j hx hy hg; apply hi; have h:= Prod.mk.inj (show (wrap (V j) (x i).1,_)= (wrap (V j) (y i).1, _) from congr_fun hg i); exact Prod.ext (hx ▸ hy ▸ congr_arg lift h.1) h.2
lemma lands (p:Script T r)(h:Summable p)(x:Page T r) (V:I→Side){l:Filter I} (hv:Tendsto (fun i=>(V i).val) l atTop): Tendsto (fun j=>scribe (0:Site (V j)) p (hand x (V j))) l (𝓝 (p x)):=by
    let f (i) y:= p y*render (0:Site (V i)) y (hand x (V i));let g(y):= if y=x then p y else 0
    have hp(y) : Tendsto (fun i=> f i y) l (𝓝 (g y)):= by
       unfold f g; simp_rw [soloH]; split
       next h' => subst y; simp; exact tendsto_const_nhds
       next h'=> apply tendsto_const_nhds.congr'; filter_upwards [segment (Ne.symm h') V hv] with i hi; simp [hi]
    have ht:=tendsto_tsum_of_dominated_convergence h.norm hp (Eventually.of_forall fun i y=> show ‖f i y‖≤‖p y‖ by unfold f; rw [soloH]; split_ifs<;>simp)
    have hx : ∑' i,g i=p x:= by unfold g; simp
    rw [hx] at ht; exact ht
end Script
end YM.OPE.Flume
