import YM.MS.Milk.Moist
import YM.Next.RANK.GaussLeg
import YM.MS.Awning.Press
/-!
# Free Wilsonian solution ($MS physics$) in coordinate kernel.Design any actual alphabet
 and full cost constraints. Use signed Wick polynomial operations (Next.RANK.NORMAL).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Milk
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Landau Detect Heat Tone Latch Latch.Job Rake Orbit Breeze Book Convolve Flux
open Analysis Submodule InnerProductSpace City Next.Rank Next.Rank.Normal Theater Drops Maxwell
open Tensor (diagonal)
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace
variable {A X:Type}{G:Gauge}{n d r:ℕ}{s:ℝ}{f:ℝ→ℂ}
local infix:70 " ⋆ "=> product (field Landau.parity)
local notation "Φκ"=> field (P:=QP) ( Landau.parity ( C:=G.ColorIndex ) ( A:=Axis ) )
variable {W E I:Type}{L:Album X G}{U V:ℝ→Law G}{g:X→Normal.poly X}
variable {u v:ℝ→ Normal.Symmetric X}{Q:Normal.Symmetric X}
def Latest (L:Album X G)(u:ℝ→ Normal.Symmetric X)(i j:X)(l:Filter ℝ)(q:ℂ): Prop:= Tendsto (fun s:ℝ=> (u s).cov i j) l (𝓝 q)
lemma centerS {Y:Type}{F:Y → ℂ}{V:I→ Y→ℂ}(u:(Y→ℂ)→ℂ){p:Filter I}(h:u∈ Heat.Centre Y)(hv:∀ i,Tendsto (fun j=> V j i) p (𝓝 (F i))): Tendsto (fun j=> u (V j)) p (𝓝 (u F)) := by
    refine Submodule.span_induction (p:=fun u _=> Tendsto (fun j=> u (V j)) p (𝓝 (u F))) ?_ tendsto_const_nhds (fun _ _ _ _ h hv=>h.add hv) (fun c _ _ h=>h.const_mul c) h; rintro u ⟨t,rfl⟩; exact hv t
lemma pass_s [DecidableEq A](D:A→X)(b:Finset A){l:Filter ℝ}(hp:∀ i j, Tendsto (fun s:ℝ=>( u s ).cov i j) l (𝓝 (Q.cov i j))):∀ w,Tendsto (fun s=> arc (glyphs D b) L u s w) l (𝓝 (Tint L Q (glyphs D b) w)):= by
    induction b using Finset.strongInduction with
    | H b ih=>
       intro w; obtain h|h:= b.eq_empty_or_nonempty; · subst b; unfold arc Normal.glyphs; simp_rw [ Finset.prod_empty,step0 ]; exact tendsto_const_nhds
       obtain ⟨i,hi⟩:=h; let v:= b.erase i; have hx:v ⊂ b:= erase_ssubset hi; rw [ ← insert_erase hi ]; unfold arc; simp_rw [ step_k L D ( Finset.notMem_erase i b ),Pi.add_apply, Finset.sum_apply ]; apply Tendsto.add; · refine centerS _ ( seller (L.H (D i))|>.reaches w ) ( ih v hx ) -- theorem name unknown
       exact tendsto_finsetSum _ fun i' _=> Tendsto.mul (hp _ _) (ih _ ( Finset.ssubset_of_subset_of_ssubset (Finset.erase_subset ..) hx ) w)
lemma last (l:Filter ℝ)(hp:∀ i j, Tendsto (fun s:ℝ=>( u s ).cov i j) l (𝓝 (Q.cov i j)))(p: Normal.poly X): ∀ w,Tendsto (fun s=> arc p L u s w) l (𝓝 (Tint L Q p w)):= by
   classical
   let U: Submodule ℂ ( Normal.poly X ):={
       carrier:= setOf fun p=> ∀ w,Tendsto (fun s=> arc p L u s w) l (𝓝 (Tint L Q p w))
       add_mem' {p q} H F := fun w=> by unfold arc; simp_rw [map_add,Pi.add_apply]; exact (H w).add (F w)
       zero_mem':= fun w=>by unfold arc; simp_rw [map_zero]; exact tendsto_const_nhds
       smul_mem' := fun c p h w=> by unfold arc; simp_rw [map_smul, Pi.smul_apply, smul_eq_mul ]; exact ( h w ).const_mul _ }
   exact (show p∈ U from axis_v U (fun s=>pass_s _ s hp) p)
-- lapse class. Scalars Stay etc. Multiplying Jur. Need proof load tight.P.
open Asymptotics
lemma C0 (c:ℝ→ℂ)(h:Tall0 c) (F:(ℝ→ℂ)) (hx:Sharp0 F): Sharp0 (fun t=> c t* F t):= solar0 h hx
lemma δ (i: I) (p:ℝ):p=p:=rfl -- remove
abbrev Giant (U:ℝ→ Law G): Prop:= ∀ w,Tall0 (fun s=> U s w)
abbrev Clean (U:ℝ→ Law G): Prop:= ∀ w,Sharp0 (fun s=>U s w)
abbrev trunk (U V:ℝ→Law G)(s:ℝ): Law G:= U s ⋆ V s
def Meat (f:ℝ→ℂ)(U:ℝ→Law G): ℝ→Law G:= fun s=> f s • U s
lemma giant_p (hp:Giant U)(c:Tall0 f): Giant (Meat f U):= fun w=> shiver c (hp w)
lemma clean_p (h:Clean U)(hp:Tall0 f): Clean (Meat f U) := fun w=> solar0 hp (h w)
lemma clean_p' (h:Giant U)(hp:Sharp0 f): Clean (Meat f U):= fun w=> solar1 (h w) hp
lemma Giant.zero: Giant (0:ℝ→ Law G):= fun w=> tall0 fun k=> shorn0 _
lemma Clean.zero: Clean (0:ℝ→Law G):= fun w k=> shorn0 _
lemma Giant.add (hx:Giant U)(hp:Giant V): Giant (U+V):= fun w=> sunny0 (hx w) (hp w)
lemma Clean.add (hx:Clean U)(hp:Clean V): Clean (U+V):= fun w n=> (hx w n).add (hp w n)
lemma Giant.smul (hp:Giant U)(x:ℂ): Giant ( x • U ):= fun w=> ( hp w ).imp (fun z h=> h.const_mul_left x)
lemma Clean.smul (hp:Clean U)(x:ℂ): Clean (x • U) := fun w k=> (hp w k).const_mul_left x
lemma gPack {t:Finset I}{A:I→ℝ→Law G}(h:∀ i∈t,Giant (A i)) : Giant ( ∑ i∈t,A i):= by
    classical
    induction t using Finset.induction_on with| empty=> rw [Finset.sum_empty]; exact Giant.zero| insert i s hi ih=> rw [Finset.sum_insert hi]; exact Giant.add (h i (by simp)) (ih fun j hv=> h j (by simp [hv]))
lemma cPack {t:Finset I}{A:I→ℝ→Law G}(h:∀ i∈t,Clean (A i)):Clean (∑ i∈t,A i):= by
    classical
    induction t using Finset.induction_on with| empty=> rw [ Finset.sum_empty ]; exact Clean.zero| insert i s hi ih=> rw [ Finset.sum_insert hi ]; exact Clean.add (h i (by simp)) (ih fun j hv=>h j (by simp [hv]))
end YM.MS.Milk
