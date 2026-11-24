import YM.WilsonCoeffUV.Ward.Impulse

/-! One local Ward field with sublattice-independent hinge. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Power
open Lattice Laurent Bloch Exterior Wilson Precision RG Function Filter Metric
open Blue FreeResolvent Tree Matrix PowerSeries Next.Free Gauge
open scoped ContDiff Topology BigOperators Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {c: Side}{G:Gauge}

section embeds
variable {U V:Type}[Fintype U][Fintype V]

def nameF (e:U→V) : Ink U→+*Ink V:= PowerSeries.map (MvPolynomial.rename e).toRingHom
omit [Fintype U] [Fintype V] in
lemma name_real (e:U→V)(x:ℝ): nameF e (realS x)=realS x:= by simp [realS,nameF]
omit [Fintype U] [Fintype V] in
lemma name_var (e:U→V)(u:U): nameF e (path u)=path (e u) := by simp [nameF,path]
def spear [DecidableEq V] (e:U→V) : Matrix U V ℝ:= of fun i j=> if j=e i then 1 else 0
omit [Fintype U] in
lemma spear_act [DecidableEq V](e:U→V)(u:Lawn V): spear e *ᵥ u=u ∘ e:= by ext i; unfold mulVec dotProduct; rw [Finset.sum_eq_single (e i)] <;>simp +contextual [spear]
omit [Fintype U] in
lemma loom_spear [DecidableEq V](e:U→V): loom (spear e)=nameF e:= by
  have h (i:U) : loom (spear e) (path i)=path (e i):= by rw [loom_pin,Finset.sum_eq_single (e i)]<;>simp +contextual [spear]
  apply serial_ext (by simp [loom]) _ (by simp [loom,nameF]); intro p
  induction p using MvPolynomial.induction_on with
  | C a=> rw [show C _=realS _ from rfl, loom_real,name_real]
  | add p q a b=> simp_rw [map_add,a,b]
  | mul_X p j a=> simp only [map_mul,show C _=path j from rfl,h,name_var,a]
omit [Fintype U] in
lemma paint_spear [DecidableEq V](u:U→V)(f:Lawn V→Lawn U)(h:∀ i: Lawn V,f i=i ∘ u) : train (spool f)=nameF u:= by rw [←loom_spear, show f=fun v=>spear u *ᵥ v from funext fun v=>(h v).trans (spear_act u v).symm]; classical apply spool_loom
omit [Fintype U] [Fintype V] in
lemma work_spear (u:U→V)(i:U)(p:Ink U)(h:Injective u): nameF u (brush i p)= brush (u i) (nameF u p) := by ext1 n; simp only [brush,nameF,coeff_map,blot_apply]; exact (MvPolynomial.pderiv_rename h i _).symm
omit [Fintype U] [Fintype V] in
lemma stop_spear (u:U→V): (stopF 0).comp (nameF (Option.map u))=(nameF u).comp (stopF 0) := by
  let F : Option U→Option V:= Option.map u
  have h c : stopF (U:=V) 0 (realS c)=realS c:= see_real ..
  have h' c : stopF (U:=U) 0 (realS c)=realS c:= see_real ..
  apply serial_ext (by simp [stopF,nameF]) _ (by simp [stopF,nameF]); intro p
  induction p using MvPolynomial.induction_on with
  | C c=> change stopF 0 (nameF F (realS c))= nameF u (stopF 0 (realS c)); rw [name_real, h,h',name_real]
  | add p q a b => simp_rw [map_add,a,b]
  | mul_X p j a=> simp only [map_mul,a,show C _=path j from rfl]; congr 1;
                  rw [RingHom.comp_apply,RingHom.comp_apply,name_var]; cases j <;> simp [stopF,path,stopT_X,nameF]
omit [Fintype V] in
lemma freeze_some : (stopF (U:=V) 0).comp (nameF some)= RingHom.id _ := by
  apply serial_ext (by simp [stopF,nameF]) _ (by simp [stopF,nameF]); intro p
  rw [RingHom.comp_apply,stopF,nameF,map_C,map_C,RingHom.id_apply]; congr 1; apply stopT_launch
omit [Fintype V] in
lemma freeze_brush (p:Ink V) : brush none (nameF some p)=0:=latent p
end embeds
section field
variable (u:Site c→G.Color)
-- all legs, option time gauge
def sourceEdge (i:Edge (Site c)) (a:G.ColorIndex) := entryS G c (i,a)
def into (G:Gauge)(e:Edge (Site c))(w:Lawn (Option (Woods G c))) := w ∘ Option.map (sourceEdge (G:=G) e)
def sole (w:Lawn (Option (Woods G c))) := w ∘ some
def after (w:Lawn (Option (Woods G c)))(i: Woods G c): ℝ:= let j:= (entryS G c).symm i; jerk (u j.1.1) (u (j.1.1+step j.1.2)) (into G j.1 w) j.2
lemma after_here (e:Edge (Site c))(i:G.ColorIndex)(w): after u w (sourceEdge e i)= jerk (u e.1) (u (e.1+step e.2)) (into G e w) i := by simp only [sourceEdge,after,Equiv.symm_apply_apply]
lemma into_green (e:Edge (Site c)): Green (into G e) := contDiffAt_pi.mpr fun _=> contDiffAt_apply ℝ ℝ _ _
lemma after_green : Green (after u) := by
  unfold Green; refine contDiffAt_pi.mpr fun i=>?_
  obtain ⟨⟨x,j⟩,rfl⟩:= (entryS G c).surjective i
  simp_rw [after, Equiv.symm_apply_apply]; apply (contDiffAt_apply ℝ ℝ j _).comp; apply (jerk_green (u x.1) _).comp (f:=into G x) _ (into_green x)
lemma after_zero : after u 0=0 := by ext i; simp only [after,(fun j:Edge (Site c)=>show into G j 0=0 from rfl),jerk_zero]; rfl
lemma pin_ward : TurnsG 1 0 (fun w i=>G.lieExp (w none • u i)) sole (after u):= by
  have hs (i:Site c) : Green fun p:Lawn (Option (Woods G c))=>G.mat (G.lieExp (p none • u i)):= G.exp_jet.contDiffAt.comp (f:=fun p:Lawn (Option (Woods G c))=> p none • u i) 0 ((contDiffAt_apply ℝ ℝ none _).smul contDiffAt_const)
  refine ⟨contDiffAt_pi.mpr (fun _=>contDiffAt_apply ℝ ℝ _ _), after_green u,rfl,after_zero u,hs,?_⟩
  filter_upwards [eventually_all.mpr fun i:Edge (Site c)=> (into_green (G:=G) i).continuousAt.eventually (jerk_exp (u i.1) (u (i.1+step i.2)))] with p hp
  rw [Lattice.pull_id]; funext i; rw [bare_linkC, Lattice.gauge,bare_linkC]
  rw [show dyes' i (after u p)= _ from funext fun j=>after_here u i j p, hp i]; rfl
lemma currents (e:Edge (Site c)): (fun j : G.ColorIndex=> spool (after u) (sourceEdge e j)) = fun j=>
     nameF (Option.map (sourceEdge e)) (spool (jerk (u e.1) (u (e.1+step e.2))) j) := by
   funext j
   classical
   let J:=jerk (u e.1) (u (e.1+step e.2))
   have h : train (spool (into G e))=nameF (Option.map (sourceEdge e)):= paint_spear _ _ fun _=>rfl
   rw [←h, show spool (after u) (sourceEdge e j) = spool (J ∘ into G e) j from ?za]
   simpa only [RingHom.comp_apply,train_path] using (DFunLike.congr_fun (spool_chain (into G e) J rfl (jerk_zero ..) (into_green e) (jerk_green ..)) (path j)).symm
   case za=> apply mul_left_cancel₀ (a:=(PowerSeries.X: Ink (Option (Woods G c)))) X_ne_zero; rw [spool_raised _ (after_zero _),spool_raised (J ∘ into G e) (show (J ∘ into G e) 0=0 from jerk_zero (u e.1) _)]; congr 1; exact funext fun x=> after_here u e j x
lemma source_unique (e:Edge (Site c)): Injective (sourceEdge (G:=G) e) := fun _ _ h=> congr_arg Prod.snd ((entryS G c).injective h)
lemma flux_live (e:Edge (Site c))(j:G.ColorIndex) : stopF 0 (brush none (spool (after u) (sourceEdge e j)))=nameF (sourceEdge e) (jet (electric (u e.1) (u (e.1+step e.2)) j)) := by
  let N:= Option.map (sourceEdge (G:=G) e)
  have hz:N none=none:=rfl
  have h : Injective N:=Option.map_injective (source_unique e)
  conv_lhs=> rw [show spool _ _=_ from (show spool (after u) (sourceEdge e j)=_ from congr_fun (currents u e) j)]
  erw [show brush none (nameF N _) = _ from (work_spear N none (spool (jerk (u e.1) (u (e.1+step e.2))) j) h).symm]
  rw [←fluxStop]; exact DFunLike.congr_fun (stop_spear (sourceEdge e)) _
lemma after_freeze : (stopF 0).comp (train (spool (after u)))=RingHom.id _ := by
  let T:=(entryS G c);
  have h i : stopF 0 (spool (after u) i)=path i := by
    obtain ⟨⟨e,j⟩,rfl⟩:=T.surjective i
    rw [show spool _ _=_ from (show spool (after u) (T (e,j))=_ from congr_fun (currents u e) j)]
    have he := DFunLike.congr_fun (stop_spear (sourceEdge (G:=G) e)) (spool (jerk (u e.1) (u (e.1+step e.2))) j)
    rw [RingHom.comp_apply,RingHom.comp_apply, liveStop,name_var] at he; exact he
  apply serial_ext (by simp [stopF]) _ (by simp [stopF]); intro p
  induction p using MvPolynomial.induction_on with
  | C a=> change stopF 0 (train _ (realS a))= realS a; rw [train_real]; apply see_real
  | add p q a b=> simp only [map_add,a,b]
  | mul_X p j a=> simp only [map_mul, a,show C _=path j from rfl]; refine congrArg (RingHom.id _ (C p) * ·) (show _= path j from ?_); rw [RingHom.comp_apply,train_path,h]
lemma wrench {P:Ink (Woods G c)}(h:rollTest P P 1 0) :
     ∑ i:Edge (Site c), ∑ j:G.ColorIndex,nameF (sourceEdge i) (jet (electric (u i.1) (u (i.1+step i.2)) j)) * brush (sourceEdge i j) P=0 := by
  let E:= entryS G c; have hw := h (pin_ward u)
  have hX : train (spool (sole (G:=G) (c:=c)))=nameF some := by classical exact paint_spear _ _ fun _=>rfl
  have he:= congr_arg (fun k=> stopF 0 (brush none k)) hw
  rw [hX,freeze_brush,map_zero,reroutes,map_sum,←Equiv.sum_comp E,Fintype.sum_prod_type] at he
  rw [he]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
  rw [map_mul]; rw [←flux_live]; congr 1
  exact (DFunLike.congr_fun (after_freeze u) _).symm
end field
end YM.WilsonCoeffUV.Power
