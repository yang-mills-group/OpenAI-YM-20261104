import YM.FVA2.TreeInput
/-!
# A real continuum-comparison stencil channel on the supplied Bare-MS basis

Here `NativeDictionary` can be used for *any* giving of the physical section,
with explicit Wilson `Cover` formulas and lower field ranks. We exhibit one
(plaquette curvature, covariant `edgeSense` differences, homogeneous slots and
full compact-color lifts) by strengthening `liftP`. `stamp` is not tuned with
the volume limit; already pins exactly by placement. Keep symmetric-axis demands
on the *dictionary* separate---this existence gives the signed cover action on
links, but not a signed/group-blind choice of basis lift coefficients, unit
normalization, or identification with the desired `Source.Hol` jet convention.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Source
open Filter Topology Set PowerSeries Function
open PertExtension PertExtension.Series PertExtension.Series.Radial
open FormalOPE.RG10 FormalOPE.RG10.MultiGauge Trans Wilson
open Lattice MS MS.Native MS.Native.Chart MS.Native.Wilsonian MS.Native.Studio MS.Native.Orient MS.Native.Sew MS.Lifting MS.Local MS.Landau MS.Menus MS.Koszul MS.Book MS.Cylinder MS.Plane MS.Cylinder.Lab MS.Cylinder.Taylor
open MS.Tone MS.Color MS.Orbit MS.Puff MS.Puff.Engine Based MeasureTheory
open scoped Topology Classical ContDiff Matrix.Norms.Frobenius
local notation "W"=>Lattice.Cover
variable {G:Gauge} {n d:ℕ}
abbrev Weights (G:Gauge) := Eye G Lattice.Cover

-- Full mark addresses relative to arbitrary base. Before spatial scaling (separate).
def put (f: Weights G) {n:Side} (x:Site n) : Wilson.Observable G n := f ∘ Lattice.expandAt x

lemma invariant_from {f : Weights G} (h:OpenGauge idRail f): GaugeInvariant f:= fun g U=> by rw [show Lattice.gauge g U= siteGauge idRail (fun x=> (g x)⁻¹) U from funext fun x=>by simp [Lattice.gauge, siteGauge, idRail,endRail]]; exact h ..
lemma putInvariant {n:Side} (x:Site n) {f:Weights G}(h:GaugeInvariant f): GaugeInvariant (put f x):= fun v U=> by unfold put; rw [Function.comp_apply, expandAt_gauge,h]; rfl
lemma put_cont {n:Side}(x:Site n){f:Weights G}(hf:Continuous f): Continuous (put f x):= hf.comp (show Continuous (expandAt (K:=G.El) x) from (by unfold expandAt; fun_prop))

def Foot {P A:Type} (F:(P→A)→ℝ) : Prop:= ∃ E:Finset P, ∀ u v:P→A,Set.EqOn u v ↑E→F u=F v
abbrev OpenSt (F : Weights G) := Foot F
lemma openLocal {f: Weights G}(h : OpenSt f): ∃ A: Finset W, Lattice.LocalOn ↑A f:= by
    obtain ⟨B,hb⟩:=h; let P:=B.image Prod.fst; let R:= B.image (fun i:Edge W=> i.1+step i.2); refine ⟨ P ∪ R,fun u v h=> hb u v (fun i hi=> h i ?_ ?_)⟩; apply Finset.mem_union_left; exact Finset.mem_image_of_mem _ hi; apply Finset.mem_union_right; exact Finset.mem_image_of_mem _ hi

structure Brand (F:Dot G Lattice.Cover) (a:Weights G) : Prop where
   go : GaugeInvariant a
   openSize : OpenSt a
   clean : Continuous a
   pays (n:Side)(x:Site n) : Reads (Lab.Shift x (shown n F)) (put a x)

lemma pinArt {F:Dot G W} {n:Side}(x:Site n){f:Weights G}(h:Brand F f): Based.place G n x F=Native.reads ((put f x) ∘ nation):= (h.pays n x).home
lemma Badd {F H:Dot G W}{f g: Weights G}(hf:Brand F f)(hg:Brand H g): Brand (F+H) (f+g):= by
   refine ⟨fun u v=> congr_arg₂ (·+·) (hf.go u v) (hg.go u v),?_ ,hf.clean.add hg.clean,fun n x=>?_⟩
   · obtain ⟨B,hb⟩:= hf.openSize; obtain ⟨T,ht⟩:=hg.openSize; exact ⟨B ∪ T,fun u v hv=> congr_arg₂ (·+·) (hb u v (hv.mono fun i hi=> Finset.mem_union_left _ hi)) (ht u v (hv.mono fun i hi=> Finset.mem_union_right _ hi))⟩
   obtain hx:= hf.pays n x; obtain hp:=hg.pays n x; rw [map_add,map_add]; refine ⟨ContDiffAt.add hx.born hp.born,?_⟩; rw [Submodule.coe_add,hx.home,hp.home]; exact (ink_add _ hx.born hp.born).symm
lemma Bcash {F:Dot G W}{f:Weights G}(h:Brand F f) (u:ℝ) : Brand ((u:ℂ) • F) (u • f):= by
   refine ⟨fun x v=> congr_arg (u • ·) (h.go x v),?_, h.clean.const_smul u,fun n x=>?_⟩; obtain ⟨B,hb⟩:=h.openSize; exact ⟨B,fun x y hp=> congr_arg (u • ·) (hb _ _ hp)⟩
   rw [map_smul,map_smul]; exact (h.pays n x).cash u
lemma Bzero : Brand (0:Dot G W) 0:= by
    refine ⟨fun _ _=>rfl,⟨ ∅, fun _ _ _=>rfl⟩,continuous_const,fun n x=>?_⟩; rw [map_zero,map_zero]; exact ⟨ contDiffAt_const,(Taylor.ink_zero _).symm⟩

variable {P A X:Type} (F:Dot G Lattice.Cover)(v:ℕ)
-- strengthen from explicit on-saddle pull.
private lemma forallP {F:(P→A)→X}: (∃ E: Finset P,∀ u v:P→A, Set.EqOn u v ↑E→ F u=F v)→∀ f:X→ℝ, Foot (f∘F):= by rintro ⟨E,h⟩ f; exact ⟨ E,fun u v he=> congr_arg f (h _ _ he)⟩
private lemma limitPP (f g:(P→A)→ℝ) (hf:Foot f)(hg:Foot g)(C:ℝ→ℝ→ℝ): Foot (fun x=>C (f x) (g x)):= by
    obtain ⟨B,hb⟩:=hf; obtain ⟨T,ht⟩:=hg; exact ⟨B ∪ T,fun u v hv=> congr_arg₂ C (hb u v (hv.mono fun i hi=> Finset.mem_union_left _ hi)) (ht u v (hv.mono fun i hi=> Finset.mem_union_right _ hi))⟩
private lemma limit_sum {I:Type}(s:Finset I)(f:I→(P→A)→ℝ)(h:∀ i∈s,Foot (f i)): Foot (∑ i∈s,f i) := by
    induction s using Finset.induction_on with| empty=> rw [Finset.sum_empty]; exact ⟨ ∅, fun _ _ _=>rfl⟩| insert i s hi ih=> rw [Finset.sum_insert hi]; exact limitPP _ _ (h _ (by simp)) (ih fun _ h'=>h _ (Finset.mem_insert_of_mem h')) (·+·)
private lemma limit_mul {I:Type}(s:Finset I)(f:I→(P→A)→ℝ)(h:∀ i∈s,Foot (f i)): Foot (fun x=>∏ i∈s,f i x) := by
    rw [ funext (fun x=> (Finset.prod_apply x s f).symm) ]; induction s using Finset.induction_on with| empty=> rw [Finset.prod_empty]; exact ⟨∅,fun _ _ _=>rfl⟩| insert i s hi ih=> rw [Finset.prod_insert hi]; exact limitPP _ _ (h _ (by simp)) (ih fun _ h'=>h _ (Finset.mem_insert_of_mem h')) (·*·)
private lemma limit_cash (f:(P→A)→ℝ)(h:Foot f)(u:ℝ): Foot (u • f):= limitPP _ _ h h (fun a _=>u*a)
section metrics
variable [AddCommGroup P] (r:Native.Chart.Rail P)
private lemma sensed (k:PlaqAxes)(l:List Axis)(x:P): ∃ E:Finset (Edge P),∀ u v: Rig G P,Set.EqOn u v ↑E→ edgeSense r k l x u=edgeSense r k l x v := by
   induction l generalizing x with
   | nil=> exact ⟨Finset.univ.image (loadC r (x,k)),fun u v h=> congr_arg bolt₀ (funext (fun i=> h (Finset.mem_image_of_mem _ (Finset.mem_univ i))))⟩
   | cons i l ih=>
        obtain ⟨B,hb⟩:=ih (x+r i); obtain ⟨R,hr⟩:=ih x; refine ⟨insert (x,i) (B∪R),fun u v h=> congr_arg₂ (·-·) (congr_arg₂ (fun a b=> G.adjoint a b) (h (by simp)) (hb u v (h.mono fun _ hi=> Finset.mem_insert_of_mem (Finset.mem_union_left _ hi)))) (hr u v (h.mono fun _ hi=> Finset.mem_insert_of_mem (Finset.mem_union_right _ hi)))⟩
private lemma rope_open (k:Plaq)(x:P) (i:G.ColorIndex): Foot (ropeF r k x i):= by unfold ropeF; split_ifs; exact forallP (sensed ..) _; exact forallP (sensed r _ _ x) (fun y=>-(α i y)); exact ⟨∅,fun _ _ _=>rfl⟩
lemma open_r (v:ℕ)(x:P)(f:Fin v→ Plaq)(u: Grid G v): Foot (realF r v x f u):= limit_sum Finset.univ _ (fun _ _=> limit_cash _ (limit_mul Finset.univ _ (fun j _=>rope_open r (f j) _ _)) _)
private lemma optical_cont : Continuous (fun x:G.El × G.Color=>G.adjoint x.1 x.2) := G.projectColor.continuous_of_finiteDimensional.comp ((((G.continuous_mat.comp continuous_fst).mul (G.colorMat.continuous_of_finiteDimensional.comp continuous_snd))).mul (continuous_star.comp (G.continuous_mat.comp continuous_fst)))
lemma sensed_cont (k:PlaqAxes)(l:List Axis)(x:P): Continuous (edgeSense (G:=G) r k l x):= by
   induction l generalizing x with| nil=> exact G.continuous_curvature.comp (f:=fun u=>atCart (u ∘ loadC r (x,k))) (by unfold atCart; fun_prop)| cons i l ih=> exact (Continuous.comp (g:=fun x:G.El×G.Color=>G.adjoint x.1 x.2) (f:=fun u: Rig G P=> (u (x,i), edgeSense r k l (x+r i) u)) optical_cont ((continuous_apply (x,i)).prodMk (ih _))).sub (ih x)
lemma rope_cont (k:Plaq)(x:P)(i:G.ColorIndex): Continuous (ropeF r k x i):= by unfold ropeF; split_ifs; exact Continuous.comp (α i).continuous (sensed_cont ..); exact (Continuous.comp (α i).continuous (sensed_cont ..)).neg; exact continuous_const
lemma real_cont (v:ℕ)(x:P)(f:Fin v→ Plaq)(u: Grid G v): Continuous (realF r v x f u):= by unfold realF; rw [show ∑ k:Grid G v,Lifting.group G k u • monF r v x f k=fun a=>∑ k:Grid G v,(Lifting.group G k u • monF r v x f k) a from funext (fun a=> Finset.sum_apply ..)]; exact continuous_finsetSum Finset.univ (fun k _=> (continuous_finsetProd Finset.univ (fun i _=> rope_cont r (f i) x (k i))).const_smul _)
end metrics

private lemma edge_exp {n:Side}(x:Site n)(k:PlaqAxes)(l:List Axis)(a:W)(u:Rig G (Site n)):
    edgeSense idRail k l a (expandAt x u)= edgeSense (drive n) k l (wrap n a+x) u:= by
   induction l generalizing a with
   | nil=> apply congr_arg (G.curvature ∘ atCart); ext1 i; fin_cases i <;> simp [loadC, expandAt,Native.Orient.idRail,drive,add_right_comm]
   | cons i l ih=> simp only [edgeSense,expandAt,ih]; rw [Native.Orient.atlas,add_right_comm]; -- simp got expandAt recursive expression under ih?
lemma rope_at {n:Side}(x:Site n)(k:Plaq)(i:G.ColorIndex)(u:Rig G (Site n)):
    ropeF idRail k 0 i (expandAt x u)= ropeF (drive n) k x i u:= by unfold ropeF; split_ifs <;> simp [Function.comp_apply,edge_exp]
lemma real_expand (v:ℕ){n:Side}(x:Site n)(f:Fin v→ Plaq)(u: Grid G v): put (realF idRail v (0:W) f u) x=realF (drive n) v x f u:= by ext1 a; simp only [put,Function.comp_apply,realF,Finset.sum_apply, Pi.smul_apply, monF, rope_at]

lemma realB (f:Fin v→ Plaq)(u: Grid G v): Brand (markP v f u) (realF idRail v (0:W) f u) where
   go := invariant_from (sings idRail v _ f u)
   openSize := open_r ..
   clean := real_cont ..
   pays n x:= by rw [ markP, shown, sings_go (g:=drive n) _ _ (atlas n), map_zero,Lab.Shift,sings_go (g:=drive n) _ _ (fun i j=>(add_assoc ..).symm), add_zero, real_expand ]; exact real_R (drive n) v x f u

-- concrete Dictionary. Keep levels incl ordinal >0; pins all stencils.
structure NativeDictionary {G:Gauge}(B:Local.Physical.Deck G) where
   book: LitBook B
   formula (u v:ℕ) (i:B.BIndex u v) : Weights G
   stamps (u v:ℕ) (i:B.BIndex u v): Brand (book.stamp u v i) (formula u v i)
private lemma all {v:ℤ}{n:ℕ}{D:Landau.Detect.Law G}(h:D∈ Local.Physical.Allowed G v n): ∃ (F:Dot G W) (f:Weights G), Aura F n ∧ MS.Lifting.Fits F D n v false ∧ Brand F f:= by
   refine Submodule.span_induction (p:=fun D _=>∃ (F:Dot G W) (f:Weights G), Aura F n∧Fits F D n v false∧ Brand F f) ?_ ⟨ 0,0,Aura.zero _ _,Fits.zero _,Bzero⟩ ?_ ?_ (syntaxK h)
   · rintro x ⟨u,w,rfl,he,rfl⟩; exact ⟨_,_,real_A ..,mark_F n u w, realB n u w⟩
   · rintro d e hd he ⟨p,q,h,hg,H⟩ ⟨f,g,k,h',K⟩; exact ⟨p+f,q+g,h.add k,hg.add h',Badd H K⟩
   rintro x u hu ⟨p,f,h,ht,H⟩; exact ⟨ (x:ℂ) • p,x • f, h.scalar x,ht.smul (x:ℂ),Bcash H x⟩

theorem diction (B : Local.Physical.Deck G) : Nonempty (NativeDictionary B):= by
   choose f a hf hF hy using fun (u v:ℕ) (i:B.BIndex u v) => all (B.le (B.form u v i)); exact ⟨⟨⟨ f,hf,hF ⟩, a,hy⟩⟩
end YM.FVA2.Source
