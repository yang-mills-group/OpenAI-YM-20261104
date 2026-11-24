import YM.SchemeConversionRG11.FirstW.Trice.Life
/-! Translate hand-leg data at horizon6. No reduction on contacts. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function Filter MeasureTheory Lattice Pert Align Position Topology Maxwell Pert.Triangle Tensor Analysis Deck MvPolynomial
open scoped Topology ContDiff BigOperators Classical RealInnerProductSpace
variable {G:Gauge}{T: Itinerary} {n:Side}
abbrev Badge (G:Gauge):= (Fin 3)× G.ColorIndex
def penn (b:Badge G)(h:Bool): Dot G 6→ₗ[ℝ] ℝ := lineReader h b.1 b.2 ∘ₗ LinearMap.proj 0 ∘ₗ barks 6
def token (b:Badge G)(h:Bool) (i:Who G 6):= penn b h (Pi.single i 1)
lemma tick (b:Badge G)(h:Bool)(x : Dot G 6): ∑ i:Who G 6,token b h i*x i= penn b h x:= by
 have e:x=∑ i:Who G 6,x i • Pi.single i (1:ℝ):=funext fun i=>by simp [Finset.sum_apply,Pi.single_apply]
 nth_rw 2 [e]; simp only [map_sum,map_smul, smul_eq_mul]; apply Finset.sum_congr rfl; intro i _; unfold token; rw [mul_comm]
lemma occur (b:Badge G)(h:Bool)(i:Who G 6)(he:i.val.fst≠0): token b h i=0:= by
 unfold token penn barks bark; simp only [LinearMap.comp_apply, LinearMap.proj_apply,LinearMap.coe_mk,AddHom.coe_mk, dif_pos (by norm_num:0≤(6:ℕ)), Pi.single_apply]; rw [Finset.sum_eq_zero,map_zero]; intro j _; split <;> simp_all
 subst i; exact False.elim (he rfl)
lemma penn_eq (b:Badge G)(h:Bool)(x:Labels.Jet G): penn b h (salute 6 x)=lineReader h b.1 b.2 (x 0):= by rw [penn]; simp only [LinearMap.comp_apply,LinearMap.proj_apply,bark_again (d:=6) x 0 (by decide)]
def Glyph (b:Badge G)(h:Bool): Part G 6:= ∑ i:Who G 6,C (↑(token b h i):ℂ)*X i
lemma proved (b:Badge G)(h:Bool): uncap (Glyph b h)= fanLeg h b.1 b.2:= by
 apply Labels.eval_ext; intro x
 rw [←salute_read, Glyph,map_sum,read_fan,show fanReading _ _ (x 0) b.2=penn b h (salute 6 x) from (penn_eq ..).symm,← tick]; push_cast; refine Finset.sum_congr rfl fun _ _=>by simp [look]
lemma count_glyph (b:Badge G)(h:Bool)(i:Who G 6): D1 i (Glyph b h)=C (token b h i:ℂ):= by
 rw [D1,Glyph,map_sum,Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]; simp; intro j _ hj; rw [pderiv_C_mul,pderiv_X_of_ne hj,mul_zero]
def Stele (b:Badge G)(h:Bool)(v:Site n)(t:ℝ): FullT G n:= ∑ i:Who G 6, token b h i • river t i.val v
def Laurel (b:Badge G)(h:Bool)(T:Itinerary)(o:StepPath T): Sight T G:=fun i=> (T.gap i)⁻¹ • Stele b h (o i) (T.gap i)
lemma statue (b:Badge G)(h:Bool)(s o:StepPath T): passA T s (Laurel b h T o)= Laurel b h T (o-s):= funext fun i=>by simp only [passA,Laurel,Stele,map_smul,map_sum,river,consumes,Pi.sub_apply]
lemma stele_eq (b:Badge G)(h:Bool)(v:Site n)(t:ℝ): Stele b h v t=(t^2)⁻¹ • tbranch G n ((lineReader h b.1 b.2) ∘ₗ Bare.wideLinear G 0 1 v):= by
 have H (i:Who G 6): token b h i • river t i.val v=(t^2)⁻¹ • (token b h i • canal i.val v):= by
    by_cases h:i.val.1=0
    · simp only [river,mass,h,zero_add]; exact smul_comm ..
    simp only [occur b _ i h, zero_smul,smul_zero]
 simp only [Stele,H,canal,← Finset.smul_sum,← map_smul,← map_sum]; congr 2
 -- linear maps
 apply LinearMap.ext; intro x; simp only [LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.comp_apply,smul_eq_mul]; exact (tick b h (salute 6 (fun i=>Bare.wideLinear G i 1 v x))).trans (penn_eq b h (fun i=> Bare.wideLinear G i 1 v x))
lemma contact_l (b: Badge G)(h:Bool)(v:Site n)(t:ℝ)(A B: FullT G n): ∑ i:Who G 6,token b h i * echoLeg t v i.val A B=(t^2)⁻¹ * lineReader h b.1 b.2 (glint v 0 A B):= by
 let u (i:ℕ):= (t^(i+2))⁻¹ • glint v i A B; rw [show (t^2)⁻¹ * _=lineReader h b.1 b.2 (u 0) from by simp [u]]; rw [←penn_eq,← tick]; apply Finset.sum_congr rfl;intro i _; apply congrArg _; simp only [echoLeg,LinearMap.smul_apply,echoAt,LinearMap.compr₂_apply,salute, LinearMap.pi_apply,LinearMap.comp_apply,LinearMap.proj_apply,u,map_smul];rfl
lemma ShoreD (o:StepPath T)(b: Badge G)(h:Bool): Shore T o 3 (Laurel b h T o):= by
 let f (a:Who G 6):Sight T G:= fun i=> token b h a • SeaA T a.val o i
 have e: Laurel b h T o= ∑ i,f i:= funext fun i=>by simp only [Laurel,Stele,Finset.smul_sum,Finset.sum_apply]; apply Finset.sum_congr rfl; intro j _; exact smul_comm ..
 have hv (a) : Shore T o 3 (f a) := by
   by_cases he:a.val.fst=0
   · have he' : mass a.val+1=3:=by simp [mass,he]
     have hk:=shore_quote a.val o; rw [he'] at hk; constructor
     · intro s; exact (hk.1 s).scale _
     intro i j; rw [show rushC T (f a) i j= token b h a • rushC T (SeaA T a.val o) i j from funext fun k=>funext fun x=>by simp only [f,rushC,map_smul,Pi.smul_apply]; rw [smul_comm]]; exact (hk.2 i j).scale _
   have hh:f a=0:= funext fun i=> by simp [f,occur b _ a he]
   rw [hh]; exact ⟨fun _=> skyhut,fun i j=> by rw [show rushC T (0:Sight T G) i j=0 from funext fun i=>funext fun x=>by simp [rushC]]; exact skyhut⟩
 have H(u:Finset (Who G 6)): Shore T o 3 (∑ i∈u,f i):= by
    induction u using Finset.induction with
    | empty=> rw [Finset.sum_empty]; exact ⟨fun _=> skyhut,fun i j=>by rw [show rushC T (0:Sight T G) i j=0 from funext fun i=>funext fun x=>by simp [rushC]];exact skyhut⟩
    | insert i s hi ih=> rw [Finset.sum_insert hi]; let L:= ∑ i∈s,f i; have hh:=hv i; refine ⟨fun j=> (hh.1 j).roll (ih.1 j),fun a b=>?_⟩; rw [show rushC T (f i +L) a b=rushC T (f i) a b+rushC T L a b from funext fun k=>funext fun x=>by simp [rushC,smul_add]]; exact (hh.2 a b).roll (ih.2 a b)
 rw [e]; exact H _
end YM.RG11.FirstW
