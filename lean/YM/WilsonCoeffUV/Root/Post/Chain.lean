import YM.WilsonCoeffUV.Root.Post.Imprint
/-!
# Leveraging Wreathe through matrix packing. Single map linear. Equivariance. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {n c:Side}{U V E:Type*}{r h D l j e k a m:ℕ} {G:Gauge}{F:Labels.Frame G h}{s t t' A X B C δ:ℝ}
def paintC (F:Labels.Frame G h)(s:Signed): Coil F:= Matrix.of fun i j=> PowerSeries.C (blueIn F s i j)
lemma paintCap (F:Labels.Frame G h)(s:Signed): trample F (paintC F s):=by
   intro k i j h; by_cases hu : k=0
   · subst k; unfold lineS paintC; simp only [Matrix.of_apply, coeff_zero_eq_constantCoeff_apply,constantCoeff_C]; by_contra h'; have he: valence F i=valence F j:= (Prod.mk.inj (mien F s i j h').1).2; omega
   exact coeff_C_of_ne_zero hu
lemma canvasF [AddCommGroup V][Module ℝ V](F: Labels.Frame G h)(s:Signed)(P:BookC F V E)(i): impose P (paintC F s) i= ∑ j,blueIn F s j i • P j:=by unfold impose; simp_rw [paintC,Matrix.of_apply,purePayment]
lemma blank (F:Labels.Frame G h): paintC F 1=1:=by
   have he (i:Embroider.Spiral h): Embroider.spindle 1 i=i:=Subtype.ext (by unfold spindle; simp)
   have hh i: hue 1 i=1:=by obtain ⟨j,h⟩:= Embroider.present i; rw [← h,scarlet]; simp [dip]
   have ht i j : bleached F (1:Signed).ortho i j=if j=i then 1 else 0:=by unfold bleached; rw [show (1:Signed).ortho =1 from map_one Signed.inclusionO, Frame.act_one]; by_cases h:i=j; simp [h]; simp [h,Ne.symm h]
   ext1 i j; unfold paintC blueIn; rw [Matrix.of_apply,he,hh,ht]; by_cases H : i=j; · subst j; simp
   rw [Matrix.one_apply_ne H]; split; next h=>
       rw [if_neg (show ¬ sheet F j=sheet F i from fun e=>H (Subtype.ext (Prod.ext e.symm h.symm)))]; simp
   next v => simp
lemma shell_mon {X:Pal (Vote D) U}(h:shellK l X)(p:l≤ k): shellK k X:= fun i r v=>h _ _ (by omega)
abbrev PatchPanel (F:Frame G h) D:= (n:Side) → BookC F (Vote D) (Woods G n)
structure Chain (F:Frame G h)(X:PatchPanel F D)(Y:Thesis F D): Prop where
   solo i: Solo (valence F i) (fun n=>X n i) (Y i)
   spirit s n i: Wreathe (X n i) (impose (X n) (paintC F s) i) s
lemma anzas {V:Type*}[NormedAddCommGroup V][NormedSpace ℝ V]{P:U→ raw E V r}{Q:U→ Ten V (Cloth E) r}(S:Finset U)(h:∀ i∈S,Bends 0 (P i) (Q i)):Bends 0 (fun n=>∑ i∈S,P i n) (∑ i∈S,Q i):= (Soil.Bends.sum h).congr (Eventually.of_forall fun _ => Finset.sum_apply ..)
lemma Solo.affixing {A}(V:PatchPanel F D)(X: Thesis F D)(p:∀ i,Solo (valence F i) (fun n=> V n i) (X i))(v:trample F A)(i:Alma F): Solo (valence F i) (fun n=> impose (V n) A i) (impose X A i):=by
   refine ⟨?_,fun _=>impose_billed A v _ (fun i=>(p i).launch _) i,fun n r=> impose_smooth A _ (fun i r=>(p i).evenS _ _) i r,?_⟩
   · intro i' r; simp_rw [impose,Finset.sum_apply]; apply anzas (P:=fun j n=>affix (A j i) (V n j) i' r); intro j _
     simp_rw [affix, Finset.sum_apply]; exact anzas (P:=fun x n=>(coeff x.1 (A j i))• V n j x.2 r) (Finset.antidiagonal i') fun _ _=> Soil.Bends.μ ((p j).shore ..) _
   intro n; unfold impose; have hv j (_:j∈Finset.univ): shellK h (affix (A j i) (V n j)):= shell_mon (affix_shell (A j i) _ ((p j).launch _)) (valence_cap ..)
   exact pulseJ _ (fun j _=> incense (A j i) _ _ 1 ((p j).launch _) ((p j).launch _) ((p j).oneS _)) hv hv
lemma Chain.pierce {A: Coil F}(V: PatchPanel F D)(X: Thesis F D)(p:Chain F V X)(t:trample F A)(v:∀ s:Signed, paintC F s*A=A*paintC F s): Chain F (fun n=> impose (V n) A) (impose X A):=by
    refine ⟨fun i=> Solo.affixing V X p.solo t _,fun s n i=>?_⟩
    rw [imposition,←v,← imposition];
    let K:= paintC F s; let T:= impose (V n) K
    have hp j: shellK h (V n j):= shell_mon ((p.solo j).launch n) (valence_cap ..)
    have ht j: shellK h (T j):= shell_mon ((Solo.affixing V X p.solo (paintCap F s) j).launch n) (valence_cap ..)
    exact pulseJ (Finset.univ (α:= Alma F)) (fun j _=>incense (A j i) _ (T j) s (hp j) (ht j) (p.spirit s n j)) (fun j _=> affix_shell _ _ (hp j)) (fun j _=> affix_shell _ _ (ht j))
lemma Chain.commutes (V:PatchPanel F D)(X: Thesis F D)(p:Chain F V X)(H:Hol G)(q:h<D)(s:Signed): paintC F s *prismata F X = prismata F X*paintC F s:=by
    let T:= paintC F s; let P:= prismata F X
    have hx i: Solo (valence F i) (fun n=> impose (V n) T i) (impose X T i) := Solo.affixing V X p.solo (paintCap F s) _
    refine Eq.symm (extortion (A:=P*T) fun e i j=> ?_)
    rw [← prismata_bind F X (fun i=>solo_stretch (p.solo i)), coined, glean_spin F H s q i (X j) (impose X T j) ?_]; swap
    · intro i _ r _; obtain ⟨a,b,ha,hb⟩:= solo_stretch (p.solo j) i r; obtain ⟨t,h,ht,v⟩:= solo_stretch (hx j) i r; exact ⟨solo_mercy (p.solo j) (hx j) _ (fun n=>p.spirit s n j) i r,solo_mural (p.solo j) _ _,solo_mural (hx j) _ _, _,_,_,_,ha,ht,hb,v⟩
    change _=coeff e ((paintC F s*P) i j); rw [Matrix.mul_apply,map_sum]; apply Finset.sum_congr rfl; intro v _; rw [paintC,Matrix.of_apply,coeff_C_mul]; exact congr_arg ((blueIn F s i v)*·) (coined X e v j).symm
end YM.WilsonCoeffUV.Cosmos
