import YM.FormalBulk08.Spigot.Torch
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Spigot
open Function Filter Lattice RG Laurent Bloch Exterior Wilson
open Reef Lava Gorge Mesa Shore Lotus Orb Wick Series Jets PowerSeries North Cork City Wine Flat Glide Bank Chapel Rift Kemp Dawn MeasureTheory
open Stationary hiding shine Rays
open scoped Topology ENNReal Matrix BigOperators Classical ContDiff
variable {I:Type*}{G:Gauge}{n:Side}{r t u e E D:ℕ}{A B C σ η:ℝ}
open Grail Precision Work.F03 Pose Tensor
open Planned.PrimaryIntegral295 Place Carrier
open scoped Matrix.Norms.Frobenius
variable {l j k:ℕ} {o:Loc G 1}{Q:Herald}{M N:List (Path D G)}{X Y:Anthem D G}
def blank (i:ℕ)(T:Anthem D G):= ∀ j < i,∀ p,T p j=0
lemma later (h: Seethe Q o M l u j E (l+E+1) η A Y)(g:Glyph o Y l E)(ht:j≤E)(hz:blank j Y): blank (j+1) (Y-binding M):= by
   intro t hT p; funext z; by_cases h:t=j
   swap
   · have he: binding M p t z=0:=by by_contra he; have hv:= (‹Seethe _ _ M _ _ _ _ _ _ _ _›.crisp t z p he).1; omega
     simp_rw [Pi.sub_apply,hz t (by omega) p,he]; simp
   subst t; by_cases hv:z<l+E+1
   · change Y p j z-binding M p j z=0; rw [‹Seethe _ _ M _ _ _ _ _ _ _ _›.lends z hv, sub_self]
   have ht' : binding M p j z=0:=by by_contra he; exact hv ((‹Seethe _ _ M _ _ _ _ _ _ _ _›.crisp j z p he).2 rfl)
   simp_rw [Pi.sub_apply,ht',show Y p j z=0 from Classical.byContradiction fun he=> by have hp:=g.summary.1 p j z he; unfold Yield at hp; omega,sub_zero];rfl
structure Litany (Q:Herald)(o:Loc G 1)(M:List (Path D G))(l u E j k:ℕ)(σ B:ℝ)(Y:Anthem D G):Prop extends Manus Q o M l u E σ B where
    build:M.length ≤ k*(l+E+1)
    fortune:∀ p∈ M,j≤p.grade∧p.grade < j+k
    agrees:∀ i<j+k,∀ p,Y p i=binding M p i
lemma incipit (H:Seethe Q o M l u j E (l+E+1) η A Y)(h:Litany Q o N l u E (j+1) k η B (Y-binding M)): Litany Q o (M++N) l u E j (k+1) η (A+B) Y:= by
   refine ⟨⟨fun p hp=> ?_,by rw [binding_fuse]; exact wood_plus H.bill h.bill⟩,?_,fun p hp=> ?_,fun i hi p=>?_⟩
   · rcases List.mem_append.mp hp with hp|hp; exact (H.origin _ hp).increase le_rfl (le_add_of_nonneg_right h.bill.height); exact (h.origin _ hp).increase le_rfl (le_add_of_nonneg_left H.bill.height)
   · rw [List.length_append,add_mul]; have hv:= H.heightp;have hx:= h.build;omega
   · rcases List.mem_append.mp hp with hp|hp
     · have he:=(H.sizes _ hp).1;omega
     have he:=h.fortune p hp; omega
   have he:=h.agrees i (by omega) p; rw [binding_fuse, Pi.add_apply,Pi.add_apply,←he]; simp
lemma lit_mono (h: Litany Q o M l u E j k σ A Y)(hs:η≤σ)(he:A≤ B): Litany Q o M l u E j k η B Y:= { h with toManus := h.toManus.mounted hs he }
lemma fork (Q:Herald)(o:Loc G 1)(l u E j k D:ℕ): ∀ σ:ℝ,0<σ → ∃ η C:ℝ,0<η ∧ 0≤C∧∀ (Y:Anthem D G) A,Woodsy o σ A E Y→Glyph o Y l E→ blank j Y→ j+k≤E+1→ ∃ M,Litany Q o M l u E j k η (A*C) Y:= by
    induction k generalizing j with
    | zero=> refine fun σ hs=> ⟨σ,0,hs,le_rfl,fun Y A F V h hv=>⟨[],⟨by simp,by rw [binding_nil]; exact wood_zero (by simp)⟩,by simp,by simp,fun i hi p=> (binding_nil) ▸ h i hi p⟩⟩
    | succ k ih=>
        intro σ hs; obtain ⟨η,C,h,hC,H⟩:= seethe (Classical.choice dill) Q o hs u D j E (l+E+1); let δ:=min σ η;have he:0<δ:=lt_min hs h; obtain ⟨ξ,K,t,hK,I⟩:= ih (j+1) δ he
        refine ⟨min η ξ,C+(1+C)*K,lt_min h t,by positivity,fun Y A F G' hv hp=>?_⟩
        have hw : j≤ E:= by omega
        obtain ⟨M,hM⟩:= H A Y l F G' hw hv; let S:=Y-binding M
        have hh:Woodsy o δ (A*(1+C)) E S:= by rw [mul_add,mul_one]; exact wood_le (wood_mono F (min_le_left ..) le_rfl) (wood_mono hM.bill (min_le_right ..) le_rfl)
        obtain ⟨N,hN⟩:= I S (A*(1+C)) hh (G'.sub (from_clef (hM.toManus.intend h) _)) (later hM G' hw hv) (by omega)
        rw [mul_add A,←mul_assoc A]; exact ⟨M++N,incipit (seethe_mono hM (min_le_left ..) le_rfl) (lit_mono hN (min_le_right ..) le_rfl)⟩
lemma ignited (Q:Herald)(o:Loc G 1)(l u E D:ℕ)(hs:0<σ): ∃ η C:ℝ,0<η ∧ 0≤C∧∀ (Y:Anthem D G) A,Woodsy o σ A E Y→Glyph o Y l E→∃ M,Litany Q o M l u E 0 (E+1) η (A*C) Y := by
    obtain ⟨η,C,h,H,hp⟩:= fork Q o l u E 0 (E+1) D σ hs; exact ⟨η,C,h,H,fun Y A he hv=> hp Y A he hv (fun _ hi=>by omega) (by omega)⟩
def terms (M:List (Path D G))(p:Studio D)(n:Side):= (M.map (fun q=>cradle q.grade q.cabin p n)).sum
lemma terms_fit (h:∀ q∈M, Merit Q o q l u E η A)(hs:0<η)(p:Studio D)(n):terms M p n=Kemp.banner l (binding M p) n:= by
    induction M with
    | nil=> simp [terms,Kemp.banner]; ext1;simp [coeff_mk]
    | cons a M ih=>
        have hk:=h a (List.mem_cons_self ..); have hm:∀ q∈ M, Merit Q o q l u E η A:= fun i hi=> h i (List.mem_cons_of_mem _ hi)
        have hv:= banner_add l ((struck a.cabin a.grade) p) (binding M p) n ((struck_linear o hk.income hs hk.meets).fare.summable _) (?_); swap
        · -- Clef for all petals: derive induction no cost
          suffices H:∀ (M:List (Path D G)),(∀ q∈M, Merit Q o q l u E η A)→ Clef o (binding M) l from (H M hm).fare.summable _
          intro M hh; induction M with
          | nil=> rw [binding_nil];exact Clef.base
          | cons a M ih=> rw [binding_cons]; let hp:= hh a (List.mem_cons_self ..); exact (struck_linear o hp.income hs hp.meets).add (ih fun i hi=> hh i (List.mem_cons_of_mem _ hi))
        rw [binding_cons,Pi.add_apply,hv,struck_banner o p hk.income hs hk.meets,← ih hm]; rfl
lemma lit_sum (h: Litany Q o M l u E 0 (E+1) η A Y)(hs:0<η)(p n): Through E (terms M p n) (Kemp.banner l (Y p) n):= by
    rw [terms_fit h.origin hs]; intro i hi; simp_rw [Kemp.banner,coeff_mk, h.agrees i (by omega)]
end YM.FormalBulk08.Spigot
