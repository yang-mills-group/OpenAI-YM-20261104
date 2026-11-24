import YM.FormalBulk08.Vale.Acre
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Vale
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Work.F03 Work.F05 Work.F08 PowerSeries
open Quire Sable Aster Dawn Wine Roof Orb Tundra Sierra Wick Series
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{X I J V:Type*}{r n m i j t d l E:ℕ}{σ A B C:ℝ}
lemma sieve_terms (T:I→Tile (Biglot V) r)(s:Finset I)(h:∀ i∈s,Summable (T i)) (n: Side): Summable (∑ i∈s,T i) ∧ sieve n (∑ i∈s,T i)=∑ i∈s,sieve n (T i):= by
    induction s using Finset.induction with
    | empty=>simp;exact summable_zero
    | @insert i S he ih=> obtain ⟨U,H⟩:=ih (fun j hj=> h j (Finset.mem_insert_of_mem hj)); obtain P:=h i (Finset.mem_insert_self ..); rw [Finset.sum_insert he,Finset.sum_insert he, (sieve_sub_add _ P U).1,H];exact ⟨P.add U,rfl⟩
lemma sieve_length (p:Side)(T:Tile (Biglot V) r)(h:r=m): sieve p (lengthen h T)=lengthen h (sieve p T):= by cases h;rfl
lemma sieve_grain (n:Side)(p:Tile (Biglot V) r)(s:Equiv.Perm (Fin r)): sieve n (fun v=>p (v∘s))=fun v=>sieve n p (v∘s):= by
    funext v; rw [sieve_i,sieve_i]; let t:=Equiv.arrowCongr s.symm (Equiv.refl (Biglot V)); rw [← Equiv.tsum_eq t (fun u=> if Lotus.drip n ∘ u=v ∘ s then p u else 0)]; refine tsum_congr fun a=>?_ ; by_cases ha:Lotus.drip n ∘ a=v
    · rw [if_pos ha, if_pos]; rfl
      change (Lotus.drip n ∘ a) ∘ s=v ∘ s; rw [ha]
    rw [if_neg ha,if_neg]; exact fun hh=> ha (funext fun i=>by
       have he:= congr_fun hh (s.symm i)
       change (Lotus.drip n ∘ a) (s (s.symm i))= v (s (s.symm i)) at he; rwa [s.apply_symm_apply] at he)
lemma sieve_sandy (n:Side)(p:Tile (Biglot V) r)(hp:Summable p): sieve n (sand p)=sand (sieve n p):= by
   let e:=Equiv.Perm (Fin r)
   let H(i: e):= Equiv.arrowCongr i.symm (Equiv.refl (Biglot V))
   let A:= fun s:e=>p ∘ H s
   rw [show sand p=(Fintype.card (Equiv.Perm (Fin r)):ℝ)⁻¹ • ∑ s,A s from funext (fun v=>by simp [sand,Finset.sum_apply,A,div_eq_inv_mul,H]; rfl),sieve_smul,(sieve_terms A _ (fun i _=>(H i).summable_iff.mpr hp) _).2];dsimp only [e]; funext v; rw [Pi.smul_apply,Finset.sum_apply,sand,div_eq_inv_mul]; apply congr_arg; apply Finset.sum_congr rfl; intro s _; exact congr_fun (sieve_grain n p s) v
lemma clasp_sieves (T:Tile (Biglot I) r)(S:Tile (Biglot I) m)(h:Summable (clutch T S))(p:Side): sieve p (clutch T S)=clutch (sieve p T) (sieve p S):=by
    ext1 V; let e:=castle (Tor p I) r m; obtain ⟨⟨u,v⟩,rfl⟩:= e.surjective V
    rw [sieve_i, show clutch (sieve p T) (sieve p S) (e (u,v))=sieve p T u * sieve p S v by simp [clutch,e,castle,Function.comp_def],sieve_i,sieve_i]
    let a:=castle (Biglot I) r m
    let f(i):=if Lotus.drip p ∘ i=e (u,v) then clutch T S i else 0
    have hx: Summable f:=(h.indicator (setOf (fun i : chain (Biglot I) (r+m)=> Lotus.drip p ∘ i=e (u,v)))).congr (fun i=>by by_cases h: Lotus.drip p ∘ i=e (u,v) <;> simp [f,h])
    change (∑' i,f i)= _;rw [←Equiv.tsum_eq a f];change (∑' i,(f∘a) i)=_; rw [(a.summable_iff.mpr hx).tsum_prod]; rw [←tsum_mul_right]; apply tsum_congr; intro X; rw [←tsum_mul_left]; apply tsum_congr; intro Y; have he : Lotus.drip p ∘ (a (X,Y))=e (Lotus.drip p ∘ X,Lotus.drip p ∘ Y):= funext fun i=> by cases i using Fin.addCases <;> simp [e,a,castle]
    dsimp only [f,Function.comp_apply]; rw [he]; simp only [Equiv.apply_eq_iff_eq,Prod.mk.injEq]; by_cases h:Lotus.drip p ∘ X = u <;> by_cases q:Lotus.drip p ∘ Y=v <;> simp only [h,q,and_self,false_and,and_false,↓reduceIte] <;> simp [clutch,castle,a,Function.comp_def]
lemma gelatine {x:Biglot V}{T:Lava.Veil (Biglot V)}{S:Lava.Veil (Biglot V)}(h:∀ i,∃ A, Knoxville (fame _) σ x (T i) A)(he:∀ i,∃ A, Knoxville (fame _) σ x (S i) A)(hs:0≤σ)(p:Side)(r:ℕ): Summable (diplex T S r) ∧ sieve p (diplex T S r)=diplex (fun r=>sieve p (T r)) (fun r=>sieve p (S r)) r:= by
    choose B h using h; choose C he using he
    let A:= (Finset.HasAntidiagonal.antidiagonal r).attach; let Z (i:↥(Finset.HasAntidiagonal.antidiagonal r)):=clutch (T i.val.1) (S i.val.2)
    let f(i:↥(Finset.HasAntidiagonal.antidiagonal r)):=lengthen (Finset.HasAntidiagonal.mem_antidiagonal.mp i.property) (sand (Z i)); have H (i:↥(Finset.HasAntidiagonal.antidiagonal r)):=clasp_cash (h i.val.1) (he i.val.2) hs
    obtain ⟨hs',ht⟩:= sieve_terms f A (fun i _=> (penn_total (((H i).polish).rename (Finset.HasAntidiagonal.mem_antidiagonal.mp i.property)) hs).of_norm) p
    refine ⟨hs', ht.trans (Finset.sum_congr rfl (fun i _=>?_))⟩
    rw [show sieve p (f i)=_ from sieve_length _ _ _,sieve_sandy p (Z i) (penn_total (H i) hs|>.of_norm)]; apply congr_arg; apply congr_arg; exact clasp_sieves _ _ (penn_total (H i) hs |>.of_norm) p
lemma consumes (a:hue G){T S : Pot G}(h:Ritual T l)(hp:Ritual S r)(n:Side):
    Kemp.banner (l+r) (duplexB T S) n= Kemp.banner l T n*Kemp.banner r S n:= by
   apply banner_eq; funext i j; rw [badge (duplexB T S) (dup_grades h.young hp.young) (spelled _ _) le_rfl, product_read]
   let x:edgeL G:=(0,Exterior.coord 0,a); obtain ⟨s,hs,H⟩:=pledge h x i; obtain ⟨u,hu,Q⟩:= pledge hp x i
   have hx(z)(hz:z∈Finset.HasAntidiagonal.antidiagonal i):= by
       have hZ: z.1 ≤ i∧ z.2 ≤ i:= by rw [Finset.HasAntidiagonal.mem_antidiagonal] at hz; omega
       exact gelatine (T:=T z.1) (S:=S z.2) (fun j=> let h:=(H z.1 j hZ.1).choose_spec;⟨_,penn_shrink h (min_le_left ..)⟩) (fun j=>let h:= (Q z.2 j hZ.2).choose_spec;⟨_,penn_shrink h (min_le_right ..)⟩) (lt_min hs hu).le n j
   unfold duplexB; rw [(sieve_terms _ _ (fun i hi=>(hx i hi).1) _).2]; apply Finset.sum_congr rfl; intro p u; rw [(hx p u).2]; congr! 2 with j
   all_goals first| exact (badge T h.young h.committees le_rfl ..).symm| exact (badge S hp.young hp.committees le_rfl ..).symm
end YM.FormalBulk08.Vale
