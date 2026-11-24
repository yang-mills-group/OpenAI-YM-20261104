import YM.OPE.Compatible.Emu.Basin
/-! # Boundary gallery. Routes on cover never cross the patch. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Merchant
open Function Filter Lattice Laurent Wilson Matrix RG Finset
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {x z y:Cover}{i a:Axis}{r b k:ℕ}
structure StepsL (x y:Cover)(A:Finset Cover)(k:ℕ):Prop where
      sees:∃ w:Walk,stop x w=y∧w.length ≤ k∧∀ z∈ Lattice.visits x w,z∈A
namespace StepsL
variable {B C:Finset Cover}{H:StepsL x y B r}
lemma lend (H:StepsL x y B r)(hv:B⊆C)(hx:r ≤ b): StepsL x y C b:=by obtain ⟨w,hw,H,h⟩:=H.sees; exact ⟨w,hw,H.trans hx,fun i hi=> hv (h i hi)⟩
lemma identity (h:x∈B):StepsL x x B 0:= ⟨[],rfl,le_rfl,by simp [visits,h]⟩
lemma stride {a:Step} (h:x∈B)(hy:x+a.vec∈B):StepsL x (x+a.vec) B 1:= ⟨[a],rfl,le_rfl,by simp [visits,h,hy]⟩ -- simp
lemma both (H:StepsL x y B r)(h:StepsL y z B b):StepsL x z B (r+b):=by
      obtain ⟨s,hs,H,hX⟩:=H.sees; obtain ⟨t,ht,h,hY⟩:=h.sees; subst y; refine ⟨s++t,by rw [stop_append,ht],by rw[List.length_append];omega,?_⟩; intro a ha; exact (joins ha).elim (fun hi=> hX a hi) (fun hi=>hY a hi)
where joins {x y:Cover}{s t:Walk} (hx:y∈visits x (s++t)): y∈visits x s ∨ y∈visits (stop x s) t:=by
        induction s generalizing x t <;> simp_all [visits,stop,or_assoc] ; grind
noncomputable abbrev bed (B:Finset Cover)(a:Axis)(f:ℤ):=B.filter (fun x=>x a=f)
-- straight corridor lemma.Strides ∧ separate with another i unchanged
lemma adjust {n:ℕ}(i:Axis)(h:x∈ Lattice.box r)(g:z∈Lattice.box r)(ha:∀ j,j≠i→x j=z j)(hx: (z i-x i).natAbs ≤ n) (a:Axis)(he:a≠i): StepsL x z (bed (Lattice.box r) a (x a)) n:=by
       induction n generalizing x z with
       | zero=>have hh: x=z:= funext fun j=>by by_cases hy:j=i; subst j; omega; exact ha j hy
               subst z; exact identity (mem_filter.mpr ⟨h,rfl⟩)
       | succ n ih=>
          rcases lt_trichotomy (x i) (z i) with hh|hh|hh
          · let y:=x+ (posDir i).vec; have hi:y i=x i+1:=(by simp [y]); have hp(j)(hv:j≠i): y j=x j:=(by simp [y,hv]); have hy:y∈Lattice.box r:=(by
                obtain ⟨hV,hH⟩:=box_test.mp h; obtain ⟨gV,gH⟩:=box_test.mp g; rw [box_test]; refine ⟨?_,?_⟩<;>intro j<;> specialize hV j<;> specialize hH j<;>by_cases hz:j=i<;> first| (subst j; specialize gH i; omega)| (rw [hp _ hz]; omega))
            let Q:= ih hy g (fun a ha'=>(hp a ha').trans (ha a ha')) (show (z i-y i).natAbs ≤ n from by omega); rw[hp a he] at Q; simpa only[add_comm 1] using both (stride (mem_filter.mpr ⟨h,rfl⟩ : x∈bed _ a _) (mem_filter.mpr ⟨hy,hp _ he⟩) (a:=posDir i)) Q
          · have hz:x=z:=funext fun j=> if ht:j=i then ht ▸ hh else ha j ht; subst z; exact lend (identity (mem_filter.mpr ⟨h,rfl⟩: x∈bed _ a _)) (by rfl) (Nat.zero_le _)
          let y:=x+ (negDir i).vec; have hi:y i=x i-1:=(by simp [y, sub_eq_add_neg]); have hp(j)(hv:j≠i): y j=x j:=(by simp [y,hv]); have hy:y∈Lattice.box r:=(by
                obtain ⟨hV,hH⟩:=box_test.mp h; obtain ⟨gV,gH⟩:=box_test.mp g; rw [box_test]; refine ⟨?_,?_⟩<;>intro j<;> specialize hV j<;> specialize hH j<;>by_cases hz:j=i<;> first | (subst j; specialize gV i;omega) | (rw [hp _ hz]; omega))
          let Q:= ih hy g (fun a ha'=>(hp a ha').trans (ha a ha')) (show (z i-y i).natAbs ≤ n from by omega); rw[hp a he] at Q; simpa only[add_comm 1] using both (stride (mem_filter.mpr ⟨h,rfl⟩ : x∈bed _ a _) (mem_filter.mpr ⟨hy,hp _ he⟩) (a:=negDir i)) Q
noncomputable abbrev dye (x:Cover)(a:Axis)(b:ℤ):Cover:=Function.update x a b
lemma painted (x:Cover) (a:Axis)(d:ℤ)(h:x∈Lattice.box r)(hv:d.natAbs ≤ r):dye x a d∈ Lattice.box r:=by
     obtain ⟨hz,ht⟩:=box_test.mp h; rw [box_test]; constructor<;> intro i<;> specialize hz i <;> specialize ht i<;> unfold dye<;> rw [update_apply]; all_goals split_ifs <;> omega
lemma slab (h:x∈Lattice.box r)(hy:z∈Lattice.box r)(K:Finset Axis)(a:Axis)(ha:a∉K)(he:∀ j,j∉K→x j=z j):StepsL x z (bed (Lattice.box r) a (x a)) (K.card*(2*r)):=by
       induction K using Finset.induction_on generalizing x z with
       | empty=>
           have hv:x=z:= funext fun j=>he j (notMem_empty _); subst z; rw [card_empty,zero_mul]; exact identity (mem_filter.mpr ⟨h,rfl⟩)
       | @insert j s ht ih=>
           simp only[mem_insert,not_or] at ha; let y:=dye x j (z j); obtain ⟨h1,h2⟩:= box_test.mp hy; have hp: (z j).natAbs ≤ r:= by specialize h1 j; specialize h2 j; omega
           obtain ⟨h3,h4⟩:=box_test.mp h; have hv:y j=z j:= update_self ..; have hh:y a=x a:= update_of_ne ha.1 ..; let ho:= painted x j (z j) h hp; let hv':=(show StepsL y z (bed (Lattice.box r) a (x a)) (s.card*(2*r)) from hh ▸ ih ho hy ha.2 (fun i hi=> if hx:i=j then hx ▸ (show y j=z j from hv) else (show y i=x i from update_of_ne hx ..).trans (he _ (by simp [hx,hi]))))
           let P:= adjust j h ho (fun i hi=>Eq.symm (update_of_ne hi ..)) (show (y j-x j).natAbs ≤2*r from by specialize h1 j; specialize h2 j; specialize h3 j; specialize h4 j; omega) a ha.1
           rw [card_insert_of_notMem ht,add_mul,one_mul,add_comm]; exact both P hv'
lemma ceiling (h:x∈Lattice.box r)(hy:z∈Lattice.box r)(a:Axis)(he:x a=z a):StepsL x z (bed (Lattice.box r) a (x a)) (8*r):=by
       let U:Finset Axis:=univ.erase a; let p:=slab h hy U a (by simp [U]) (fun i hi=>by have hx: i=a:= by_contra fun h=> hi (mem_erase.mpr ⟨h,mem_univ _⟩); subst a; exact he); have hf:U.card≤4:= Finset.card_le_univ _|>.trans (by simp [Axis]); refine lend p (fun _ h=>h) ?_; nlinarith [hf] -- rfl subset wrong
-- bark ONLY shell 
noncomputable abbrev RingP (r:ℕ):=Lattice.box r|>.filter fun x=>∃ i,(x i).natAbs=r
lemma close (h:x∈ RingP r): x∈ Lattice.box r:= (mem_filter.mp h).1
lemma gallery (h:x∈Lattice.box r)(hz: (x a).natAbs=r)(hx:z∈ Lattice.box r)(he:x a=z a):StepsL x z (RingP r) (8*r):=lend (ceiling h hx a he) (fun _ hy=> mem_filter.mpr ⟨(mem_filter.mp hy).1,a, (mem_filter.mp hy).2.symm ▸ hz⟩) le_rfl
end StepsL
end YM.OPE.Merchant
