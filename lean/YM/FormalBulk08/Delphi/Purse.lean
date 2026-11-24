import YM.FormalBulk08.Delphi.Games
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Delphi
open Lattice Laurent Bloch Precision Stationary RG Wilson Filter Function
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix
open Next.Free Reef Flat Dove Dove.Lab North Elm Spigot Aster Source Drops Labels
open RG.Supply Push.PriceCompiler Borough Sable Tundra Sierra
variable {X:Type}{G:Gauge}{K:KernelChoices}{W:Borough.Window G K}{F:∀ d,Frame G d}{H:Hol G}{ρ:ChartRatio G}{Q:Herald}{Y:Sheet G}{P:Rolls Y}{T:Protection P}{V:Delays T}{A:Levels G}{j t:ℕ}
-- separate issue for fuel width power queries.
structure Jolt (K:KernelChoices)(U:ℕ→ℕ) (F:∀ d,Frame G d)(H:Hol G)(f:ℕ→ℕ):Prop where
    body : ∀ j t:ℕ,t≤j → ∀ D E R d,∀ o:Loc G 1,d≤j→D≤ j→E≤j→R≤j→∀ u≤ U j, perCap K H (F d) D E R u j t o ≤ (f j:ℝ)
    soil:∀ j t:ℕ,t≤j → ∀ R E,R≤j→E≤j→∀ u≤ U j, skirtV G K u R E j t ≤ (f j:ℝ)
lemma jolt_raises (F:∀ d,Frame G d)(H:Hol G)(K:KernelChoices)(u v:ℕ→ℕ): ∃ f:ℕ→ℕ,v≤ f ∧ Jolt K u F H f:= by
    let I(j:ℕ):= Fin (j+1); let a(j x:ℕ)(h:x≤ j): I j:=⟨x,by omega⟩
    choose B hB P using fun j:ℕ=> bddBill (fun p:I j × I j × I j × I j × I j × I (u j) × Loc G 1=> perCap K H (F p.1.val) p.2.1.val p.2.2.1.val p.2.2.2.1.val p.2.2.2.2.2.1.val j p.2.2.2.2.1.val p.2.2.2.2.2.2)
    choose C hC Q using fun j:ℕ=> bddBill (fun p:I j×I j×I j×I (u j)=>skirtV G K p.2.2.2.val p.2.1.val p.1.val j p.2.2.1.val)
    let f j:= v j+Nat.ceil (B j+C j); have hx (j:ℕ):B j+C j≤(f j:ℝ):=(Nat.le_ceil _).trans (Nat.cast_le.mpr (Nat.le_add_left ..)); refine ⟨f,fun j=>Nat.le_add_right ..,⟨fun j t y D E R d o A h e k u' b=>?_,fun j t y R E D A u' U=>?_⟩⟩
    · exact (le_abs_self _).trans ((P j (a j d A,a j D h,a j E e,a j R k,a j t y,a (u j) u' b,o)).trans ((le_add_of_nonneg_right (hC j)).trans (hx j)))
    exact (le_abs_self _).trans ((Q j (a j E A,a j R D,a j t y,a (u j) u' U)).trans ((le_add_of_nonneg_left (hB j)).trans (hx j)))
lemma jolt_more {U f g:ℕ→ℕ}(h:Jolt K U F H f)(hp:f≤g):Jolt K U F H g:= by
    have hv j: (f j:ℝ) ≤ g j:= by exact_mod_cast hp j
    exact ⟨fun j t ht D E R d o hd hD hE hR u hu=> (h.body _ _ ht _ _ _ _ _ hd hD hE hR _ hu).trans (hv _),fun j t ht R E hr he u hu=> (h.soil _ _ ht _ _ hr he _ hu).trans (hv _)⟩
structure Bottle (K:KernelChoices)(U:ℕ)(F:∀ d,Frame G d)(H:Hol G)(L:Side) (j:ℕ)(B:ℝ):Prop where
    mark:∀ d D E R u t,d≤j→D≤j→E≤j→R≤j→u ≤ U→ t≤j→∀ (o:Loc G 1) (P:Patch)(V:Lodge P),P.L=L→P.J=j → |burrow K H (F d) D E R u j t o P V|≤ B
    wake:∀ R E u t,R≤j→E≤j→u≤U→t≤j→∀ (P:Patch)(V:Lodge P),P.L=L →P.J=j → |tracks G K u R E j t P V| ≤ B
lemma bottled (K:KernelChoices)(U:ℕ)(F:∀ d,Frame G d)(H:Hol G)(L:Side)(j:ℕ):∃ B:ℝ,0 ≤ B ∧ Bottle K U F H L j B:=by
   let I:= Fin (j+1);let x (i:ℕ)(h:i≤j):I:= ⟨i,by omega⟩;let J:={P:Patch // P.L=L ∧ P.J=j};let P:= (i:J) × Lodge i.val;let _ : Finite J:= patch_owned;let _ (p:Patch):Finite (Lodge p):= lodge_owned p
   obtain ⟨B,b,M⟩:= bddBill (fun p:I× I ×I× I ×I × Fin (U+1)× Loc G 1× P=>burrow K H (F p.1.val) p.2.1.val p.2.2.1.val p.2.2.2.1.val p.2.2.2.2.2.1.val j p.2.2.2.2.1.val p.2.2.2.2.2.2.1 p.2.2.2.2.2.2.2.1.val p.2.2.2.2.2.2.2.2)
   obtain ⟨C,c,W⟩:=bddBill (fun p:I×I×I× Fin (U+1) × P=> tracks G K p.2.2.2.1.val p.1.val p.2.1.val j p.2.2.1.val p.2.2.2.2.1.val p.2.2.2.2.2)
   refine ⟨B+C,add_nonneg b c,⟨fun d D E R u t he hp hz hR hu ht o Q V h hb=>?_,fun R E u t hr he hv ht P V hp hz=>?_⟩⟩
   · exact (M (x d he,x D hp,x E hz,x R hR,x t ht,⟨u,by omega⟩,o,⟨⟨Q,h,hb⟩,V⟩)).trans (le_add_of_nonneg_right c)
   exact (W (x R hr,x E he,x t ht,⟨u,by omega⟩,⟨⟨P,hp,hz⟩,V⟩)).trans (le_add_of_nonneg_left b)
structure Booth (K:KernelChoices)(Q:Herald)(F:∀ d,Frame G d)(H:Hol G)(ρ:ChartRatio G)(u j:ℕ)(W:Lab G K X) :Prop extends Poster K Q F H ρ W j where
   money: ∀ d D R E t:ℕ, d < D→d+3≤j → (d+1)*(d+1)≤ t → D≤j →R≤j→E ≤ j→ t≤u→ ∀ o:Loc G 1,Nesting (F d) D E R t W o
   motion: ∀ R E t:ℕ,R≤j→E≤j→t≤u → Weather W t R E
lemma vertical (U:ℕ→ℕ)(W:Lab G K X)(h:∀ i,Jolt K U F H (fun j=> ((W.V i).clock.factor j).val))(ht:Poster K Q F H ρ W j)(hv:∀ i:Leaf W.scrolls,j ≤ W.upper i)(S:Leaf W.scrolls→ℝ)(hs:Soft (chron W.scrolls) S)(hy:∀ i:Leaf W.scrolls,Bottle K (U (W.upper i)) F H ((W.V i.a).S.block i.b) (W.upper i) (S i))(hp: Monotone U): Booth K Q F H ρ (U j) j W:= by
    have hX(i:Leaf W.scrolls):=((W.V i.a).fits.mono (show i.b ≤ i.b+1 from Nat.le_succ _))
    refine { ht with money:=fun d D R E t hw hz hZ hD hR hE he o=>?_,motion:=fun R E t hR hE hT=>?_}
    · let f (x: Leaf W.scrolls):=burrow K H (F d) D E R t (W.upper x) (W.lower x) o (W.pat x) (W.wood x.a x.b); have he' x:t≤ U (W.upper x):= he.trans (hp (hv x)); refine ⟨ht.glow,(Nat.mul_le_mul (by omega) (by omega)).trans hZ,f,hs.below (fun x=>?_),fun x=>?_⟩
      · exact ((hy x).mark d D E R t _ ((hw.le.trans hD).trans (hv x)) (hD.trans (hv _)) (hE.trans (hv _)) (hR.trans (hv _)) (he' x) (hX x) o _ (W.wood _ _) rfl rfl).trans (le_abs_self _)
      refine buried_up (D:=D) (d:=d) K H _ _ _ _ ⟨hw,hZ, (W.V x.a).clock.adm _, show d+1 ≤ W.upper x-2 by have he:= hv x;omega,(W.V x.a).clock.adm _⟩ ?_
      have he:= (h x.a).body (W.upper x) (W.lower x) (hX x) D E R d o ((hw.le.trans hD).trans (hv x)) (hD.trans (hv _)) (hE.trans (hv _)) (hR.trans (hv _)) t (he' x); unfold upper at he;rw [(W.V x.a).fits.sameFactor] at he; exact he
    let f (x:Leaf W.scrolls):=tracks G K t R E (W.upper x) (W.lower x) (W.pat x) (W.wood x.a x.b);have he' x:t≤ U (W.upper x):= hT.trans (hp (hv x)); refine ⟨ht.glow,f,hs.below (fun i=>?_),fun x=>?_⟩
    · exact ((hy i).wake R E t _ (hR.trans (hv _)) (hE.trans (hv _)) (he' _) (hX i) _ (W.wood _ _) rfl rfl).trans (le_abs_self _)
    apply tracts G K _ _ ((W.V x.a).clock.adm _) ((W.V x.a).clock.adm _); have he:=(h x.a).soil (W.upper x) (W.lower x) (hX x) R E (hR.trans (hv _)) (hE.trans (hv _)) t (he' x);unfold upper at he;rw [(W.V x.a).fits.sameFactor] at he;exact he
end YM.FormalBulk08.Delphi
