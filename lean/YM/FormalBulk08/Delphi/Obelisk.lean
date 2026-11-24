import YM.FormalBulk08.Delphi.Merge
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Delphi
open Lattice Laurent Bloch Precision Stationary RG Wilson Filter Function
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix
open Next.Free Reef Flat Dove Dove.Lab North Elm Spigot Aster Source Drops Labels
open RG.Supply Push.PriceCompiler Borough Sable Tundra Sierra Copula
variable {X:Type}{G:Gauge}{K:KernelChoices}{W:Borough.Window G K}{F:∀ d,Frame G d}{H:Hol G}{ρ:ChartRatio G}{Q:Herald}{A:Levels G}{V:Empire G K X}{j t:ℕ}
lemma overhead (U:ℕ→ℕ)(hK:Monotone U)(hp:∀ i,Dominoes (V.V i) U F H K)(k:X→ ℕ)(T:X→Time ℕ)(hx:Poster K Q F H ρ (register G K V W k T) j)(hr:∀ x,j≤ (V.V x).clock.J (k x+1))(hw:Soft (chron (register G K V W k T).scrolls) (fun i=>ageZ ((V.V i.a).clock.hatBeta i.b)))(hg:∀ i,Jolt K U F H (fun j=>((V.V i).clock.factor j).val)): Booth K Q F H ρ (U j) j (register G K V W k T):= by
   let Y:= register G K V W k T; choose C hC c H using fun x:Leaf Y.scrolls=> (hp x.a).title x.b;have hv:Soft (chron _) C:= hw.below fun i=> by rw [abs_of_nonneg (hC _)]; exact (c _).trans (le_abs_self _)
   exact vertical U _ hg hx (fun i=> (hr i.a).trans ((V.V i.a).fits.mono (Nat.add_le_add_right (show k i.a ≤ i.b from i.zone) _))) _ hv H hK
-- lyre & dated. slopes measurable eras from First.
lemma postages (U:ℕ→ℕ)(hK:Monotone U)(hp:∀ i,Dominoes (V.V i) U F H K)(k y:X→ ℕ)(u:X→ℝ)(hu:∀ i,0≤u i)(he:∀ i,ageZ ((V.V i).clock.hatBeta (y i)) ≤ 2+u i)(hs:G.Simple)(hE:∀ i,Evergreens K Q F H ρ W (V.V i))(h:5≤j)(hr:∀ x,j≤ (V.V x).clock.J (k x+1))(hg:∀ i,Jolt K U F H (fun j=>((V.V i).clock.factor j).val)) :
    Booth K Q F H ρ (U j) j (register G K V W k (fun i=>lyre (V.V i))) ∧ Booth K Q F H ρ (U j) j (register G K V W k (fun i=> logtime (V.V i).S (y i) (u i) (hu i))):= by
    refine ⟨overhead U hK hp k _ (presold hs hE k h hr) hr ((soft_day _).below (fun i=>?_)) hg, overhead U hK hp k _ (dated hs hE k y u hu he h hr) hr (log_day hs hE k y u hu he) hg⟩; change _ ≤ |(lyre _).day _|; rw [measure (hE i.a)]
lemma boostAux (U:ℕ→ℕ)(hK:Monotone U)(hG:G.Simple)(h:∀ P:Patch,P.Branches K G)(F:∀ d,Frame G d)(H:Hol G)(O:Herald)(ρ:ChartRatio G)(W:Borough.Window G K)(j:ℕ)(hx:5 ≤ j):∃ M:ℕ,∀ P:Patch,P.J=j → M≤P.L.val → ∃ V:Lab G K ℕ, Auxiliary P K O ρ F H W V ∧ Booth K O F H ρ (U j) j V:= by
   obtain ⟨x,-,Y⟩:=funded_before _ W ρ F H 0; obtain ⟨X,hX,Z⟩:=jolt_raises F H K U x
   let S:=tilled G K X j h (by omega);obtain ⟨M,m⟩:=fund_first hG S
   refine ⟨M,fun P hp hv=>?_⟩; obtain ⟨R,r⟩:=m _ hv P.odd_side
   choose B b C using fun i=>counter_paid K O (R.L i) i F H ρ W
   choose D d L using fun i=>bottled K (U i) F H (R.L i) i
   let E(i:ℕ):=B i+D i;have hE i:0≤E i:=add_nonneg (b i) (d i)
   choose A ha H' Hz Q' using fun N:ℕ=>delay_install hG R E hE N
   let T:Empire G K ℕ:= ⟨A,H',fun i k=>routes _⟩; let V:=register G K T W (fun _=>0) (fun i=>sealedTime (A i).S i)
   have hstep(i n:ℕ):Counter K O ((A i).S.block n) ((A i).clock.J (n+1)) F H ρ W (B ((A i).clock.J (n+1))) := by rw [←(A i).fits.sameFactor,ha]; exact C _
   have hV: Soft (chron V.scrolls) (fun x=> E (V.upper x)):= by refine (((soft_coin (chron V.scrolls) (E S.first)).plus (soft_day _))).below fun x=>?_ ;rw [abs_of_nonneg (hE _)]; exact (Q' _ _).trans (le_abs_self _)
   have hρ: Soft (chron V.scrolls) (fun x=>B (V.upper x)):= hV.below (fun i=>by rw [abs_of_nonneg (b _),abs_of_nonneg (hE _)];exact le_add_of_nonneg_right (d _))
   have hS: Soft (chron V.scrolls) (fun x=>D (V.upper x)):= hV.below (fun i=>by rw [abs_of_nonneg (d _),abs_of_nonneg (hE _)];exact le_add_of_nonneg_left (b _))
   have hX' : Years V.scrolls:= by
      refine ⟨⟨1,zero_le_one,fun i m k _ hx=>?_⟩, hρ.below ?_⟩; rotate_left;· intro x; rw [Nat.abs_cast];exact (hstep x.a x.b).1.trans (le_abs_self _)
      rw [one_mul];exact age_build _ _ hx
   have hw(i): X≤ fun j=> ((T.V i).clock.factor j).val:= by intro j; change X j ≤ ((A i).clock.factor _).val;rw [ha];exact (R.large j).need
   have he i:= pre_enlarge Y (le_trans hX (hw i)); have hv(x:ℕ):j≤(A x).clock.J 1:= ((Hz x 0 (by omega)).ge.trans ((A x).fits.mono zero_le_one))
   obtain ⟨q,g,Q⟩:= setup (U:=T) (fun i=>i) (fun _=>0) hX' he _ hρ (Q:=O) (fun x=>hstep x.a x.b) j hx hv
   have hb: Poster K O F H ρ V j:= ⟨q,g,fun i hi=>(Q i hi).1,fun i hi=>(Q i hi).2.1,fun _ _ o _ _ hu hv hx hy hz=> ((Q _ hz).2.2 _ _ hu hv hx o _ hy).1,fun d D o R E _ _ hd hD ht hR hE hl hm=> ((Q _ hE).2.2 _ _ hd hD ht o _ hR).2 _ hm _ hl⟩
   have hT (i n:ℕ): Bottle K (U ((A i).clock.J (n+1))) F H ((A i).S.block n) ((A i).clock.J (n+1)) (D ((A i).clock.J (n+1))) := by rw [←(A i).fits.sameFactor,ha];exact L _
   refine ⟨V,⟨fun i k hi=>(Hz i k hi).trans hp.symm,fun i k hk=>?_,hp ▸ hb,rfl,fun i k hi=> under_time _ hi,fun i k hi=> congr_arg _ ((Hz i k hi).trans hp.symm),fun _ _=>rfl⟩, vertical _ _ (fun i=> jolt_more Z (hw i)) hb (fun i=>?_ ) _ hS (fun i=>hT _ _) hK⟩
   · change (A i).S.block k=P.L;rw [←(A i).fits.sameFactor,ha,Hz _ _ hk,r]
   exact (hv i.a).trans ((A i.a).fits.mono (show 1≤ i.b+1 from by omega))
end YM.FormalBulk08.Delphi
