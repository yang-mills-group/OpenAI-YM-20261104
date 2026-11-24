import YM.FormalBulk08.Copula.Charge
import YM.Price.Waits

/-! An auxiliary formal family is not an existential YM history.
Levels uses J→∞. For transfer of Lemma(kbulk) to the independent
constant-L,J prescription we embed arbitrary long finite windows. The price
polynomial will **NOT** change with this embedding. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Copula
open Filter Function Finset Lattice Laurent Bloch Precision RG
open Stationary Supply Next.Free Reef Flat Dove Dove.Lab North Elm Spigot Aster Source Drops Labels
open scoped BigOperators Topology Classical Matrix
variable {X:Type} {G:Gauge} {K:KernelChoices}{W: Borough.Window G K}{F:∀ d,Frame G d}{H:Hol G}{ρ:ChartRatio G}{Q:Herald}{S:Sheet G}
open Borough
lemma setup {U:Empire G K X} (V: X → ℕ) (k:X→ℕ)(hb:Years (register G K U W k (fun i=>sealedTime (U.V i).S (V i))).scrolls)
   (hzp:∀ i: X,Pre K W ρ F H (fun j=>((U.V i).clock.factor j).val))
   (C:Leaf (register G K U W k (fun i=>sealedTime (U.V i).S (V i))).scrolls → ℝ)(hs:Soft (chron _) C) (Q':∀ x,Counter K Q ((U.V x.a).S.block x.b) ((U.V x.a).clock.J (x.b+1)) F H ρ W (C x))
   (J:ℕ)(h:5≤J)(hr:∀ x,J≤ (U.V x).clock.J (k x+1)) :
    let Y:=register G K U W k (fun i=>sealedTime (U.V i).S (V i))
    Avenue.Extras Y ∧ Soft (chron Y.scrolls) (fun i=>(Y.windowD i)⁻¹) ∧ ∀ E ≤ J, Y.Use ρ E ∧ Broc.Render Y E ∧∀ d D, d+3 ≤ J → d< D→D ≤ J→∀ (o:Loc G 1) (R:ℕ), R≤J→Quota (F d) H Y o D E R ∧∀ l≤ J,∀ u≤ J, VividC u o E D l Y Q:= by
    intro Y
    have hT (i:Leaf Y.scrolls): J≤Y.upper i:= (hr i.a).trans ((U.V i.a).fits.mono (show k i.a+1 ≤ i.b+1 from Nat.add_le_add_right i.zone _))
    have hx (i:Leaf Y.scrolls): Y.lower i ≤ Y.upper i:= (Y.V i.a).fits.mono (Nat.le_add_right ..);have hv (i:Leaf Y.scrolls): Y.upper i≤ Y.lower i+1:= (Y.V i.a).fits.stepSlow _
    have S:= Q'
    have hi i:C i ≤ |C i| := le_abs_self _
    have hz i:=W.lines (hx i) (hv i)
    refine ⟨hs.below fun i=>?_,hs.below fun i=> ?_,fun E hE=>?_⟩
    · exact (le_add_of_nonneg_left (abs_nonneg _)).trans (((S i).header _ (hx i)).trans (hi i))
    · exact (le_add_of_nonneg_right (abs_nonneg _)).trans (((S i).header _ (hx i)).trans (hi i))
    have hy i:= (S i).coarse _ (hx i) E (hE.trans (hT i)); have hQ (i:Leaf Y.scrolls): (((U.V i.a).clock.factor (Y.upper i)).val:ℝ)= wideA i:=by
       dsimp only [upper]; rw [show Y.V i.a=U.V i.a from rfl,(U.V i.a).fits.sameFactor];rfl
    refine ⟨⟨hb,fun i=> h.trans (hT i),fun i=>W.pos _,fun i=>(hz i).1,fun i=>(hz i).2.1,fun i=> ((hzp i.a).vacuum _ _ _ (hE.trans (hT i)) (hx i) (hv i)).trans_eq (hQ i),hs.below fun i=>?_,hs.below fun i=>?_⟩,⟨hs.below fun i=> ?_,hs.below fun i=>?_⟩,fun d D hd ht hD o R hr=>?_⟩
    · exact ((S i).past _ (hx i) E (hE.trans (hT i)) _ (Y.wood i.a i.b) rfl rfl).trans (hi i)
    · exact ((le_add_of_nonneg_right (abs_nonneg _)).trans (le_add_of_nonneg_right (abs_nonneg _))).trans ((hy i).trans (hi i))
    · exact ((le_add_of_nonneg_left (abs_nonneg _)).trans (le_add_of_nonneg_right (abs_nonneg _))).trans ((hy i).trans (hi i))
    · exact (le_add_of_nonneg_left (add_nonneg (abs_nonneg _) (abs_nonneg _))).trans ((hy i).trans (hi i))
    have ht' i:= (ht.le.trans hD).trans (hT i); refine ⟨⟨ht,fun i=>by have := hd.trans (hT i);omega,fun i=> (hz i).2.2,fun i=> ((hzp i.a).fields _ _ _ _ _ _ o (ht' i) (hD.trans (hT i)) (hE.trans (hT i)) (hr.trans (hT i)) (hx i) (hv i)).trans_eq (hQ i),hs.below fun i=>?_⟩,fun l hl u hu=>?_⟩
    · exact ((S i).light _ (hx i) _ (ht' i) _ (hE.trans (hT i)) _ (hD.trans (hT i)) _ (hr.trans (hT i)) o _ (Y.wood i.a i.b) rfl rfl).trans (hi i)
    have H' i:= ((S i).render _ (hx i) E (hE.trans (hT i)) D (hD.trans (hT i)) l (hl.trans (hT i)) u (hu.trans (hT i)) o).trans (hi i)
    exact ⟨hs.below fun i=>(le_add_of_nonneg_right (abs_nonneg _)).trans (H' i),hs.below fun i=> (le_add_of_nonneg_left (abs_nonneg _)).trans (H' i)⟩
-- Universal family with all estimates of the Poster. A witness depends on
-- depth m but C's here (the Poster) do not. Can turn as needed to subprobes.
structure Auxiliary (P:Patch)(K:KernelChoices)(O:Herald)(ρ:ChartRatio G)(F:∀ d,Frame G d)(H:Hol G)(W:Borough.Window G K)(V:Lab G K ℕ):Prop where
    scheme:∀ i j,j≤ i → (V.V i).clock.J j=P.J
    step:∀ i j, j < i → (V.V i).S.block j=P.L
    fund:Poster K O F H ρ V P.J
    neck : V.neck=fun _=>0
    years:∀ i j,j ≤ i  → (V.years i).day j=1
    stamps: ∀ i j,j ≤ i → V.width i j=W.width P.J
    walk: ∀ i j,V.wood i j=routes _
lemma pay_aux (hG:G.Simple)(h:∀ P:Patch,P.Branches K G)(F:∀ d,Frame G d)(H:Hol G)(O:Herald)(ρ:ChartRatio G)(W:Borough.Window G K)(j:ℕ)(hx:5≤j) :∃ M:ℕ, ∀ (P:Patch),P.J=j→ M≤P.L.val → ∃ V:Lab G K ℕ, Auxiliary P K O ρ F H W V:= by
   obtain ⟨X,-,U⟩:= funded_before _ W ρ F H 0
   let S:= tilled G K X j h (by omega);obtain ⟨M,m⟩:= fund_first hG S
   refine ⟨M,fun P hp hv=>?_⟩;obtain ⟨R,r⟩:= m _ hv P.odd_side
   choose B b C using fun i=> counter_paid K O (R.L i) i F H ρ W
   choose A ha H' Hz Q' using fun N:ℕ=> delay_install hG R B b N
   let T:Empire G K ℕ:= ⟨A,H',fun i k=> routes _⟩; let V:=register G K T W (fun _=>0) (fun i=> sealedTime (A i).S i)

   have hstep (i n:ℕ): Counter K O ((A i).S.block n) ((A i).clock.J (n+1)) F H ρ W (B ((A i).clock.J (n+1))) := by rw [← (A i).fits.sameFactor,ha]; exact C _
   have hρ: Soft (chron V.scrolls) (fun x=>B (V.upper x)) := by
       refine ((soft_coin (chron V.scrolls) (B S.first)).plus (soft_day _)).below ?_; intro x; rw [abs_of_nonneg (b _)]; exact (Q' _ _).trans (le_abs_self _)
   have hX: Years V.scrolls:= by
       refine ⟨⟨1,zero_le_one,fun i m k _ hx=>?_⟩,hρ.below ?_⟩
       · rw [one_mul]; exact age_build _ _ hx
       intro x; rw [Nat.abs_cast]; exact (hstep x.a x.b).1.trans (le_abs_self _)
   have he(i):Pre K W ρ F H (fun j=> ((T.V i).clock.factor j).val):= pre_enlarge U (fun u=> by change X u ≤ ((A i).clock.factor _).val; rw [ha]; exact (R.large u).need)
   have hv (x:ℕ): j≤(A x).clock.J 1:= ((Hz x 0 (by omega)).ge.trans ((A x).fits.mono zero_le_one))
   obtain ⟨q,g,Z⟩:= setup (U:=T) (fun i=>i) (fun _=>0) hX he _ hρ (Q:=O) (fun x=>hstep x.a x.b) j hx hv
   refine ⟨V, fun i k hi=>(Hz i k hi).trans hp.symm,fun i k hk=>?_,?_,rfl,fun i k hi=> under_time _ hi,fun i k hi=>congr_arg _ ((Hz i k hi).trans hp.symm),fun _ _=>rfl⟩
   · change (A i).S.block k=P.L; rw [←(A i).fits.sameFactor,ha,Hz _ _ hk,r]
   rw [hp]; exact ⟨q,g,fun i hi=> (Z i hi).1,fun i hi=>(Z i hi).2.1,fun _ _ o _ _ hu hv hx hy hz=> ((Z _ hz).2.2 _ _ hu hv hx o _ hy).1,fun d D o R E _ _ hd hD ht hR hE hl hm=> ((Z _ hE).2.2 _ _ hd hD ht o _ hR).2 _ hm _ hl⟩
end YM.FormalBulk08.Copula
