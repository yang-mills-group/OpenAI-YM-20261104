import YM.Contacts.Costar.Ticket
import YM.Contacts.Costar.Wide
set_option autoImplicit false
noncomputable section
namespace YM.Contacts.Costar
open Function Set Filter MeasureTheory Extraction Extraction.Spin Wilson Spec Cells Lattice Word Bid Work.B15 OS OS.Ground Org Next.Phase
open scoped Topology BigOperators Matrix.Norms.Frobenius NNReal InnerProductSpace
variable {G : Gauge} {C : Family G} {F : Extraction.Order} {b k l t q N p m r : ℕ} {E : Episode C F k} {S:Table C.book}{τ:Filter (ℕ×ℕ)}

variable (P:Ticket E τ) (e:b≤k) (hl:b≤l) (ht:l≤t) (A:ℝ)
variable (w: Fin m→ C.book.Token)(y:Fin m→ Cover)(B:Fin m→ℝ)
lemma cuts_translate (N p : ℕ) (q : Cover) (U : Config G (C.side N p)) :
    P.cuts N p 0 (translate (location C.S k N p q) U) = P.cuts N p q U := by
  simp_rw [Ticket.cuts,add_zero,C.translation,Order.location_add]
include hl in
lemma paid_now (hk:k ≤ N) (hx:t ≤ N) (w':Site (C.side N p))(Z : Config G (C.side N p)→ℂ)
    (hC:C.Makes)
    (hf: P.cuts N p 0 = fun U=> Z U*∏ i,C.seen (w i) (location C.S k N p (y i)) U)
    (hY : t ≤ N)
    (hB : ∀ i,0 ≤ B i) (hO:∀ i,C.ref (w i).1 ≤ N) (hs:∀ i,Single C (w i) (B i) t N p)
    (hh : ∀ i, Next.Phase.Inside ((center C.S p (ht.trans hx) 0).newly w') (3*span C.S hx p) (location C.S k N p (y i)))
    (h₀: (0:Site (C.side N p))∈ ((center C.S p (e.trans hk) 0).newly w').chamber 0)
    (hD: Interior (((center C.S p (e.trans hk) 0).newly w').chamber 0) Z)
    (hp: ((center C.S p (e.trans hk) 0).newly w').rootTest (C.beta N p) Z ≤ A)
    (hw: let x i:= location C.S k N p (Episode.step C e r i); let η (j:Fin (2*q)×Fin m):= location C.S k N p (y j.2)+x j.1.val
         (∀ (i:Fin (2*q)) j, span C.S (e.trans hk) p < separation (x i.val) (η j))∧
         (∀ i j,i≠j→ span C.S (ht.trans hx) p < separation (η i) (η j)))
    (hsize:2*r*(2*q) ≤ (C.side b p).val)(hr:0<r):
    ‖P.fromCut e r q N p‖ ≤ (A * ∏ i, B i)^(2*q):=by
   let x i:= location C.S k N p (Episode.step C e r i)
   let Y (j:Fin (2*q)×Fin m):= location C.S k N p (y j.2)+x j.1.val
   let yT:= (center C.S p (ht.trans hx) 0).newly w'; let T:= (center C.S p (e.trans hk) 0).newly w'; let c (i:Fin (2*q)):= addr T r i.val
   let Z' (j:Fin (2*q)) : Config G (C.side N p)→ℂ:= if j.val%2=0 then fun x=>star (Z x) else Z
   let v (i:Fin (2*q)×Fin m):= if i.1.val%2=0 then C.book.conjugate (w i.2) else w i.2
   have hv (U:Config G (C.side N p)) : (∏ i,T.copy (c i) (Z' i) U)*(∏ i,C.seen (v i) (Y i) U)=P.twice e r q N p U:=by
       rw [Fintype.prod_prod_type,← Finset.prod_mul_distrib]; unfold Ticket.twice
       refine Finset.prod_congr rfl fun i _=>?_ 
       rw [addr_copy, addr_root' C e w' hk]; rw [← cuts_translate, hf] -- rfl T let?
       by_cases h:i.val%2=0
       · simp_rw [v,Z',h,if_true,star_mul',star_prod]; unfold Family.seen Register.conjugate
         simp_rw [C.reality hC (hO _)]; unfold Y; simp only [C.translation]; rfl
       simp_rw [v,Z',h,if_false,Family.seen,C.translation]; rfl
   have HH j: Next.Phase.Inside yT (3*span C.S hx p) (Y j):=inside_shifted C e w' hk w' _ hl _ r j.1.val _ (hh j.2) rfl
   have hdv:yT.side.val∣ T.side.val:= Around.inherits (C:=C) (p:=p) hl (ht.trans hx)
   have he i j: c i ≠ T.which (Y j):= fun h=> (hw.1 i j).not_ge
      (T.extent (which_after C e w' hk _ _ h₀) (show Y j∈ T.chamber (c i) from (h.symm ▸ (shared_inside T yT rfl rfl rfl hdv _ _ (HH j)).1)))
   have hV i : Single C (v i) (B i.2) t N p:= by
       unfold v; split
       · rw [show C.book.conjugate (w i.2)=Spin.token _ (w i.2) (1,true) from by simp [Spin.token,Register.move]]; exact (hs _).moves _
       exact hs _
   have hp i:T.rootTest (C.beta N p) (Z' i)≤ A:=by unfold Z'; split; rw [rootTest_star];exact hp; exact hp
   have hI i: Interior (T.chamber 0) (Z' i) := by unfold Z'; split; exact hD.real;exact hD
   unfold Ticket.fromCut; rw [← funext hv]; apply (stocked hC (T:=T) (Y:=yT) rfl rfl rfl hdv hx (Around.inherits (C:=C) (p:=p) ht hx) Z' c (addr_inj T hr hsize) (fun _=>A) hI hp v Y HH he hw.2 (B ∘ Prod.snd) (fun i=> hB _) hV).trans_eq
   rw [Fintype.prod_prod_type]; simp [Function.comp_def,mul_pow]
variable [τ.NeBot](hT:τ ≤ F.fuse)(V:Final C F S)(hp:Grill C F)

include P hT hp e hl ht
-- same bound for all viewers. Allows an angle-variable offset of the center tiling, not a root comparison varying in cutoff
lemma follow (v:Viewer V)
    (hA:0≤A) (hB:∀ i,0≤B i)(hgap:∀ i,2*C.S.a b< ‖C.S.gridPoint k (y i)‖)
    (hh:∀ i j,i≠j→ 2*C.S.a l < ‖C.S.gridPoint k (y i)-C.S.gridPoint k (y j)‖) (hs:∀ i, F.late (Single C (w i) (B i) t))
    (ht': ∀ᶠ c:ℕ×ℕ in τ, ∃ (o:Site (C.side c.1 c.2)) (Z:Config G (C.side c.1 c.2)→ℂ) (he:k ≤ c.1) (hY:t ≤ c.1),
       let T:= (center C.S c.2 (e.trans he) 0).newly o; let L:= (center C.S c.2 (ht.trans hY) 0).newly o;
       0∈ T.chamber 0 ∧ Interior (T.chamber 0) Z ∧ T.rootTest (C.beta c.1 c.2) Z ≤ A ∧
       (∀ i, Next.Phase.Inside L (3*span C.S hY c.2) (location C.S k c.1 c.2 (y i))) ∧
         P.cuts c.1 c.2 0 = fun U=> Z U*∏ i,C.seen (w i) (location C.S k c.1 c.2 (y i)) U):
      ‖∑ i,E.factor i*(watches V v).expect (E.word i)‖ ≤ (A * ∏ i,B i):= by
   refine Ticket.watches_le P hT V hp _ (mul_nonneg hA (Finset.prod_nonneg (fun i _=> hB i))) e ?_ v
   intro q
   filter_upwards [seats_grid C e (κ:=2*q) F y hgap hh,eventually_gt_atTop 0] with r hr hh
   have hn: ∀ᶠ c:ℕ×ℕ in F.fuse, 2*r*(2*q) ≤ (C.side b c.2).val:= by
       rw [Extraction.Order.fused,Extraction.Order.late]
       apply (F.per.cofinal.eventually (C.S.period_strict.tendsto_atTop.eventually (eventually_ge_atTop (2*r*(2*q))))).mono; intro p hp
       exact Eventually.of_forall fun i=> hp.trans (Nat.le_mul_of_pos_right _ (C.S.denominator b).property)
   have hu := Extraction.Order.witnesses w F; have hv' : ∀ᶠ c in F.fuse, ∀ i, Single C (w i) (B i) t c.1 c.2 := eventually_all.mpr hs
   filter_upwards [((hr.and (hn.and (hu.and hv'))).filter_mono hT), ht'] with c hs hh'
   obtain ⟨hp,hn,hr,hv⟩:= hs; obtain ⟨o,Z,he,hY,h₀,hI,hZ,hX,hE⟩:= hh'; exact paid_now P e hl ht A w y B he hY o Z V.room.cutoff hE hY hB hr hv hX h₀ hI hZ ⟨fun i j=>hp.1 i j _,fun i j h=>hp.2 i j h _⟩ hn hh
end YM.Contacts.Costar
