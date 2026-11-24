import YM.FVA2.O.Ward.Rings
/-!
# Static BV from the MS input itself
No auxiliary filter/master assumptions. This also identifies the linear drive.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Ward
open MS Function Filter Set Finset MS.Plane MS.Koszul Flux MeasureTheory MS.Heat MS.Book Convolve Signal
open MS.Breeze MS.Latch MS.Native MS.Osc.Snap MS.Osc MS.Fiddle MS.Garment MS.Garment.Wick MS.Rock MS.Rock.Path MS.City MS.Rake MS.Tone Momentum MS.Landau Detect
open MS.Land MS.Outlook MS.Local.Physical Pearl Train Dock Emit Logarithm MS.Motif MS.Hem Mell MS.Garment.Wave
local notation "Π0"=> Job.single Unit
variable {G:Gauge}{B:Deck G}{A:Booked B}
variable {U: Edge G}{F H: T (Law G)}{v:Law G}{y s:ℝ}{J:Pearl.Flats G}{d n:ℕ}{t:ℤ}{b:Bool}
abbrev Φ (G:Gauge)(s:ℝ):= rack (A0 G s 0) (B0 G s 0) (Wick.Q G 0) planeF
-- namespace Q possible ambiguity by later opens
abbrev Pulse (M:MS_Data G A)(y s:ℝ): T (Law G):= fun i => Archive 4 M.bulk i (y,s)
abbrev readM (M:MS_Data G A)(i: Plaid B d)(y s:ℝ) : T (Law G):= fun n=> Archive d (M.marks d i) n (y,s)
lemma fullW (h:Host J d): four d J (y,s) ∈ Wallet G:= by
    apply permits.mpr; intro E _ _ w; rw [ spaceArc ]; exact BigG ( blade0 (s:=s) (y:=y) h ).price 0 w
lemma fullS (h:Gang b d t J): Solid false (four d J (y,s)) t:= by
    obtain ⟨r,hr⟩:= h.price; have h0:= ( Moony.toast (clockMoon hr)); let F:= hereZ d J s y; have hp: Collar t F:= valueC h.dost h0 _ need_col (fun i=> (hr i).fine.ghost); have hx:Sight F:= sees_some h.dost h0 _ need_eye (fun i=> (hr i).fine.sense)
    exact ⟨fun l i j k _=> hp.sym 0 l i j k, fun v _ hv=>hp.ghost 0 v hv,fun w _ p=> congr_fun ( hp.color 0 p ) w, fun w _=> hx 0 w⟩
lemma fullU (h:Gang b d t J) : ∃ r:ℕ,∀ s y, Upper false r ( four d J (y,s)):= by
    obtain ⟨r,hr⟩:= h.price; refine ⟨r.toNat,fun s y w hw hp=>?_⟩; obtain he: Issue r (hereZ d J s y):= valueC h.dost ( Moony.toast (clockMoon hr)) _ need_tail (clockCap hr); exact he 0 w (by omega)
lemma clayS (h:Solid false v t): Symm (field Landau.parity) v:= fun l i j r=> h.symm l i j r (fun i=>Bool.noConfusion i)
lemma truthP (h: Solid false v t): Pure (field Landau.parity) (Local.parity t) v:= Rails.parity (v:= ghostNo ∘ Prod.fst) (fun i=> Native.ghostParity i.1) (fun i hi=> h.ghost i (fun z=>Bool.noConfusion z) hi)
variable (M: MS_Data G A)
include M
lemma center: Pulse M y s 0=0:= congr_fun (archive0 ((M.bulkOK 0).2 rfl) 4) 0
lemma at_bulk (n:ℕ): Solid false (Pulse M y s n) 0:= fullS (gang (M.bulkOK n))
lemma count (n:ℕ) : Pulse M y s n∈ Wallet G:= fullW (Host.host (gang (M.bulkOK n)))
lemma homeM (n:ℕ)(i: Plaid B d): Solid false (readM M i y s n) 0:= fullS (gang (M.markOK d i n))
lemma calm (n:ℕ)(i: Plaid B d): readM M i y s n∈ Wallet G:= fullW (Host.host (gang (M.markOK d i n)))
-- match standard lives/grow using walk. general tool
omit M
lemma trunkM {B F: High.Recount G}(K: High.Needle G)(he:B 0 (y,s)=0)(ht:K.measure=planeF)(hK:K.meter s=U)(hh:Pass U (F n (y,s)) planeF): Domain.recu K 0 1 B F n (y,s)= orbit U planeF (F n (y,s)) + pairW (boulevard Landau.parity U) (fun k=>B k (y,s)) (fun k=> F k (y,s)) n:= by
    rw [ Domain.recu,Domain.using_tree,one_smul,paired, Tone.Frame.canon_sub (fun i j=> boulevard Landau.parity U (B i (y,s)) (F j (y,s))) n, he,map_zero,LinearMap.zero_apply,zero_add, finite_cc planeF hh]; simp only [ht,hK]; rfl
lemma trunkB {B:High.Recount G}(K:High.Needle G)(h:0<n)(he:B 0 (y,s)=0)(ht:K.measure=planeF)(hK:K.meter s=U)(hh:Pass U (B n (y,s)) planeF): let V := fun i=> B i (y,s); Domain.recu K 1 ((2:ℂ)⁻¹) B B n (y,s)= orbit U planeF (B n (y,s)) + (2:ℂ)⁻¹ • pairW (boulevard Landau.parity U) V V n:= by
    intro V; rw [Domain.recu,Domain.using_tree,paired, Tone.Frame.canon_corner (fun i j=>boulevard Landau.parity U (V i) (V j)) n h, show V 0=0 from he,map_zero,map_zero, LinearMap.zero_apply,zero_add,zero_add,finite_cc planeF hh]; simp only [ht,hK]; rfl
include M
lemma climate : Agrees ((Φ G s).matCont (Pulse M y s) n) 0 := by
    let P:= Pulse M y s; by_cases hv:n=0; · subst n; change Agrees ((Φ G s).J (P 0)+ (2:ℂ)⁻¹ • pairW _ P P 0) _; rw [paired,Finset.Nat.antidiagonal_zero,Finset.sum_singleton, show P 0=0 from center M,map_zero,map_zero,smul_zero,add_zero]; exact fun _ _=>rfl
    let K:= High.degreeMaster id (High.spaceD G); let X:=B0 G s 0
    intro l hl; have hh : ( Wick.Q G 0).raise (P n) l= High.Ward id (High.spaceD G) n 1 ((2:ℂ)⁻¹) ( Archive 4 M.bulk ) ( Archive 4 M.bulk ) (y,s) l := B_ward M.bulkOK l (fun _=>hl) ( wardLeader M.bulkOK wisdom n|>.1) (by omega)
    unfold High.Ward at hh; rw [trunkB (y:=y) (s:=s) (U:=X) K (by omega) (center M) rfl rfl (rB.pays Geo.Coherent (count M n))] at hh; change (((Wick.Q G 0).raise (P n)+orbit X planeF (P n))+(2:ℂ)⁻¹ • pairW (boulevard Landau.parity X) P P n) l=0; simp only [ add_assoc,Pi.add_apply,hh ]; exact neg_add_cancel _
lemma whereM (i: Plaid B d) : (Φ G s).res (Pulse M y s) (readM M i y s)=0:= by
    let P:= Pulse M y s; let X:= B0 G s 0; let V:= readM M i y s
    ext n l; have he : (Wick.Q G 0).raise (V n) l= High.Ward id (High.spaceD G) n 0 1 (Archive 4 M.bulk) (Archive d (M.marks d i)) (y,s) l := ( Outlook.fieldD M.bulkOK (M.markOK d i) wisdom ((A.law d i).moodQ)).master.qfm n (y,s) l (by omega) (fun i=>Bool.noConfusion i) (fun i=>Bool.noConfusion i); unfold High.Ward at he; rw [trunkM (y:=y) (s:=s) (U:=X) (High.degreeMaster id (High.spaceD G)) (center M) rfl rfl (rB.pays Geo.Coherent (calm M n i))] at he; change (((Wick.Q G 0).raise (V n)+orbit X planeF (V n))+pairW (boulevard Landau.parity X) P V n) l=0; simp only [add_assoc,Pi.add_apply,he]; exact neg_add_cancel _
omit M
lemma pDust (h:∀ i,Agrees (F i) 0): pairW (boulevard Landau.parity U) F H=0:= by
    funext n; rw [paired]; exact Finset.sum_eq_zero fun i _=> by rw [ blvd,tree_agrees _ _ _ _ _ (h i.1), ← blvd,map_zero,LinearMap.zero_apply ]
include M
lemma square_full (h:∀ k,H k∈Wallet G)(hp:∀ k,Symm (field Landau.parity) (H k)) : (Φ G s).res (Pulse M y s) ((Φ G s).res (Pulse M y s) H)=0:= by
    funext i; unfold Φ; rw [ square_at planeF i (fun k _=> wise (h k) rB (hp k)) (fun k _=> wise (count M k) rB ( clayS (at_bulk M k) )) (fun k _=> truthP (at_bulk M k)) no_raise (cl_b G s 0) (reverse_b G s 0) (fun i j _=>colors (count M i) (h j) rB rB (reverse_b G s 0)) (zeroTrace s 0), show pairW (rack (A0 G s 0) (B0 G s 0) ( Wick.Q G 0) planeF).C ((rack (A0 G s 0) (B0 G s 0) ( Wick.Q G 0) planeF).matCont (Pulse M y s)) H= 0 from pDust (fun k=> climate M) ]; exact neg_zero
lemma derivative_identity (h:∀ k,H k∈ Wallet G)(hp:∀ k,Symm (field Landau.parity) (H k)): let P:= Pulse M y s; let A:= Φ G s; A.res P (A.lives P H)+ promote A.L H+ pairW A.D P H+ pairW A.C (A.grow P) H=A.lives P (A.res P H):= by
    intro P A; have hp:= point_sole planeF (K:=A0 G s 0) (L:=B0 G s 0) (Q:=Wick.Q G 0) (pieces (count (y:=y) (s:=s) M) h (fun k=> clayS (at_bulk ..)) hp (fun k=>truthP (at_bulk ..))); rw [ show pairW (rack (A0 G s 0) (B0 G s 0) (Wick.Q G 0) planeF).X ((rack (A0 G s 0) (B0 G s 0) (Wick.Q G 0) planeF).matCont (Pulse M y s)) H= 0 from pDust (fun k=> climate M), add_zero ] at hp; exact hp
end YM.FVA2.O.Ward
