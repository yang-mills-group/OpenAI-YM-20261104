import YM.FVA2.O.Lives.Case
/-!
# Input the 4D bulk and marked kernels from `YM/MS`

Prove their corresponding evolution (`season`, `comet_V`). See `Resp`
for then working with the `Bank` properties and the Ward-closed fields.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Lives
open MS Function Filter Set Finset MS.Plane MS.Koszul Flux MeasureTheory MS.Heat MS.Book Convolve Signal
open MS.Breeze MS.Latch MS.Native MS.Osc.Snap MS.Osc MS.Fiddle MS.Garment MS.Garment.Wick MS.Rock MS.Rock.Path MS.City MS.Rake MS.Tone Momentum MS.Landau Detect MS.Color Real
open Ward Job Wire MS.Local.Physical MS.Land MS.Outlook MS.Hem MS.Hem.Mell MS.Pearl Train Dock Emit
open scoped Topology ContDiff
variable {G:Gauge}{I E:Type}{B:Deck G}{O:Booked B}{Y X X' Y': T (Glade G I)}{K:T (Flats G)}{p q:CostsM G}{t:ℤ}{d:ℕ}{s:ℝ}{i:I}{η:I→ℝ}
abbrev gather (M: MS_Data G O)(η:I→ℝ): T (Glade G I) := fun i=> nameR (Archive 4 M.bulk i) η
abbrev letIn (d:ℕ)(η:I→ℝ)(i:T (Flats G)): T (Glade G I) := fun x=> nameR ( Archive d i x ) η
abbrev soloV (d:ℕ)(y:I→ℝ)(M:MS_Data G O)(i:Plaid B d): T (Glade G I):= letIn d y (M.marks d i)
abbrev peek (U:T (Glade G I))(i:I)(s:ℝ): T (Law G):= fun n=> U n i s
lemma z_pair (X Y:T (Glade G I)) (K: Signal.Pair ( Glade G I ))(V: Signal.Pair (Law G))(h:∀ F H:Glade G I, K F H i s= V (F i s) (H i s))(n:ℕ) : pairW K X Y n i s=pairW V (peek X i s) (peek Y i s) n:= by simp_rw [paired,Finset.sum_apply,h]
lemma η_res : peek ( (both G I).res X Y ) i s=(Φ G s).res (peek X i s) (peek Y i s) := by
    funext n; change _ + pairW (both G I).C X Y n i s = (Φ G s).J _ + _; rw [ z_pair X Y (both G I).C (Φ G s).C (fun _ _=>rfl) ]; rfl
lemma η_lives : peek ( (both G I).lives X Y ) i s=(Φ G s).lives (peek X i s) (peek Y i s):= by
    funext n; change _+pairW (both G I).X X Y n i s= (Φ G s).P _ + _; rw [ z_pair X Y (both G I).X (Φ G s).X (fun _ _=>rfl) ]; rfl
lemma η_grow : peek ( (both G I).grow X ) i s = (Φ G s).grow (peek X i s) := by
    funext n; change _+(2:ℂ)⁻¹ • pairW (both G I).X X X n i s= (Φ G s).P _ + _; rw [ z_pair X X (both G I).X (Φ G s).X (fun _ _=>rfl) ]; rfl
lemma collectV {J:Flats G}{b:Bool}(h: Gang b d t J) : Bank (nameR (four d J) η) t:= ⟨ nameD_warm (Host.host h),collectD (Host.host h), fun _ _=> fullS h⟩
variable (M:MS_Data G O)
include M
lemma plenary : Banks (gather M η) 0:= fun i=> collectV (gang (M.bulkOK i))
lemma markW (hp: comet d t M.bulk p K q): Banks ( letIn d η K ) t:= fun i=> collectV (gang (hp i))
lemma zero_B : gather M η 0=0:= funext fun _=> funext fun _=> center M
-- movement of projected comets. full all rows (fig earlier b=false used not master True)
set_option maxHeartbeats 450000 in
lemma season (n:ℕ): Velocity (gather M η n) ((both G I).grow (gather M η) n):= by
    intro i s; let X:=gather M η; let V:= peek X i s; let P:= Φ G s; rw [show (both G I).grow (gather M η) n i s=P.grow V n from congr_fun (η_grow (s:=s) (X:=X) (i:=i)) n]; by_cases he:n=0
    · rw [he,zero_B M]; change Zip (0:Heat.BF (BH G) QP) (P.P (V 0)+(2:ℂ)⁻¹ • pairW P.X V V 0) s; rw [paired, Finset.Nat.antidiagonal_zero,Finset.sum_singleton,show V 0=0 from center M,map_zero,map_zero,smul_zero,add_zero]; exact fun l=> hasDerivAt_const s _
    have hp:= Host.host (gang ( M.bulkOK n )); obtain hv:= Outlook.rise hp.tall ( grow_host M.bulkOK n ).tall (Moony.toast hp.bill) ( RootF ( M.bulkOK n ) ).advance s (η i) 0; obtain H := Bday M.bulkOK (show 1 ≤ n from by omega); let T:=Archive 4 M.bulk; rw [show P.grow V n= Domain.recu (High.spaceD G) 1 ((2:ℂ)⁻¹) T T n (η i,s) from Eq.symm ( trunkB (y:=η i) (s:=s) (U:=lineA G s) (High.spaceD G) (by omega) (center M) rfl rfl (rA.pays Geo.Coherent (Ward.count M n)) ), show Domain.recu (High.spaceD G) 1 _ T T n ( η i,s )= _ from Eq.symm (congr_fun H (η i,s)) ]; exact hv
lemma rec_raw (n:ℕ) (h: (peek (gather M η) i s) 0=0)(T:High.Recount G)(hk: T n (η i,s)∈ Wallet G): let V := fun x=> T x (η i,s); (Φ G s).lives (peek (gather M η) i s) V n=Domain.recu (High.spaceD G) 0 1 ( Archive 4 M.bulk ) T n (η i,s):= Eq.symm (trunkM (High.spaceD G) h rfl (U:=lineA G s) rfl (rA.pays Geo.Coherent hk))
lemma comet_V (hp: comet d t M.bulk p K q) (n:ℕ): Velocity (letIn d η K n) ((both G I).lives (gather M η) (letIn d η K) n):= by
    intro i s; let W:= letIn d η K; rw [show (both G I).lives (gather M η) W n i s=(Φ G s).lives (peek (gather M η) i s) ( peek W i s ) n from congr_fun η_lives n, show (Φ G s).lives _ (peek W i s) n = _ from rec_raw M n (center M) (Archive d K) ((markW (η:=η) M hp n).invoice), ← Mday M.bulkOK hp ]; have h:= Host.host ( gang (hp n)); exact Outlook.rise h.tall (mark_h M.bulkOK hp n).tall (Moony.toast h.bill) (RootF (hp n)).advance s (η i) 0
end YM.FVA2.O.Lives
