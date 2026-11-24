import YM.FVA2.O.Fusion.Whole
/-!
# Rake input for connected multi-mark calculus

`world_price` (`Warm` bounds, using earlier `Rake` results) and
`solitude` to use the `Bank` data here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Fuse
open MS Function Filter Set Finset MS.Plane MS.Koszul Flux MeasureTheory MS.Heat MS.Book Convolve Signal
open MS.Breeze MS.Latch MS.Native MS.Osc.Snap MS.Osc MS.Fiddle MS.Garment MS.Garment.Wick MS.Rock MS.Rock.Path MS.City MS.Rake MS.Tone Momentum MS.Landau Detect MS.Color Real
open Ward Job Wire MS.Local.Physical MS.Land Lives Puff Serve Rake.Geo Vane
open scoped Topology ContDiff
variable {G:Gauge}{t:Bool}{I E W:Type}[LinearOrder W]{F H:Glade G I}{L:Planet G I}{B:Deck G}{K:Booked B}{M:MS_Data G K}{q:ℤ}{P:Geo I}{x:Position W I} {p a b:I→QP}{R:W→Rake.Label B}{X:Rake.Dance G I W}{S:Finset W}
local notation "Λ0"=> (fun _ : I => lineA G)
local notation "m0"=> (fun _ : I=> planeF)
omit [LinearOrder W] in
lemma soften (hp:Bank F 0)(_:Bank H q): voyage Λ0 false F H=( both G I ).P (joint G I F H)-joint G I ((both G I).P F) H-joint G I F ((both G I).P H):= by funext i t; simp only [Pi.sub_apply]; have he : (both G I).P (joint G I F H) i t = joint G I ((both G I).P F) H i t+joint G I F ( (both G I).P H ) i t+voyage Λ0 false F H i t:= pira (y:=H i t) (x:=F i t) ⟨ hp.invoice, Ward.truthP (hp.tone i t)⟩; rw [he]; abel
omit [LinearOrder W] in
lemma stretch (hp:Bank F 0)(ht:Bank H q): Bank (voyage Λ0 false F H) q := by rw [soften hp ht]; rw [ ← zero_add q ]; exact (( joint_mem hp ht|>.A ).sub ( joint_mem hp.A ht )).sub ( joint_mem hp ht.A )
omit [LinearOrder W] in
lemma attach (hp:Bank F 0)(ht: Bank H q): voyage Λ0 false ( tilt G a F ) ( tilt G b H )= tilt G b (regionC m0 (a-b) Λ0 F H) := funext fun i=> funext fun t=> tension (U:= lineA G t) rA (reverse_a G t 0) (cl_a G t 0) hp.invoice ht.invoice ( Ward.truthP ( hp.tone i t ) ) (a i) (b i)
omit [LinearOrder W] in
lemma point (hp: Bank F 0)(he:Bank H q): Bank (regionC m0 p Λ0 F H) q:= by
    obtain h:= stretch (bankTilt (p:=p) hp) ( bankTilt (p:=0) he ); rw [attach hp he,sub_zero,dizzy] at h; exact h
-- usually parameterized DOrd needed all positions; Mesh only for Warm. Wrap into clause profitable later for irregular mesh
lemma world_price (h:Mesh P x)(he:DOrd K P M R x X)(s:Finset W)(n:ℕ): Warm (X s n) false := by by_cases hv:s.Nonempty; exact ( founded ( builder M h R ) he hv n ).2; rw [Finset.not_nonempty_iff_eq_empty.mp hv,he.1]; exact CabinF.warm0
lemma solitude (h:DOrd K P M R x X)(hx:∀ s k,Warm (X s k) false): Banks ( X S ) 0:= by
    induction S using Finset.strongInductionOn with| _ s ih=>
    by_cases hp: s.Nonempty; swap; · rw [Finset.not_nonempty_iff_eq_empty.mp hp, h.1]; exact fun _=> Bank.zero
    by_cases hs: s.card≥2; swap
    · obtain ⟨i,rfl⟩:= Finset.card_eq_one.mp (show s.card=1 from by obtain he:= Finset.card_pos.mpr hp; omega); rw [h.2.1]; exact ( Response.visit (M:=M) (η:=P.η) ( ( R i ).item ) ).life
    intro k; induction k using Nat.strong_induction_on with| h k IH=>
    obtain ⟨hC,hQ,hY⟩:= h.2.2 s hs k; let A:= gather M P.η; let V:= multi m0 x Λ0 Λ0 A (X s) X k s; have he : Bank V 0:=(Bank.all_fin _ (fun i hi=>( (plenary M) (k-i) ).X (IH i (( Finset.mem_Ico.mp hi ).2 )))).add ( Bank.all_fin _ (fun i hi=> Bank.all_fin _ (fun j _=> point (ih i ( n_small hi|>.1 ) j.1) (ih (s\ i) ( n_small hi|>.2.2.2 ) j.2) )) ); refine triple (hx s k) he ⟨ hC,?_,?_⟩
    · obtain hv: (both G I).P ( X s k )= _:= spine ( hF:=hx s k ) realityA; dsimp only; rw [hv]; exact hQ
    obtain hv : (both G I).P ( X s k )=_:= spine (hx s k) realityA; dsimp only; rw [hv]; exact hY
end YM.FVA2.O.Fuse
