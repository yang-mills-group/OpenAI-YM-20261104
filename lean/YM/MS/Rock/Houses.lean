import YM.MS.Rock.Conic
/-!
# Trees Synch proof. Extend at all integer dimensions.

Sym at rank, price tested. Frees use hards plots on D. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Rock
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux
open Landau Arts Pilot Spin Arc Wire Path
open scoped Topology ContDiff
open Metric
variable {G:Gauge}{I:Type}{b c:Bool}{f H:ℂ→ Mob G}{u:ℂ→ Rip G}{D:Set ℂ}
lemma Bold0 (p:Set ℂ)(Q:(I→ℂ)→ℂ) (h:Q∈ Heat.Centre I){f:ℂ→ I→ℂ}(hp:∀ i, Forest p fun z=> f z i): Forest p fun z=> Q (f z) := by
   refine Submodule.span_induction (p:=fun Q _=> Forest p fun z=> Q (f z)) ?_ (fun z _=>differentiableAt_const _) ?_ ?_ h; rintro v ⟨i,rfl⟩; exact hp i; · intro a b hx hy h0 h1 z hz; exact DifferentiableAt.add (h0 z hz) (h1 z hz)
   intro a b hK he z hz; exact (he z hz).const_mul _
lemma Hol.port {Q:Shade G}(hq:Priced Q)(h:Hol D f): Hol D fun i=>portZ Q (f i):= ⟨fun c R hc hp=>count_price Q hq (h.price c R hc hp), fun m l=> Bold0 _ _ (sense_Q (Q m)|>.reaches l) (h.top m)⟩
lemma Sync.port {Q:Shade G}(hk:Priced Q)(hp:CountsD b Q)(h:Sync b f): Sync b fun i=>portZ Q (f i):= by obtain ⟨A,hA,hX⟩:=h.eye.price; exact ⟨⟨⟨A,hA,count_price Q hk hX⟩,Hol.port hk h.eye.sky⟩,fun i hi=>zMotion (h.vote i hi) hp⟩
-- finite
lemma Tree_stamp (h:hill D f)(hk:hill D H)(hp:∀ m a b p, Forest D fun i=> u i m a b p) : hill D fun i=> arbor (u i) (f i) (H i):= by
   intro m w z hz; let Z:= (Landau.parity (C:=G.ColorIndex) (A:=L m));
   have he (a b : Legs (Shore G m)): DifferentiableAt ℂ (fun z=> attaches Z (u z m) (f z m) (H z m) a b) z:= by
       unfold attaches; dsimp only; refine DifferentiableAt.fun_sum (fun i _=>DifferentiableAt.fun_sum (fun j _=> DifferentiableAt.add ?_ ?_ )) <;> exact (hp m _ _ _ z hz).mul (((h m _ z hz).const_mul _).mul (hk m _ z hz))
   have hu (w:Legs (Shore G m)) (U:ℂ→ Shared (Shore G m) ℂ)(hH:∀ a b,DifferentiableAt ℂ (fun i=>U i a b) z): DifferentiableAt ℂ (fun i=> scatter (field Z) w (U i)) z:= by
       induction w generalizing U with| nil=> exact hH [] []| cons i l ih=> exact ih _ (fun a b=> DifferentiableAt.add (hH (i::a) b) ((hH a (i::b)).const_mul _))
   exact hu w _ he
lemma wood_bill {A B C:ℝ}(h:Shine A f)(hv:Shine B H)(hr: Sugar C u)(hA:1≤A)(hB:1≤B)(hC:1≤C): Shine (C*(A*B)) fun i=>arbor (u i) (f i) (H i):= by
   have he:= for_tree h hv (u:=fun i:Town=> u i.val) (fun m a b=> railto (hr m a b)) (fun i=> (mass_positive i (by linarith:0<C)).le)
   convert! he using 1; ext; rw [mint_mul hC (one_le_mul_of_one_le_of_one_le hA hB), mint_mul hA hB]; -- finish
lemma Hol.woods (h:Hol D f)(hv:Hol D H)(hh:Hop D u): Hol D (fun i=> arbor (u i) (f i) (H i)) where
    top:= Tree_stamp h.top hv.top hh.top
    price:= by intro c R hc hp; convert! for_tree (h.price c R hc hp) (hv.price c R hc hp) (u:=fun i:closedBall c R=>u i) (fun n i j=> railto (hh.price c R hc hp n i j)) (fun _=>zero_le_one) using 1; simp
lemma Sync.tree (h:Sync b f)(hv:Sync b H)(hc:Stamp b u)(hk:∀ i∈Town, closedF (u i) c)(hr:∀ i∈Town,reverseF (u i)) : Sync b (fun i=> arbor (u i) (f i) (H i)):= by
    obtain ⟨A,hA,h_f⟩:= h.eye.price; obtain ⟨B,hB,h_y⟩:= hv.eye.price; obtain ⟨C,hC,h_u⟩:= hc.arg.price; exact ⟨⟨⟨_,one_le_mul_of_one_le_of_one_le hC (one_le_mul_of_one_le_of_one_le hA hB), wood_bill h_f h_y h_u hA hB hC⟩, h.eye.sky.woods hv.eye.sky hc.arg.sky⟩,fun i hi=> arboreal (h.vote i hi) (hv.vote i hi) (hc.tree i hi) (hr i hi) (hk i hi)⟩
end YM.MS.Rock
