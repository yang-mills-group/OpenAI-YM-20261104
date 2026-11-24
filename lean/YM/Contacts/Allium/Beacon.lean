import YM.Contacts.Allium.Astro
import YM.Contacts.Odor.Aroma
/-! # Winding limits for post-regulator deadlines. -/
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace YM.Contacts.Allium
open Function Filter Finset Lattice Gauge RG Matrix Wilson Milling Pulse Loom Flux Revest.Outlay PhysicalNext.Repeat Pressure Precision UVNext.CouplingReset
open Push.Uniform Pulse Spine Garf Steam House Exterior Model Model.Arbor Province.Costing PertExtension.Series Radial
open Lintel Lintel.Angle Lintel.Plata Loom Junction Junction.Current Junction.Buyer Junction.Provision ConnectedActivityE6 Blaze Blaze.March Coat Meter Capture YM.Stationary Cove Lumen
open Resetter Sienna Next.Scheduling Barrage Barrage.Reserve Push.AbsoluteSums
open scoped Topology ContDiff Classical NNReal BigOperators Matrix.Norms.Frobenius
variable {G:Gauge} {i j k n r:ℕ}{c c':Side} {X:G.ColorIndex} {a σ C v Λ p:ℝ}{t:Clip}
namespace Grant
variable (X σ C t k n) 
-- Hantee generalizes log fee pass. Width for tiny period may vary.
structure Item (G:Gauge) where
    x:ℝ -- hatβ coarse
    c:Side
    raw : bore G -- post unreset
    pitch : bore G -- post reset
    B: Bed
    F: PathData G
    P:BudgetPoint
    U: House (Lines G c 1)
namespace Item
abbrev sink' (X:G.ColorIndex)(A:Item G):= sink X A.raw
abbrev advance (X:G.ColorIndex)(A:Item G)(k:ℕ)(q:ℝ):= shiftβ q (k+3) (A.sink' X)
abbrev land (X:G.ColorIndex) (t:Clip) (A:Item G)(k:ℕ)(β:ℝ)(u:Positions (Primary A.c G)) := aperture (c:=A.c) A.pitch A.P A.F t k β (A.advance X k β) A.U (Boulevard.actual u) (Arbor.settle A.c u) -- syntax advance name collision
structure Bounded (X:G.ColorIndex) (p:Clip)(σ C:ℝ) (Z j k n:ℕ)(Q:ℝ→ℝ)(A:Item G): Prop where
    height : (Fintype.card (Site A.c):ℝ) ≤ Q A.x
    beauty : (A.P).B= radiusB A.x
    earned : ∀ u<k+3, ‖pin (A.sink' X) u‖ ≤ lush A.x^j
    vessel : 10*A.P.B < A.c.val
    girth i r : i<k+3 → r<k+3 → r≠0→ Rooted (Range.cheap _) (hair A.pitch A.c i r) (lush A.x^j) ∧ Rooted (Range.cheap _) (hair A.raw A.c i r-A.U i r) (hush (2*narrow A.x) A.c * lush A.x ^ j)
    shine : Aegis X A.pitch A.B ∧ Resetter.QuietPower (A.sink' X)
    portal : hair A.pitch A.c= lowerHouse (A.sink' X) (hair A.raw A.c)
    prospect : A.F.Bounds p σ C (loopBill G 1 A.x) ∧∃ z, Z≤z∧ n+3≤z∧ ∀ i≤k, Charted G k A.x A.P A.F A.pitch p z (ripe A.x) ((z+1:ℝ)⁻¹) i z
-- f whose width paid.Fire
variable (A:Item G) (Z:ℕ)(Q:ℝ→ℝ)
end Item
open Item
section film
variable {Q:ℝ→ℝ}{A:ℕ→Item G}{N:Meter}
-- choose output Epoch param using actual film. Takes arbitrary β(s). Lens pull via Paper.
variable {X k n t σ C}
variable (hs:N.β=(fun i=>(A i).x))
set_option quotPrecheck false
local notation "P" => (fun i:ℕ=> (A i).c)
local notation "λ'" => (A)
local notation "H" => (fun i=> Item.U (A i))
local notation "A'" => (fun i=> Item.pitch (A i))
local notation "t⁰" => (fun i=>Item.P (A i))
local notation "M" => (fun i=> hair (A i).raw (P i))
local notation "B" => (fun i=> sink' X (A i))
lemma paid_q (G:Gauge)(u:ℝ→ℝ)(ht:Rate G 1 a u): N.Rush a (u ∘ N.β):= Meter.Rush.grounded ht N.grows (by simp_rw [ownHat]; exact .refl _ _)
variable (hX:Flat G Q)(w:∀ i, Bounded X t σ C i j k n Q (A i))
include hX w hs
-- hush kills via coneCost when rim ≥ radius.B.It.Ass.Fixed.
lemma senility : let u:= N.β; N.Rush a (fun i=> hush (2*narrow (u i)) (P i)):= by
   let f x:= Real.exp (-(narrow x:ℝ)*Model.Province.aperture (radiusB x)); intro u; apply (paid_q G f (coneCost a)).view; filter_upwards with i; unfold hush; rw [← Real.exp_neg,Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; refine le_trans ?_ (le_abs_self _); apply Real.exp_le_exp.mpr;
   let y:=(N.β i); let s:= (narrow y:ℝ); have ht:0<s:= narrow_pos _; let p:= (A i).P.B; have hu: p=radiusB y:= (by unfold p y; rw [hs]; exact (w i).beauty); let k:= Model.Province.aperture (radiusB y); push_cast; change - (2*s*((P i).val:ℝ)) ≤ (-s)*(k:ℝ); refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonpos_left (a:=(↑(2:ℕ)*((P i).val:ℝ))) ?_ (neg_nonpos.mpr ht.le)); swap; · exact_mod_cast (show k ≤ 2*(P i).val by unfold k Model.Province.aperture; rw [← hu]; have h:= (w i).vessel; unfold p; change _ ≤2*(A i).c.val; omega)
   ring
lemma deep : N.Rush 0 (fun i=> lush (A i).x^j):= by rw [show (fun i=>lush (A i).x^j)=_ from (show _=(fun i=> lush (N.β i)^j) from by rw [hs])]; exact paid_q G (fun i=> lush i^j) (raised (lushPrice G) j) -- lhs ?
lemma earnedPin : Live B N (k+3):= by
   intro i hi; refine (deep hs hX w).view ?_; exact Eventually.of_forall fun v=> ((w v).earned i hi).trans (le_abs_self _)
lemma census₀ : N.Rush 0 fun i=> (Fintype.card (Site ((A i).c)):ℝ):= by refine (paid_q (N:=N) G Q hX).view (Eventually.of_forall fun i=>?_); simp only [Function.comp_apply, hs]; exact (Real.norm_of_nonneg (Nat.cast_nonneg _)).trans_le ((w i).height.trans (le_abs_self _))
lemma lights : Firm X t (fun i=>(A i).F) (fun i=>(A i).B) (fun i=> (A i).pitch) (fun i=>(A i).P) P N σ C k n ∧ Spectrum N k (M-H) (fit*(k+3)):= by
   have hu:N.Rush 0 (fun i=> (Fintype.card (Lines G ((A i).c) 1):ℝ)):= by
       refine ((census₀ hs hX w).bind (Fintype.card (Loc G 1):ℝ)).take (Eventually.of_forall fun i=>?_); dsimp only; rw [show Fintype.card _=_ from (show Fintype.card (Lines G ((A i).c) 1)=_ from Fintype.card_prod ..)]; push_cast; rfl
   have hp:= deep hs hX w; choose H' hm hk ht using fun i=>(w i).prospect.2; let Y:= lush ∘ N.β; have hx:Tendsto H' atTop atTop:= tendsto_atTop_mono (f:=id) hm tendsto_id
   have hz:Tendsto (fun i=>(H' i:ℝ)) atTop atTop:= tendsto_natCast_atTop_atTop.comp hx
   refine ⟨⟨⟨_,(fun i=> (H' i+1:ℝ)⁻¹),(fun i=> (H' i:ℝ)),H',paid_q G _ (loopBill_rate G 1),?_,?_,?_⟩,⟨fun i r h hh=>?_,hu⟩, census₀ hs hX w, Eventually.of_forall (fun i=> ⟨(w i).shine.1,(w i).vessel⟩)⟩,⟨fun i r h ht=>?_, hu⟩⟩
   · intro e b h; filter_upwards [N.grows.eventually_ge_atTop 1,hz.eventually_ge_atTop (-b)] with i hi ht; rw [Real.norm_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hi) _)]; exact Real.rpow_le_rpow_of_exponent_le hi (by linarith)
   · intro b hb; filter_upwards [N.grows.eventually_ge_atTop 1,hz.eventually_ge_atTop b⁻¹] with i hi ht; rw [Real.norm_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hi) _)]; apply Real.rpow_le_rpow_of_exponent_le hi; exact inv_le_of_inv_le₀ hb (by linarith)
   · rw [hs]; exact Eventually.of_forall fun i=> ⟨(w i).prospect.1, hk i,ht i⟩
   · refine ⟨_,hp,Eventually.of_forall fun a=>?_⟩; have hx:=((w a).girth (i+r-2) r (by omega) (by omega) hh).1; exact ⟨hx.cash,hx⟩
   -- Root with hush ≤. Qual shape.*
   refine ⟨_,(senility hs hX w (N:=N) (a:=fit*(k+3))).times hp (add_zero _),?_ ⟩; rw [hs]; refine Eventually.of_forall fun y=>?_ ; have he:= (w y).girth (i+r-2) r (by omega) (by omega) ht|>.2; exact ⟨he.cash,he⟩
variable (hk:2≤k)(hn:k≤n)(hg:G.Simple) (ha:1+stashp*(k+3)< a) {β:ℕ→ℝ} (hβ: Foil β N)
variable (L:Side)
local notation "θ" => (fun i=> Positions (Primary ((A i).c) G))
local notation "f" => (fun i=> Sienna.eaves G L (N.β i))
local notation "J" => Frame.Port θ (1)
local notation "Φ" => (fun i j (x:θ i)=> Arbor.settle (P i) ((f i) • x))
include L hg hk hn ha hβ
lemma catered : N.Rush fit f ∧ ∀ᶠ i in atTop,0<f i:= by
    let Y i:= betaF G (N.β i) L; have ht (i:ℕ): N.β i ≤ Y i:= le_add_of_nonneg_right (YM.Work.E04.shift_nonneg G L)
    refine ⟨(Meter.Rush.mono (Meter.Rush.any (p:=vow)) (by norm_num [vow,fit])).view ?_ , N.eventual.mono fun i hi=> Real.rpow_pos_of_pos (hi.trans_le (ht i)) _⟩; filter_upwards [N.eventual] with i hi; let a:=(f i); have hv:0< a:= Real.rpow_pos_of_pos (hi.trans_le (ht i)) _; exact (Real.norm_of_nonneg hv.le).trans_le ((Real.rpow_le_rpow_of_nonpos hi (ht i) vow_ok.le).trans (le_abs_self _))
-- price hZ capture.norm.
def Lens (G:Gauge)(L:Side)(X:G.ColorIndex) (x p:ℝ)(t:Clip)(k n:ℕ)(A:Item G) (β:ℝ):Prop := let H':= Sienna.eaves G L x; let ξ:= A.advance X k β;
   |ξ-β-pin (A.sink' X) 2| ≤ potion x ∧ ∀ z:Positions (Primary A.c G), ‖z‖<H'→Brush (n+1) (x^p) H'⁻¹ (A.land X t k β) z
lemma silhouette : ∀ᶠ i in atTop,Lens G L X (N.β i) a t k n (A i) (β i):= by
   have h := earnedPin hs hX w; have hu : ∀ᶠ i in atTop, Resetter.Uniform (B i) ∧ QuietPower (B i):= Eventually.of_forall fun i=>⟨sink_mast _,(w i).shine.2⟩; let P' i:=(settle (G:=G) ((A i).c)); have hc := catered hs hX w hk hn hg ha hβ L;
   have hf:Budget N J (n+3) fit Φ:=(Arms.project P' (Arms.weighted (Budget.id (k:=n+3) (Frame.head (E:=θ) (Meter.Rush.settle 1))) hc.1 (zero_add _)) ((Meter.Rush.settle («M»:=N) 1).view (Eventually.of_forall fun i=> by rw [norm_norm,norm_one]; exact (due _))) (add_zero _))
   have hx:= lights hs hX w; have ht:= Allium.strut hx.1 hg hk hn hβ h hu (Eventually.of_forall fun i => (w i).portal) hx.2 hf; let d i:= Item.advance X (A i) k (β i); let K i:= A i; have hh:= (Foil.dimes (k:=k+3) hβ (by omega) h hu) (-(1/4)) (by norm_num)
   filter_upwards [hh,ht.read ha,hc.2] with i hi hx' hf; let H':= (f i); refine ⟨hi, fun v hv=> ?_⟩; let v':= H'⁻¹ • v; have htmem:v'∈ Frame.Bank θ 1 i:= mem_ball_zero_iff.mpr (by unfold v'; rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hf.le),inv_mul_lt_iff₀ hf]; exact hv.trans_le ((mul_one H').symm.le)); let g:θ i →ℝ:= land X t (A i) k (β i); let D:θ i→L[ℝ]θ i:= Junction.Provision.morph (H')⁻¹;
   have ht: Brush (n+3) (N.pow a i) 1 (fun z:θ i=>g ((f i) • z)) (D v):= hx' ⟨_,htmem⟩; have hv':= ht.reading (L:=D) (slopes (inv_nonneg.mpr hf.le)); -- pos slopes need inverse
   rw [one_mul] at hv'; exact ((hv'.shimmy (Eventually.of_forall (fun x=>congr_arg g (smul_inv_smul₀ hf.ne' x).symm))).smaller (by omega));
end film
variable (L:Side){Q:ℝ→ℝ}
variable (hk:2≤k)(hn:k≤n)(hg:G.Simple)(hX:Flat G Q)(ha:1+stashp*(k+3)<a) 
include hg ha hX hn hk
open Clock
lemma flare (j:ℕ): ∃ i:ℕ, ∀ᶠ x in atTop, ∀ A:Item G, A.x=x→A.Bounded X t σ C i j k n Q→∀ β:ℝ, inBand x β → Lens G L X x a t k n A β:= by
   by_contra H; push Not at H; choose v u h hv using (fun i:ℕ=> show ∃ (A:Item G)(β:ℝ), (i:ℝ) ≤ A.x ∧ Bounded X t σ C i j k n Q A ∧ inBand A.x β∧ ¬ Lens G L X A.x a t k n A β from (by
        obtain ⟨x,h,hx⟩:= ((H i).and_eventually (eventually_ge_atTop (i:ℝ))).exists; obtain ⟨A,hA,hQ,b,hb,h⟩:= h; exact ⟨A,b,hA.symm ▸ hx,hQ,hA.symm ▸ hb,hA.symm ▸ h⟩)); let N:Meter:=⟨fun i=>(v i).x,tendsto_atTop_mono (f:=fun i:ℕ=>(i:ℝ)) h tendsto_natCast_atTop_atTop⟩; have he:= silhouette (N:=N) (β:=u) (A:=v) rfl hX (fun i=>(hv i).1) hk hn hg ha (Eventually.of_forall fun i=>(hv i).2.1) L; obtain ⟨i,hi⟩:= he.exists; exact (hv i).2.2 hi
end Grant
end YM.Contacts.Allium
