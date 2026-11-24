import YM.WilsonCoeffUV.Product.Connected.Refund
/-!
# Post calendar bills for joints
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Soil
open Gauge Power PathCost Precision Embroider Fountain Cosmos Shard Realm
open PowerSeries
open scoped Topology BigOperators
variable {n:Side}{U V α β ι:Type*}{r h D j m e i i' j' l k u a:ℕ}{A B C s:ℝ}{G:Gauge}
variable {p q:ProfileW}{D' t η K M s S δ:ℝ}
variable {b:ℕ}
lemma apexPrice (e u b m a l:ℕ)(G:Gauge)(v:m≤e): Bank.Slate (xpos e (sen G e b u)) (dpos e (sen G e b u)) (fun _I j=>coeff m (j.R.P.moving^a*(j.R.P.moving⁻¹)^l)) (fun _I j=>coeff m (j.R.Q.moving^a*(j.R.Q.moving⁻¹)^l)):=by
   obtain ⟨d,H⟩:= titles (G:=G) (i:=m) (e:=e+1) (by omega) 0 a l; refine ⟨d,fun i=>?_⟩; obtain ⟨C,h,f⟩:= H i; exact ⟨C,h,fun j=>f j.R⟩
lemma soarPrice (e u b k r i:ℕ)(G:Gauge)(v:i≤e): Spent (V:=(fun _:Gear G=>Hooks G)) (u:=u) (b:=b) (e:=e) r (fun I v=>joinC I v.R.P k v.P v.U i r) (fun I v=>joinC I v.R.Q k v.Q v.V i r):=by
   unfold joinC Blue.mix; apply Fallow.sum _ (ChargePlot ..); intro a ha; have hv:= Finset.mem_range.mp ha; apply Fallow.st (apexPrice e u b (i-a) a r G (by omega)) _ (ChargePlot ..)
   unfold hotC sluice finallyA; apply Fallow.gleanS (J:=TripG e b u) (P:=fun (I:Gear G) v=>(∑ j∈ Finset.range (1+k+3*a), boilingJ I v.R.P v.P v.U j a) r) (Q:=fun (I:Gear G) v=>(∑ j∈ Finset.range (1+k+3*a), boilingJ I v.R.Q v.Q v.V j a) r)
   simp_rw [Finset.sum_apply]; exact Fallow.sum (fun j _=>burgeon G e u b (show a≤e by omega) j r) (ChargePlot ..)
lemma priceWalk (G:Gauge)(e k u b:ℕ): ∃ d:ℕ,∀ I:Gear G,∃ C:ℝ,0≤ C∧∀ (X:TripG e b u I)(i r l:ℕ),i≤ e → r ≤ k+e → l ≤ k →
    YieldP 0 X.η u (C*X.R.x^d*X.plot) X.R.σ (joinC I X.R.P l X.P X.U i r) (joinC I X.R.Q l X.Q X.V i r):=by
    let q:= Fin e.succ× Fin (k+e+1) × Fin k.succ
    choose V h using fun (v:q)=>soarPrice e u b v.2.2 v.2.1 v.1 G (Nat.le_of_lt_succ v.1.isLt)
    set d:=∑ i,V i; refine ⟨d,fun I=>?_⟩; choose C hC p using fun i=> h i I
    refine ⟨∑ i,C i,Finset.sum_nonneg (fun i _=>hC i),fun X i r l t z v=>?_⟩; let w:q:= (⟨i,Nat.lt_succ_of_le t⟩,⟨r,Nat.lt_succ_of_le z⟩,⟨l,Nat.lt_succ_of_le v⟩); have ht:= X.R.rich; have hx:= zero_le_one.trans ht
    have hv: V w≤ d:= Finset.single_le_sum (fun _ _=> Nat.zero_le _) (Finset.mem_univ w)
    exact (p w X).step (mul_le_mul_of_nonneg_right (calc C w*xpos e (sen G e b u) I X ^ V w ≤ C w * X.R.x^d:= mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht hv) (hC _)
                                                         _ ≤ _:= mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun i _=> hC i) (Finset.mem_univ w)) (by positivity)) ((ChargePlot ..).post I X)) X.R.θ

variable {c' N n' m:ℕ}
abbrev poreD (G:Gauge)(e k u b:ℕ):= (priceWalk G e k u b).choose
abbrev poreF (G:Gauge)(e k u b:ℕ)(I:Gear G):= ((priceWalk G e k u b).choose_spec I).choose
variable {E W:Credit}
structure SpringD (R:Realm G (e+1) E)(k u b:ℕ)(W:Credit):Prop where
    lens m (h:R.anchor≤ m) : poreF G e k u b (R.mint m h).gear ≤ R.cash W m
def priceWG (G:Gauge)(e k u b:ℕ)(E W:Credit):= W.prodC ((costXV G e E).powC (poreD G e k u b))
abbrev heirP (A:Levels G)(m:ℕ)(p:ProfileW) (x:Cover):= p (parentC (A.S.block m) x)
def PaidMer (e u:ℕ)(p: ProfileW)(X Y: Era G ℝ)(A δ:ℝ):Prop:=∀ i j,i≤e→ PromX p u A δ (X.2 i j) (Y.2 i j)
variable {R:Realm G (e+1) E}
theorem enterShore (h:SpringD R k u b W)(v:R.anchor ≤ m)(t:m<c')(a:c' ≤ N)(g:c' ≤ n')(P P' Q Q':Era G ℝ)(x:Auth i P)(X:Auth i P')(y:Auth j Q)(Y:Auth j Q')(z: SplitHill p q η K D')(hv:i+j≤ k)(w:δWarm R m c'≤ δ)(p': PaidMer e (u+b) (heirP R.draws m p) P P' A δ)(q': PaidMer e (u+b) (heirP R.draws m q) Q Q' B δ):
   let X:= JoinGap R.draws R.paid m N i j P Q; let Y:= JoinGap R.draws R.paid m n' i j P' Q'; Fringed (i+j) e u η (R.cash (priceWG G e k u b E W) m*(pearlB u b K D'*(A*B))) δ X Y :=by
    intro X' Y'; have fN:=t.trans_le a; have fM:= t.trans_le g
    have hx:Auth _ X':= (Auth.verse R.draws fN R.hG R.green (x.manor y)).sub ((Auth.verse R.draws fN R.hG R.green x).manor (Auth.verse R.draws fN R.hG R.green y)); have hy:Auth _ Y':= (Auth.verse R.draws fM R.hG R.green (X.manor Y)).sub ((Auth.verse R.draws fM R.hG R.green X).manor (Auth.verse R.draws fM R.hG R.green Y))
    set I:=(R.mint m v).gear; let V:= ReelTime R (le_refl e) v t a g; let θ:=V.σ; have hθ: θ ≤ δ:= w
    let J: Rally (e+1) 0 I:= { V with σ:=δ, θ:= V.θ.trans hθ, paid:=fun i j h=>(V.paid i j h).graded hθ le_rfl, Υ:= V.Υ.partial hθ, Χ:= V.Χ.partial hθ, Ω:= V.Ω.partial hθ }
    let T: TripG e b u I:=⟨J,p,q,K,D',η,z,P.2,P'.2,Q.2,Q'.2,A,B,p',q'⟩
    let L:= R.cash (priceWG G e k u b E W) m*T.plot; have hL:0≤ L:=mul_nonneg (zero_le_one.trans (Credit.purchase _ (R.depth _ v))) ((ChargePlot ..).post I T)
    refine ⟨hx,hy,J.θ,fun c r hm=>?_⟩; change YieldP 0 η u L δ (X'.2 c r) (Y'.2 c r)
    by_cases hh:r≤k+e; swap; · rw [hx.coverN c r (by omega),hy.coverN c r (by omega)]; exact YieldP.zero.step hL J.θ
    have ha: X'.2= joinC I T.R.P (i+j) T.P T.U:= heatMiss R.draws x y R.hG R.green fN
    have hb: Y'.2= joinC I T.R.Q (i+j) T.Q T.V:= heatMiss R.draws X Y R.hG R.green fM
    rw [ha,hb]; apply ((((priceWalk G e k u b).choose_spec I).choose_spec.2 T c r (i+j) hm hh hv).step) _ J.θ; unfold L priceWG cash; rw [Credit.products,Credit.power]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (h.lens m v) (pow_nonneg (zero_le_one.trans (T.R.rich)) _)) ((ChargePlot ..).post I T)
end YM.WilsonCoeffUV.Mer
