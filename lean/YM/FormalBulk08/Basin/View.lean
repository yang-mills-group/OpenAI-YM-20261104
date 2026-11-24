import YM.FormalBulk08.Basin.Nurture
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Basin
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Work.F03 Work.F05 Work.F08 PowerSeries
open Vale Quire Sable Aster Dawn Wine Roof Orb Tundra Sierra Wick Series
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{X I J V:Type*}{r n m i j t d l E:ℕ}{σ A B C:ℝ}
variable {X:Type}{τ:Time X}{J:X→Type*} {R:X→Type}{q Q: ∀ i:X,R i→R i→ℝ}{V:∀ i,Reach (R i)}{η σ δ:X→ℝ}{ε:X→ℝ≥0}{x y:∀ i:X,J i→R i}
variable {b c g:∀ i:X,J i→ℝ}{T S:∀ i:X,J i→Tile (R i) r}{u:ℕ}

def Mountain (τ:Time X)(V:∀ i,Reach (R i))(ε:X→ℝ≥0)(x y:∀ i:X,J i→R i): Prop:= ∃ B:X→ℝ,Soft τ B∧(∀ i,0≤B i)∧ ∀ i p,(ε i:ℝ)*(V i).d (x i p) (y i p) ≤ B i
lemma lowlands (hp:Mountain τ V ε x y)(h:Bear τ (fun i=>Sable.grain (V i) (ε i)) x (fun _=>u) b T) : Bear τ (fun i=>Sable.grain (V i) (ε i)) y (fun _=>u) b T:= by
   obtain ⟨B,b',ht,H⟩:=h; obtain ⟨C,c,p,Q⟩:=hp; let U i := Real.exp u*(1+C i)^u;have H1 : Soft τ U:=(soft_coin τ _).times (((soft_coin τ 1).plus c).pows u)
   have he i:0 ≤ U i:= by have := p i; unfold U; positivity
   refine ⟨_,H1.times b',fun i=>mul_nonneg (he i) (ht i),fun i q=> ?_⟩
   have hh:= H i q; have hD:=penn_move (x:=y i q) hh (Nat.cast_nonneg _); apply hD.mono; rw [mul_assoc (U i)]; apply mul_le_mul_of_nonneg_right _ hh.1
   rw [(Sable.grain (V i) (ε i)).turn]; apply (grain_up ..).trans;apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le; unfold Sable.gauge; exact pow_le_pow_left₀ (by positivity) (add_le_add_right (Q i q) 1) u
lemma grassier (hp:Mountain τ V ε x y)(h: Matched τ (fun i=> Sable.grain (V i) (ε i)) x (fun _=>u) δ b T S): Matched τ (fun i=>Sable.grain (V i) (ε i)) y (fun _=>u) δ b T S:= ⟨lowlands hp h.left, lowlands hp h.right,lowlands hp h.chalk⟩
lemma hills (hp:Mountain τ V ε x y)(h:Matched τ V x η δ b T S)(hs:∀ i,0<η i)(he:∀ i, ε i ≤1) (hk:Soft τ (fun i=> (η i)⁻¹))(u:ℕ): Matched τ (fun i=> Sable.grain (V i) (ε i)) y (fun _=>u) δ b T S:= grassier hp (stains hk hs he u h)
variable {w:∀ i:X,J i→R i}{Z T S U:∀ i:X,J i→ Waves (R i)}
lemma brushwood (hp: Mountain τ V ε x w)(h: Gilt τ V η δ q Q)(hs:∀ i,0<η i)(hS:Soft τ (fun i=>(η i)⁻¹))
    (hP:∀ i e r, e≤E →0<r → Matched τ V x η δ b (fun j p=>T j p i e r) (fun j p=>S j p i e r))(hQ:∀ i e r,e≤E →0<r → Matched τ V y η δ c (fun j p=>Z j p i e r) (fun j p=> U j p i e r))(hx:∀ i,ε i≤1) (hk:Chasm τ V η x y g)(i u e:ℕ)(he:e ≤ E) (m:ℕ): Matched τ (fun i=>Sable.grain (V i) (ε i)) w (fun _=>u) δ (fun i j=> b i j*c i j*g i j) (fun j p=> brawl (q j) (T j p) (Z j p) i e m) (fun j p=>brawl (Q j) (S j p) (U j p) i e m):= by
    refine hills hp (huddle h (fun i=>(hs i).le) hP hQ hk i e he m) (fun i=>half_pos (hs i)) hx ?_ u; convert (soft_coin τ 2).times hS using 1; ext i; simp [div_eq_mul_inv]
variable {b:I→∀ i:X,J i→ℝ}{x:I→ ∀ i:X,J i→ R i}{z:∀ i:X,J i→ R i}{T S:I→ ∀ i:X,J i→ Waves (R i)}
lemma remarries (s:List I)(p:I)(hk:Mountain τ V ε (x p) w)(h:Gilt τ V η δ q Q)(hs:∀ i,0<η i)(hS:Soft τ (fun i=>(η i)⁻¹))(hx: ∀ i∈s,Mountain τ V ε (x i) w)
    (hP:∀ j∈p::s,∀ i e r,e≤E →Matched τ V (x j) η δ (b j) (fun k n=>T j k n i e r) (fun k n=>S j k n i e r)) (hp:∀ i∈s, Chasm τ V η (x p) (x i) g)(he:∀ i,ε i≤ 1)(u i e r:ℕ)(hE:e≤E):
    Matched τ (fun i=>Sable.grain (V i) (ε i)) w (fun _=>u) δ (fun i j=> cartwork (p::s) b i j*g i j) (fun i' j=> scatter (q i') (T p i' j) (fun k=>T k i' j) s i e r) (fun i' j=>scatter (Q i') (S p i' j) (fun k=>S k i' j) s i e r):= by
   induction s generalizing i e r with
   | nil=> exact mates_void ..
   | cons j t ih =>
       have hU := hP p List.mem_cons_self; have hT :∀ k∈j::t,∀ i' e' r',e'≤E → Matched τ (fun i=>Sable.grain (V i) (ε i)) w (fun _=>u) δ (b k) (fun i j=> T k i j i' e' r') (fun i j=> S k i j i' e' r'):= fun k hh i e r hv=> hills (hx k hh) (hP k (List.mem_cons_of_mem _ hh) i e r hv) hs he hS u
       have hM:= curr (e:=e) (r:=r) (fun _:X=> Nat.cast_nonneg (α:=ℝ) u) (fun a b' c hb => brushwood hk h hs hS (fun a b c hg _=> hU a b c hg) (fun i e r hv _=> hP j (List.mem_cons_of_mem p (List.mem_cons_self)) i e r hv) he (hp j List.mem_cons_self) a u b' hb c) (company (fun _:X=>Nat.cast_nonneg u) t (fun i hi=> hT i (List.mem_cons_of_mem j hi))) i hE
       have hK:= curr (fun _:X=>Nat.cast_nonneg (α:=ℝ) u) (hT j List.mem_cons_self) (fun i e r he=> ih (fun a ht=>hx a (List.mem_cons_of_mem _ ht)) (fun a ht => hP a (by simp only [List.mem_cons] at *; tauto)) (fun a ht=>hp a (List.mem_cons_of_mem _ ht)) i e r he) i e r hE
       let f (i:X)(x:J i) := cartwork (p::j::t) b i x*g i x; have hx : (fun i k=> b p i k * b j i k*g i k*cartwork t b i k)=f:= funext fun i=>funext fun k=> by unfold f cartwork; simp;ring
       have hz :(fun i k=> b j i k*(cartwork (p::t) b i k*g i k))=f:=funext fun i=>funext fun k=>by unfold f cartwork;simp;ring
       rw [hx] at hM; rw [hz] at hK; exact hM.plus hK
lemma caravans (s:List I)(h:Gilt τ V η δ q Q)(hs:∀ i,0<η i)(hS:Soft τ (fun i=>(η i)⁻¹))(hx:∀ i∈s,Mountain τ V ε (x i) w)(hP:∀ j∈s,∀ i e r,e≤E →Matched τ V (x j) η δ (b j) (fun k n=>T j k n i e r) (fun k n=>S j k n i e r)) (hp:s.Pairwise (fun i j=> Chasm τ V η (x i) (x j) g)) (ht:∀ i,ε i≤1)(u i e r:ℕ)(he:e≤E): Matched τ (fun i=>Sable.grain (V i) (ε i)) w (fun _=>u) δ (fun i j=>cartwork s b i j*g i j) (fun x y=> collision (q x) (fun i=>T i x y) s i e r) (fun x y=>collision (Q x) (fun i=>S i x y) s i e r):= by
   induction s generalizing i e r with
   | nil=>exact mates_void ..
   | cons a L ih=>
       obtain ⟨A,hL⟩:= List.pairwise_cons.mp hp
       have H:= curr (fun (_:X)=>Nat.cast_nonneg (α:=ℝ) u) (fun i e r h=> hills (hx a List.mem_cons_self) (hP a List.mem_cons_self i e r h) hs ht hS u) (ih (fun _ h=>hx _ (List.mem_cons_of_mem a h)) (fun _ h=>hP _ (List.mem_cons_of_mem a h)) hL) i e r he
       have hv:(fun i k=> b a i k*(cartwork L b i k*g i k))=(fun i k=> cartwork (a::L) b i k*g i k):= funext fun i=>funext fun k=>by unfold cartwork; simp;ring
       rw [hv] at H; exact (remarries L a (hx a List.mem_cons_self) h hs hS (fun i ht=>hx _ (List.mem_cons_of_mem a ht)) hP A ht u i e r he).plus H
end YM.FormalBulk08.Basin
