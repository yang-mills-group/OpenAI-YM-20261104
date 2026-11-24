import YM.FormalBulk08.Aster.Jet

/-! Absolute and transparent dust estimates. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Aster
open Lattice Laurent Bloch RG Precision Wilson Orb Reef City Filter Function Series Wick Jets Stationary Lotus Shore Lava Gorge Mesa Cork Wine Flat Glide Bank Work.F08 Next.Free Chapel Rift PowerSeries
open scoped Topology ENNReal BigOperators Classical
variable {G:Gauge} {K:KernelChoices} {X:Type} {E e r m n:ℕ}
variable {j t:X→ℕ}(F:∀ x:X,Flight (j x) (t x)) (U:∀ x:X,Lodge (F x).patch)(H:∀ x:X,(F x).patch.Branches K G)(D L:∀ i:X,Train (j i))
variable (τ:Time X) (σ η ω:X→ℝ)
structure TermPrice (G:Gauge)(K:KernelChoices)(E:ℕ) :Prop where
   merit : ∃ A Q:X→ℝ, Soft τ A ∧ Soft τ Q ∧ (∀ i,Teller G (η i) (A i)) ∧ (∀ i,Bail (fame _) (η i) (ham F D G K i) (Q i)) ∧ ∀ m:ℕ,1≤m→ m+1≤ E+2 → ∃ R:X→ℝ, Soft τ R ∧ ∀ i,Pledge G K (graded F D i) (U i) (σ i) (η i) (A i) (Q i) (ω i) (R i) m
   pegs : ∀ e≤ E,∀ m,1≤m→m+1≤ E+2 → ∃ P:X→ℝ, Soft τ P ∧ ∀ i,Angler G (σ i) (P i) e m
variable {ρ:ChartRatio G}{F U H D L τ σ η ω}{δ:X→ℝ}{T M:X→Pot G}(w:Freight F U ρ K τ σ η E)(c:Canvas F U H τ D L η δ)(l:Honest F U K G D τ η H)(hp:LocalRatio ρ)(hh:∀ i,4≤ t i)(hT:∀ i,FrameV (T i) (pink K.penalty (D i)))(p:TermPrice F U D τ σ η ω G K E)
include w hp hh hT p l
lemma direct_line (a:hue G)(he:0<e)(hx:e≤ E)(hr:1≤r)(hz:r+1≤ e+2) (hU:floor_cost τ σ T e (r+1)):
     ∃ C:X→ℝ,Soft τ C ∧ (∀ i,0≤C i) ∧ ∀ x B,Bail (fame _) (σ x) (T x e (r+1)) B→ Bail (fame _) (η x) (taxi ρ a (graded F D x) (U x) (H x) (T x) e (r+1)) (ω x*B+C x) := by
   obtain ⟨A,Q,hA,hQ,P,Z,K1⟩:=p.merit; obtain ⟨B,hB,H1⟩:= K1 _ hr (le_trans hz (by omega)); obtain ⟨J,hJ,Y⟩:= p.pegs _ hx _ hr (by omega)
   let W(x:X):=risePath (graded F D x) (U x) G K (T x e (r+1)); let V(x:X):=manure ρ a (graded F D x) (U x) (H x) (T x) e (r+1)
   have ht x:=(hT x).toStory; have ht':Cost τ (fun _=> fame _) η V := (manured w (l.mock (δ:=fun _=>0)) (fun _=>le_rfl) hp hh ht ht P hA a hx he hz (fun b m q z _ hx=> Totem.constant (hU b m q z hx)) 0).left
   obtain ⟨C,b,M⟩:=ht'; obtain ⟨Y1,p,Q1⟩:= purse_here hJ Y (fun i=>authoritative (ht i)) (fun i=>(ht i).agate e (r+1)) (fun i=>(ht i).civil e (r+1)) (fun k hk l u _ => floorCost_lower hU (fun i=>(ht i).toVivid) k l u (Or.inl hk))
   obtain ⟨Y2,q,e2,U2⟩:= l.zeal
   let R(x:X):= 1+A x*Q x;have hR: Soft τ R:=(soft_coin τ 1).plus (hA.times hQ)
   have hX:Soft τ (fun i=> |B i *Y1 i+R i*C i|):=((hB.times p).plus (hR.times b)).radius
   refine ⟨_,hX,fun i=> abs_nonneg _,fun x bN hN=>?_⟩
   have hx:=route_at a (graded F D x) (U x) (H x) hp (hh x) _ (ht x) he 0 (w.output x).le (w.coverage x) hN (e2 x) (U2 x); rw [hx]
   obtain ⟨D',z,L⟩:=(H1 x).shop _ ((ht x).civil e (r+1)) ((ht x).agate e (r+1)) (frame_valence (hT x) he) _ _ hN (Q1 x); apply (limits _ _ _ (P x) (Z x) (z.add (M x))).mono; change R x*(D'+ C x) ≤ _; rw [mul_add]; refine (add_le_add_left L (R x*C x)).trans ?_; rw [add_assoc]; gcongr;exact le_abs_self _

omit w hp hh hT p l in
lemma agate_sub {Y:Type}{T U:Tile Y n}(h:Agate T)(p:Agate U):Agate (T-U):=fun v s=> by simp only [Pi.sub_apply,h v s,p v s]
omit w hp hh hT p l in
lemma up_sub {I:Type}{T U:Tile (Biglot I) n}(h:Up T)(p:Up U):Up (T-U):=fun v s=> by simp only [Pi.sub_apply,h v s,p v s]
omit l
variable (a:hue G)(he:0<e)(hx:e≤E)(hr:1≤r)(hz:r+1≤e+2)
include he hx hr hz c
lemma dusting (h0:∀ i,0≤δ i) (hs:G.Simple) (hM:∀ i,FrameV (M i) (pink K.penalty (L i))) (hU:floor_dust τ σ δ T M e (r+1))(hT':Cost τ (fun _=> fame _) σ (fun i=>T i e (r+1)))(hM':Cost τ (fun _=> fame _) σ (fun i=>M i e (r+1))) (hV: Dust τ (fun _=> fame _) η δ (fun i=>ham F D G K i-ham F L G K i)):
     let W:= fun x=> T x-M x
     ∃ C:X→ℝ, Soft τ C ∧ (∀ i,0≤C i) ∧ ∀ x B,Bail (fame _) (σ x) (W x e (r+1)) B→ Bail (fame _) (η x) (taxi ρ a (graded F D x) (U x) (H x) (T x) e (r+1) - taxi ρ a (graded F L x) (U x) (H x) (M x) e (r+1)) (ω x*B+C x*δ x) := by
   intro W; obtain ⟨A,Q,hA,hQ,P,Z,K1⟩:= p.merit; obtain ⟨B,hB,H1⟩:= K1 r hr (by omega); obtain ⟨J,hJ,Y⟩:=p.pegs _ hx _ hr (by omega)
   let L1 x:=risePath (graded F D x) (U x) G K (T x e (r+1));let L2 x:= risePath (graded F L x) (U x) G K (M x e (r+1)); let u x:=risePath (graded F D x) (U x) G K (M x e (r+1)); let v x:=manure ρ a (graded F D x) (U x) (H x) (T x) e (r+1); let t x:=manure ρ a (graded F L x) (U x) (H x) (M x) e (r+1)
   obtain ht := rise_paid w c h0 (T:=M) (M:=M) (e:=e) (r:=r+1) 0 (Totem.constant hM')
   have hv i:=(hT i).toStory; have hp' i:=(hM i).toStory; obtain hw := manured w c h0 hp hh hv hp' P hA a hx he hz (fun b m q z _ hx=> hU b m q z hx) 0
   obtain ⟨C',z,hR⟩:= Cost.plus (T:=L1) (U:=v) (rise_paid w c.left.mock h0 0 (Totem.constant hT') |>.left) hw.left; have ht':Cost τ (fun _=> fame _) η (fun x=> L2 x+t x):= ht.right.plus hw.right
   obtain ⟨C,c',ch,Z1⟩:=ht.nebula.plus hw.nebula; obtain ⟨V,hX,v',W1⟩:= limiter_diff a hA P hV ht'; obtain ⟨B1,b1,hZ⟩:=ht'
   have ha i: Agate (W i e (r+1)) := agate_sub ((hT i).agate e (r+1)) ((hM i).agate e (r+1)); have hQ i: Up (W i e (r+1)):= up_sub ((hT i).civil e (r+1)) ((hM i).civil e (r+1))
   obtain ⟨Y1,p',Y',Q1⟩:= dusty_here h0 hJ Y (fun i=>authorized_sub (authoritative (hv i)) (authoritative (hp' i))) ha hQ (fun j hj k hk _=> (floorDust_lower hU (fun i=>(hv i).toVivid) (fun i=>(hp' i).toVivid) j k hk (Or.inl hj)).nebula)
   let R(x:X):=1+A x*Q x; have ht:Soft τ R:=(soft_coin τ 1).plus (hA.times ‹Soft τ Q›)
   let X1(x):= B x * Y1 x+R x*C x+V x; obtain ⟨A',a',C1⟩:=hT'; obtain ⟨K2,q,q'⟩:=hM'
   obtain ⟨D1,t1,d1,hk⟩:= c.left.zeal; obtain ⟨D2,t2,d2,H2⟩:= c.right.zeal
   refine ⟨fun x=>|X1 x|,(((hB.times p').plus (ht.times c')).plus hX).radius,fun _=>abs_nonneg _,fun x bN hN=>?_⟩
   have hα:=w.output x; have hβ:=w.coverage x
   rw [route_at a (graded F D x) (U x) (H x) hp (hh x) _ (hv x) he 0 hα.le hβ (C1 x) (d1 x) (hk x), route_at a (graded F L x) (U x) (H x) hp (hh x) _ (hp' x) he 0 hα.le hβ (q' x) (d2 x) (H2 x)]
   let M1:= ham F D G K x;let R1:= risePath (graded F D x) (U x) G K (W x e (r+1)); have he' : L1 x-u x= R1:= rise_split (graded F D x) (U x) 0 hα.le hβ (C1 x) (q' x) (d1 x) (hk x)
   obtain ⟨E,X2,H3⟩:= (H1 x).shop _ (hQ x) (ha x) (valed_sub (hT x) (hM x) he a hs) _ _ hN (Q1 x)
   have hg: Bail (fame _) (η x) (L1 x+v x-(L2 x+t x)) (E+C x*δ x):= by
       have hh : L1 x+v x-(L2 x+t x)=R1+(u x - L2 x +(v x-t x)):= by rw [←he'];abel
       rw [hh]; exact X2.add (Z1 x)
   have hw: Bail (fame _) (η x) (limiter a M1 (L1 x + v x)-limiter a M1 (L2 x+t x)) (R x*(E+C x*δ x)):=by rw [limiter_shift a M1 (hR x) (hZ x) hα]; exact limits _ _ _ (P x) (Z x) hg
   change Bail (fame _) (η x) (limiter a M1 (L1 x+v x)-limiter a (ham F L G K x) (L2 x+t x)) _; rw [←sub_add_sub_cancel _ (limiter a M1 (L2 x+t x))]; apply (hw.add (W1 x)).mono; rw [mul_add]; calc
       _ ≤ (ω x*bN+B x*(Y1 x*δ x)+ R x*(C x*δ x))+V x*δ x:= add_le_add_left (add_le_add_left H3 _) _
       _ = ω x*bN+X1 x*δ x:= by unfold X1;ring
       _ ≤ _ := add_le_add_right (mul_le_mul_of_nonneg_right (le_abs_self _) (h0 x)) _
end YM.FormalBulk08.Aster
