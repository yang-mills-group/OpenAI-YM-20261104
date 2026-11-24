import YM.FormalBulk08.Elm.Knoll
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Elm
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Clover Dove
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
variable {G:Gauge}{K:KernelChoices}{X:Type}{E e R d D m n l r:ℕ}{o:Loc G 1}
variable {A:Page X}{P:Pin A}{θ α:ℝ}{η:Deck P→ℝ}{T: Deck P→Studio D→Tile (edgeL G) r}
-- arbitrary multiplier g(x) nonnegative: may buy prepared top residual on
-- far contexts. generalize upcoming
lemma tenderLift {Y:Type}{τ:Time X}{s:Time Y}{p:X→Y}(e:Soft τ (fun i=> s.day (p i))){T:Y→ Studio D→ Tile (edgeL G) r}{σ g:Y→ℝ}(h:Tender s o σ g T): Tender τ o (fun i=>σ (p i)) (fun i=>g (p i)) (fun i=>T (p i)):= by
   obtain ⟨C,hc,V,U⟩:=h; exact ⟨_, town_fold (g:=p) e hc,fun i=>V _,fun i f=> U (p i) f⟩

lemma stip (h:Years A)(hv:0<θ) (w:Nextpay o (Dove.tide P) (fun i=>η i.ups) (fun i=>η i.bed) (Turn.rad θ) (fun _=>1) r (fun i=> T i.ups) (fun i=> T i.bed))
   (hx:Tender ((sage P).reach (peak P)) o (fun i=>η (peak P i)) (fun _=>1) (fun i=> T (peak P i))): Tender (sage P) o η (fun _=>1) T:= by
   let f(x:Deck P)(b:ℝ):Prop:=∀ p, Knoxville (fame _) (η x) (0,o) (T x p) (b*‖p‖)
   obtain ⟨C,hC,hc,H⟩:=w; obtain ⟨B,b,hB,Q⟩:=hx; have he(i:X):f (peak P i) (B i):= fun p=> by simpa only [one_mul] using Q i p
   have ht (x:Turn P)(Z:ℝ)(h:f x.ups Z)(p:0≤Z): f x.bed (Turn.rad θ x*Z+C x):= by intro i;simpa only [mul_one] using H x Z p h i
   obtain ⟨C',c,P',W⟩:=upward (f:=f) h hv (fun i A hp B h p=>(hp p).mono (mul_le_mul_of_nonneg_right h (norm_nonneg _))) b he hC ht
   exact ⟨_,c,P',fun i p=>by simp only [one_mul];exact W i p⟩
lemma targe (h:Years A)(hp:θ<α)(hx:θ≤1)(w:Nextpay o (Dove.tide P) (fun i=>η i.ups) (fun i=> η i.bed) (Turn.rad α) (Dove.bump θ) r (fun i=> T i.ups) (fun i=> T i.bed))
   (he:Tender ((sage P).reach (peak P)) o (fun i=>η (peak P i)) (fun _=>1) (fun i=> T (peak P i))): Tender (sage P) o η (Dove.Degree θ) T:= by
   obtain ⟨B,b,t,Y⟩:= he; obtain ⟨K,k,c,hK⟩:=w
   let g (x:Turn P):= (((A.mesh x.a).block x.b).val:ℝ); have hu:Soft (Dove.tide P) g:= h.blocks.reach (fun x:Turn P=>x.toLeaf)
   let f(x:Deck P)(b:ℝ):Prop:=∀ p, Knoxville (fame _) (η x) (0,o) (T x p) ((b*Dove.Degree θ x)*‖p‖)
   have hv x:f (peak P x) (B x):= by
       have he: Dove.Degree θ (peak P x)=1:= by unfold Dove.Degree ratioR; rw [show (peak P x).a=x from rfl,show (peak P x).b= P.N x from rfl,div_self ((A.mesh x).a_pos _).ne',Real.one_rpow]
       intro p; rw [he,mul_one]; simpa only [one_mul] using Y x p
   have ht (x:Turn P)(Z:ℝ)(h:f x.ups Z)(q:0≤Z): f x.bed (Turn.rad (α-θ) x*Z+K x*g x):= by
       let V:=Degree θ x.ups; let U:=Degree θ x.bed;have hp:0<V:=ratioR_pos ..; have he:0<U:=ratioR_pos ..
       have hv:= hK x (Z*V) (mul_nonneg q hp.le) h; intro p; apply (hv p).mono; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _);change Turn.rad α x*(Z*V)+K x*V≤ (Turn.rad _ x*Z+K x*g x)* U
       have hh:Turn.rad α x*V=Turn.rad (α-θ) x*U:= adjusted _ _ _ _ _
       obtain ⟨M,hM,u,H⟩:=adjust_rate (A.mesh x.a) hx x.b (P.N x.a); have hU : V=M*U:= H; rw [add_mul, mul_left_comm _ Z,hh,mul_left_comm Z (Turn.rad _ x),mul_assoc (Turn.rad (α-θ) x) Z]; apply add_le_add_right; rw [mul_assoc,hU];exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right u he.le) (c _)
   obtain ⟨C,c,H,R⟩:= upward h (sub_pos.mpr hp) (f:=f) (fun i A hp B h p=>(hp p).mono (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h (ratioR_pos ..).le) (norm_nonneg p))) b hv (k.times hu) ht
   exact ⟨C,c,H,fun i p=> by rw [←mul_assoc];exact R i p⟩

-- actually induction across rank weight
lemma avenues (F:Frame G d)(E:ℕ)(P : Letter F→ℕ→ℕ→Prop)(h:∀ i j k,j≤E→ k≤ j+slots F i →(∀ p m n,itinerary F i j k p m n→ n≤m+slots F p→ P p m n)→ P i j k) : ∀ i j k,j≤E → k≤ j+slots F i → P i j k := by
    intro i j k he hg
    induction j using Nat.strong_induction_on generalizing i k with
    | _ j ih=>
      -- lex inner: slots, j+slots-k, d-weight
      generalize ha : slots F i=e
      induction e using Nat.strong_induction_on generalizing i k with
      | _ e ht =>
        generalize hx : j + Pose.slots F i - k=r
        induction r using Nat.strong_induction_on generalizing i k with
        | _ r hr=>
          generalize hb: d- Pose.weight F i=z
          induction z using Nat.strong_induction_on generalizing i k with
          | _ z hz=>
             apply h i j k he hg;intro p m n hv hW
             obtain hp|⟨rfl,hV⟩:=hv
             · exact ih m hp p n (hp.le.trans he) hW
             obtain hl|⟨hl,hP⟩:= hV
             · exact ht (Pose.slots F p) (hl.trans_eq ha) p n hW rfl
             obtain hh|⟨rfl,hS⟩:= hP
             · exact hr (m+ Pose.slots F p-n) (by omega) p n hW (hl.trans ha) rfl
             exact hz (d-Pose.weight F p) (by have hh:=Pose.weightFits F p; omega) p k hW (hl.trans ha) (by rw [hl,hx]) rfl
end YM.FormalBulk08.Elm
