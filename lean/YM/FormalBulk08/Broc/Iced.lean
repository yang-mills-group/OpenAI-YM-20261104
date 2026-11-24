import YM.FormalBulk08.Broc.Charge
import YM.Next.STATIONARY.Loops.Curvature

/-!
One first-grade lift. Q requests whether retain extra vanishing at rank two after
base. And a rank one residual must vanish. Linear constants pre-L.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Broc
open Function Filter Lattice RG Laurent Bloch Exterior Wilson
open Reef Lava Gorge Mesa Shore Lotus Orb Wick Series Jets PowerSeries North Cork City
open Stationary hiding shine Rays
open scoped Topology ENNReal Matrix BigOperators Classical ContDiff Matrix.Norms.Frobenius
def paradeS (i:ℕ):Side:=⟨i+1,Nat.succ_pos i⟩
lemma marching : Tendsto (fun i=> (paradeS i).val) atTop atTop:= tendsto_atTop_mono (fun i=>Nat.le_succ i) tendsto_id
variable {G:Gauge}{n:Side}{s:Signed}{r t e E:ℕ}{A σ:ℝ}
section hold
variable (hs:0<σ) {T:Pot G} (hB:Bail (fame _) σ (T e (t+1)) A)
   (H : Up (T e (t+1)))(U:Agate (T e (t+1)))(h: ∀ n,Charter (stone T n) E)(he:e≤ E)(hh:t<e+2)(hp:∀ n i,i<e→ coeff i (stone T n)=0)
include hs hB H U h he hh hp
lemma published : ∀ n, Recorded (pixel (T e (t+1))) (shadeK T e t n) 0:= (matched_iff (T e (t+1)) _ H hB hs.le).mp fun n=>local_receive T (h n) he hh (hp n) H U
lemma featured : Features (pixel (T e (t+1))) (σ/((t:ℝ)+1)) A:= by
    have hv n:= orbitPoint T (h n) he hh (hp n);exact withdrew marching (tendsto_const_nhds (x:=(0:ℝ))) (pitch _ hB hs) (F:=fun i=>shadeK T e t (paradeS i)) (fun i=>by rw [mul_zero]; apply published hs hB H U h he hh hp) (fun i=>(hv _).analytic) (fun i=>(hv _).stained) (fun i=>(hv _).guard) (fun i=> quietsK T (h _) he hh (hp _))
end hold
-- t indexed as m+1
lemma testified {T:Pot G} (hs:0<σ)(hB:Bail (fame _) σ (T e 2) A) (H: Up (T e 2))(U:Agate (T e 2))(h: ∀ n,Charter (stone T n) E)(he:e≤ E)(hp:∀ n i,i<e→ coeff i (stone T n)=0): TributeColor (pixel (T e 2)) (σ/(((1:ℕ):ℝ)+1)) A Universal:= by
    have hh:1<e+2:=by omega
    have hv n:= orbitPoint T (h n) he hh (hp n);exact tributing marching (pitch _ hB hs) (tendsto_const_nhds (x:=(0:ℝ))) (F:=fun i=>shadeK T e 1 (paradeS i)) (fun i=>by rw [mul_zero]; apply published hs hB H U h he hh hp) (fun i=>(hv _).analytic) (fun i=>(hv _).guard) (fun i=>(hv _).stained) (fun i=> quietsK T (h _) he hh (hp _)) (fun i s _=> (hv _).rotate s)
lemma goblets {T:Pot G}(hs:0<σ)(hB:Bail (fame _) σ (T e 2) A)(P: TributeColor (pixel (T e 2)) (σ/(((1:ℕ):ℝ)+1)) A Universal)(U:Agate (T e 2))(hG:G.Simple) (Q:Prop)(a:hue G)[Decidable Q](hz: Q→value a (T e 2)=0) (x i): Stationary.Rays ((if Q then 2 else 0)+2) (pixel (T e 2) x i ∘ axes):= by
    by_cases h:Q
    · rw [if_pos h]; apply P.vanish hG 1 0 (by decide) a
      have H:= lemon (T e 2) U ⟨_,_,hs,hB⟩ a; rw [hz h,Complex.ofReal_zero,neg_zero,mul_eq_zero] at H;exact H.resolve_left (by norm_num)
    rw [if_neg h]; obtain ⟨b,e⟩:= axisEquiv.surjective (i 0); obtain ⟨p,L⟩:=axisEquiv.surjective (i 1)
    rw [show i=![coord b,coord p] from funext fun k=> by fin_cases k <;> first| exact e.symm|exact L.symm]; exact roads_extent (P.crop_edict (fun _ _=>trivial) x b p)
section c
variable (G t) [NeZero t]
abbrev Bumps (t:ℕ)(Q: Prop)(f: Skin G t)[NeZero t]: Prop:= ∀ h:t=1,Q → Bs G (issue (cast (congr_arg (Skin G) h) f) (t:=1))
-- actual budget, normalization, match
structure Styled (T:Tile (edgeL G) (t+1))(Q:Prop)(σ A:ℝ)(R:Skin G t):Prop where
    coins : AtomWall (issue R) σ A
    bumps : Bumps G t Q R
    license : Matched T (fun n=> turnSeries (issue R) (m:=n))
variable {G t}
lemma sprawl {L:Tile (edgeL G) (t+1)}(f:∀ n,Link G n→ℝ)(H:∀ n,Pointwise (f n))(h:∀ n,Recorded (pixel L) (f n) 0)(e:Matched L f){g: Skin G t}(hs:0<σ)(hx:Shades g (pixel L) σ A)(Q:Prop)(hq:Bumps G t Q g): Styled G t L Q σ (A*inkCost G t σ) g := by
    obtain ⟨hh,hu⟩:= artery_funded hx;refine ⟨⟨hh,hu⟩,hq,fun n=>?_⟩
    rw [e n]; have he:= aperture_eq (colors_align (f n) (H n).analytic (H n).lights _ g hx hs (h n)); funext i; rw [beam,Tensor.coeff,he.symm]; rfl
end c
lemma regimen (G:Gauge)(hG:G.Simple)(hs:0<σ)(t:ℕ)[NeZero t]: ∃ δ K:ℝ, 0<δ ∧ 0≤K ∧ ∀ E e (T:Pot G) A,
   Bail (fame _) σ (T e (t+1)) A → Up (T e (t+1)) → Agate (T e (t+1)) →
   (∀ n,Charter (stone T n) E) → e ≤ E → t<e+2 → (∀ n i,i<e→coeff i (stone T n)=0) →
   ∀ Q:Prop,(Q → t=1 → ∀ a:hue G,value a (T e 2)=0) → ∃ R : Skin G t, Styled G t (T e (t+1)) Q δ ((A*K)) R := by
   let η:=σ/((t:ℝ)+1);have hp:0<η:= by unfold η; positivity
   by_cases h:t=1
   · subst t;obtain ⟨δ,K,hx,-,hK,B⟩:= Stationary.veins G η hp
     refine ⟨δ,K*inkCost G 1 δ,hx,mul_nonneg hK (inkCost_nonneg ..),fun E e T A hb hv ht h he hℓ hg Q hz=>?_⟩
     obtain ⟨a⟩:=nonempty_color hG; let X:=T e (1+1); let f:=shadeK T e 1; let V n:=orbitPoint T (h n) he hℓ (hg n); let hh:= testified hs hb hv ht h he hg; let k:= if Q then 2 else 0
     obtain ⟨R,hR,hY⟩:= B A k (pixel X) hb.1 hh.toFeatures (goblets hs hb hh ht hG Q a (fun hq=>hz hq rfl a))
     refine ⟨R,?_⟩;rw [←mul_assoc];apply sprawl f V (published hs hb hv ht h he hℓ hg) (fun n=>local_receive T (h n) he hℓ (hg n) hv ht) hx hR Q
     intro p hq i j S hS; have he: k=2:=if_pos hq; rw [he] at hY; exact issue_normal hR.price hx hY S hS i j
   obtain ⟨δ,K,hx,-,hK,B⟩:= strokes G t (by have hh:=NeZero.ne t;omega) η hp
   refine ⟨δ,K*inkCost G t δ,hx,mul_nonneg hK (inkCost_nonneg ..),fun E e T A hb hv ht hh he hl hg Q _=>?_⟩
   obtain ⟨R,hR⟩:= B A (pixel (T e (t+1))) hb.1 (featured hs hb hv ht hh he hl hg); rw [←mul_assoc]; exact ⟨R,sprawl _ (fun n=> orbitPoint T (hh n) he hl (hg n)) (published hs hb hv ht hh he hl hg) (fun n=> local_receive T (hh n) he hl (hg n) hv ht) hx hR Q (fun hx=> (h hx).elim)⟩
lemma level_nil {T:Pot G}(hG:G.Simple)(hs:0<σ)(hB:Bail (fame _) σ (T e 1) A)(h: ∀ n,Charter (stone T n) E)(he:e≤ E)(hh:Agate (T e 1))(H:Up (T e 1))(hp:∀ n i,i<e→ coeff i (stone T n)=0): T e 1=0:= by
   have hr:0<e+2:=by omega
   refine cum_cmp H (up_zero _) σ σ A 0 hs.le hs.le hB (bail_void ..) 0 fun n=> ?_
   rw [local_receive T (h n) he hr (hp n) H hh,cum_zero]; funext v; rw [beam,Tensor.coeff, point_quiet hG (orbitPoint T (h n) he hr (hp n)) 1 (by omega) Nat.one_pos,smul_zero]; rfl
end YM.FormalBulk08.Broc
