import YM.RegulatorIR.Oracle.Vellum

/-! Extend payments to joint layer. Use public constructor deterministic
Clock.Leg; `Rates` includes χ.Bill on Addon jets (not on growing ranks k automatically).
-/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Oracle
open Function Finset Lattice Laurent Bloch Set Filter Budget Spatial Budget.Packet Budget.Tuple Budget.Layer Quadratic Quarry Sources Tree Tree.Forest PertExtension Geometry Geometry.Field
open Exterior RG Wilson Matrix Halo Profiles Push Precision Prim Clocks Series Series.Radial Series.Tested Diagram Diagram.Formal PowerSeries YM.RegulatorIR.Step YM.RegulatorIR.Ledger YM.RegulatorIR.Ledger.Sky Taping Uniform
open scoped Topology ENNReal NNReal BigOperators Classical Matrix Matrix.Norms.Frobenius PowerSeries
variable {X Y W V I:Type} {M:X→ℕ} {n:Page M→Side} {K:KernelChoices} {k p:ℕ}
section joint
variable {K:Tariff V}{F:W → V}{L:Y→V}{A:Layer W W}{B:Layer W Y}{C:Layer Y W}{D:Layer Y Y}{a b c d:ℝ≥0∞}
lemma halo_p {f: W⊕Y→ℝ}{g:W⊕Y→ℝ≥0∞} : quota f g=quota (f ∘ Sum.inl) (g ∘ Sum.inl)+quota (f ∘ Sum.inr) (g ∘ Sum.inr):=by
 let u (x:W ⊕ Y):=‖f x‖ₑ * g x
 let l(x:W⊕Y):ℝ≥0∞:=x.elim (u ∘ Sum.inl) (fun _=>0)
 let r(x:W⊕Y):ℝ≥0∞:= x.elim (fun _=>0) (u ∘ Sum.inr)
 unfold quota; change (∑' x,u x)=_;rw [tsum_congr (g:=fun x=>l x+r x) (fun i=>by cases i <;> simp [l,r]), ENNReal.tsum_add]
 have hl : (∑' x:W, l (Sum.inl x))=∑' x,l x := Function.Injective.tsum_eq Sum.inl_injective (fun z h=>by cases z with
   | inl a=>exact ⟨a,rfl⟩
   | inr i=>exact (h rfl).elim)
 have hh : (∑' x:Y, r (Sum.inr x))=∑' x,r x:= Function.Injective.tsum_eq Sum.inr_injective (fun z h=>by cases z with
   | inl i=> exact (h rfl).elim
   | inr i=>exact ⟨i,rfl⟩)
 rw [← hl, ← hh]; rfl
lemma halo_led (ha:Layer.row A K F F a)(hb:Layer.row B K F L b)(hc:Layer.row C K L F c)(hd:Layer.row D K L L d): Layer.row (glued A B C D) (K.uses (Sum.elim F L)) id id (max (a+b) (c+d)):=by
 rintro (x|x) <;> rw [halo_p]
 · exact (add_le_add (ha x) (hb x)).trans (le_max_left ..)
 exact (add_le_add (hc x) (hd x)).trans (le_max_right ..)
lemma mirror_led : Function.swap (glued A B C D)=glued (Function.swap A) (Function.swap C) (Function.swap B) (Function.swap D):= by ext1 i; ext1 j; cases i <;> cases j <;> rfl
lemma row_dark {f: V→ I}{K:Tariff I}{g:X→I}: Layer.row 0 K f g 0:=fun _=> (quota_zero _).le
lemma row_identity : Layer.row (ID W) K F F 1:=by intro i;unfold quota; rw [tsum_eq_single i];simp [ID,K.own];intro y hy;simp [ID,hy.symm]
lemma row_core (h:Layer.row B K F L b)(hh:Layer.row (Function.swap B) K L F b): Layer.row (hoses B) (K.uses (Sum.elim F L)) id id (max b 1) ∧ Layer.row (Function.swap (hoses B)) (K.uses (Sum.elim F L)) id id (b+1):=by
 constructor
 · simpa only [zero_add] using! halo_led (A:=0) (C:=0) row_dark h row_dark row_identity
 unfold hoses; rw [mirror_led]; have ht:Function.swap (ID Y)=ID Y:=by ext1 i;ext1 j; simp [Function.swap,ID,eq_comm]
 rw [ht]
 simpa only [add_zero,sup_eq_right.mpr (zero_le (a:=b+1))] using! halo_led (A:=0) (B:=0) row_dark row_dark hh row_identity
lemma row_wing (h:Layer.row A K F F a): Layer.row (petals (I:=Y) A) (K.uses (Sum.elim F L)) id id a:=by
 simpa only [add_zero,max_eq_left (zero_le (a:=a))] using! halo_led (B:=0) (C:=0) (D:=0) h (L:=L) (hb:=row_dark) (hc:=row_dark) (hd:=row_dark)
lemma row_heals {a b:ℝ≥0∞}(h : Layer.row A K F F a)(hb:a≤b):Layer.row A K F F b:=fun x=>(h x).trans hb
end joint
namespace Circuit
variable (S:Circuit M n)(Y:Program K)(G:Gauge)(Z:∀ P:Patch,P.Branches K G) (t:Page M→Binding.Scale)
local notation "A"=>S.dialect Y G Z t
local notation "T"=>S.lane Y G Z t
variable (P: Meter X)(H:Credit S Y G Z t P k p)
include H
lemma lens_u : Beam (flapL M P) ((A).ceilingRoom.cone k) (A).lifts.lineL :=by
 refine ⟨_,H.rayS,fun i=>?_⟩
 have hz:= S.honored Y i.prev
 let θ:= S.pactP i; let L:= (T).pulses i;let l:= S.l i.prev;let m:= S.l i.next;have he:m=l* θ.L.val:= S.width_s i
 let k':= Tariff.native m (S.l_p _) k
 have hv : Layer.row L k' (fm G l) (fm G l) _:= reels θ K G _ (l:=l) (S.l_p _) he (S.l_p i.next) (q:=k) hz.card (Z _)
 let X:= k'.uses (Sum.elim (fm G l) (fm G m)); have hp:Function.swap (petals (I:=Foot G) L)=petals L:=by rw [petals,mirror_led,show Function.swap L = L from t_warm θ K G _ hz.card (Z _)]; rfl
 refine ⟨row_wing (L:=fm G m) hv,?_⟩
 change Layer.row (Function.swap (petals L)) X id id _;rw [hp]; exact row_wing hv
lemma projector_u : Beam (flapL M P) ((A).ceilingRoom.cone k) (A).lifts.forecast:=by
 have hp:= H.projection
 refine ⟨_,hp.add (g:=fun _=>1) (Uniform.Poly.oneQ _),fun i=>?_⟩
 let H0:= S.honored Y i.prev; let L:= S.sails Y G i
 let m:=S.l i.next; let l:=S.l i.prev; let K':=Tariff.native m (S.l_p i.next) k
 obtain ⟨hv,hc⟩:=tilts (S.pactP i) K G _ (S.predicted Y i).rows H0.card.paid H0.card.pos (q:=k) (S.l_p i.prev) (S.width_s i) (S.l_p i.next)
 have ht:=row_core hv hc; refine ⟨ht.2,?_⟩; exact row_heals (F:=id) (K:=K'.uses (Sum.elim (fm G l) (fm G m))) ht.1 (max_le le_self_add le_add_self)
omit H in
lemma pull_z {L Q:Side}{P':Patch}(t: StepData L Q)(he:t.patch=P')(hb:t.kernel=K)(hh:Q=L*P'.L){q:Binding.Scale}{T': Branchix→Orders (KFoot G)}(B:Prim.Sphere t (bios t) q T') (i j) {l r:ℝ}(h:0<l)(hv:r=l*P'.L.val)(ht:0<r): localQ ((Tariff.native r ht k).uses (peak_o G l r)) (many T' i j) (valor q i*archive P' K G (Z _) i j k):=by
 subst Q; have he':t=avenue P' K L:=by obtain ⟨a,b,c⟩:= t; change a=P' at he; change b=K at hb; subst a;subst b;rfl
 subst t; exact financed P' K G (Z P') B h hv ht i j -- stemF rfl
lemma grants_c (i j)(ht:i≤p): Workday (flapL M P) ((A).ceilingRoom.cone k) (fun f:Flap M=> (A).lifts.rails f i j):=by
 by_cases h : j ≤ i + 2
 · have he:Uniform.Poly (flapL M P) (fun w=> valor (t w.prev) i):= Uniform.Poly.add (Uniform.Poly.oneQ _) (Uniform.Poly.sum _ _ fun a ha=> H.clockV a ((Nat.le_of_lt_succ (mem_range.mp ha)).trans ht))
   refine ⟨_,he.mul (H.wall i j ht h),fun w f x=>?_⟩
   have hp : localQ ((Tariff.native _ (S.l_p w.next) k).uses (peak_o G (S.l w.prev) (S.l w.next))) (many (S.bore G Z t w) i j) _:= pull_z G Z (P':=S.pactP w) (S.rail K w) rfl rfl (S.seats w) (S.wheeled G Z t w) _ _ (S.l_p _) (S.width_s w) (S.l_p _)
   exact hp f x
 refine ⟨_,Uniform.Poly.zeroQ _,fun w=>?_⟩
 have he:= Halo.essential T w; change localQ _ (((A).frames w).addon i j) 0
 rw [show ((A).frames w|>.addon i j)=0 from ?_];exact local_zero _
 by_contra hv; exact h (he _ j hv).2
lemma paid_full : Halo.Aug.Amenities A P p k:=⟨lens_u S Y G Z t P H,projector_u S Y G Z t P H,fun i hi j=> grants_c S Y G Z t P H i j hi⟩
end Circuit
end YM.RegulatorIR.Oracle
