import YM.Pert.First.OneArray
import YM.FormalOPE.RG10.Gazebo.Aisle
/-! Frame/read derivative equations port for finite square choice. In the already accepted
position-solve coordinates; we won't ask for invertibility on actual fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Gazebo
open Function Maxwell Labels Extraction Filter Finset Extra.FD PertExtension MeasureTheory
  Topology Metric PertExtension.Position PertExtension.Physical PowerSeries Triangle Matrix
open RG10.Position RG10.Position.Grade Deck Shutters
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}{F:Frames G}{d k:ℕ}(h:d≤k)
local notation "π'"=> climb F h
local notation "𝓥" d=> Deck F d
local notation "𝓕" d=> FrameAt (Deck F d) ℝ
local notation "𝒩" d=> tents F d
local notation "α"=>PertExtension.Physical.Profile.n
local notation "ℳ" d=> Mark (Deck F d) (PertExtension.Physical.Profile.n)
local notation "ins" d=> PertExtension.Position.insert (Deck F d) (PertExtension.Physical.Profile.n)

abbrev raw (F: Frames G) (d:ℕ) : Mark (Deck F d) PertExtension.Physical.Profile.n→ℝ:= Physical.free (L:=Maxwell.standard F) (deck F d)
abbrev pulse {I:Type*}(A:FrameAt I ℝ) i j:= PowerSeries.C (Physical.diag I i j)+PowerSeries.C (A i j)*PowerSeries.X
def beam (v:ℳ d): (𝒩 d) →ₗ[ℝ] ℝ where
 toFun A := ∑ i,∑ u:(Deck F d), raw F d (⟨v.1,update v.2 i u⟩) * A.val (v.2 i) u
 map_add' _ _:= by simp only [AddMemClass.coe_add,Pi.add_apply, mul_add,sum_add_distrib] -- name
 map_smul' c x:= by simp only [SetLike.val_smul,Pi.smul_apply,smul_eq_mul, RingHom.id_apply,Finset.mul_sum, mul_left_comm _ c] -- names

private lemma leak {I J:Type*}[Fintype I][Fintype J][DecidableEq I]
 (a:I→J)(f:I→J→ℝ)(g:(I→J)→ℝ) (i:I): ∑ p : I→J, g p * (f i (p i) * ∏ j∈ univ.erase i, Physical.diag J (a j) (p j)) = ∑ u:J,g (update a i u) * f i u := by
 let x(u:J):= update a i u; have hx:Injective x:= fun j k hk=> by simpa [x] using congr_fun hk i
 let G(p:I→J):= g p * (f i (p i)*∏ j∈univ.erase i,Physical.diag J (a j) (p j))
 change ∑ p:I→J,G p=_
 rw [← sum_subset (f:=G) (subset_univ (Finset.image x univ)) ?_, sum_image hx.injOn]
 · apply sum_congr rfl; intro j _; unfold G x; rw [update_self,prod_eq_one,mul_one]
   intro k hk; simp [Physical.diag,update_of_ne ((mem_erase.mp hk).1)]
 intro p hp hy
 have he:∃ j,j≠i ∧ a j≠p j:= by
   by_contra! ht; exact hy (mem_image.mpr ⟨p i,mem_univ _,funext fun j=>by unfold x; by_cases h:j=i; subst j; simp; rw [update_of_ne h,ht j h]⟩)
 obtain ⟨j,hj,hh⟩:=he; unfold G; rw [Finset.prod_eq_zero (mem_erase.mpr ⟨hj,mem_univ _⟩) (by simp [Physical.diag,hh]),mul_zero, mul_zero]
lemma ray_force (v:ℳ d)(B:𝒩 d) : coeff 1 ((ins d) (PowerSeries.C ∘ raw F d) (pulse B.val) v)= beam v B:= by
 unfold PertExtension.Position.insert; simp only [map_sum,Function.comp_apply, coeff_C_mul];
 let I:=Fin v.1.n; have hh (f:Fin (PertExtension.Physical.Profile.n v.1)→fps) : coeff (R:=ℝ) 1 (∏ i:Fin (PertExtension.Physical.Profile.n v.1), f i)=∑ i:I, coeff 1 (f i) * ∏ j ∈ univ.erase i, constantCoeff (f j):= Pert.First.first_product f univ
 simp_rw [hh]; simp only [pulse,map_add,map_mul,constantCoeff_C,constantCoeff_X, mul_zero,add_zero,coeff_C_mul,coeff_C, Nat.one_ne_zero, ↓reduceIte, coeff_one_X, mul_one,zero_add, Finset.mul_sum]; rw [sum_comm]; apply Finset.sum_congr rfl; intro k _; exact leak v.2 (fun i u=> B.val (v.2 i) u) (fun p=>raw F d ⟨v.1,p⟩) k

lemma glowing_p {J:Type*}(w:J→ℕ) : glass w (Physical.diag J)= Physical.diag J:= by
 ext i j; by_cases h:i=j
 · subst j; simp [glass,Physical.diag,lapse,pow_add,lap_twice]
 simp [glass,Physical.diag,h]
lemma glass_phase (A:𝒩 d) : glass (Deck.slots F d) (pulse A.val)= pulse ((mode d A).val):= by
 let w:= Deck.slots F d; let b:= A.val
 funext i j; have he (c:ℝ):lapse (S:=fps) (w i+w j)*C c=PowerSeries.C (lapse (S:=ℝ) (w i+w j)*c):=by simp [lapse]
 unfold glass pulse; rw [mul_add,←mul_assoc,he,he,show lapse _ * Physical.diag (Deck F d) i j= _ from congr_fun₂ (glowing_p w) i j]; rfl
lemma twirl (A:𝒩 d)(P:Plan F) : glow α (Deck.slots F d) (fun i=>beam i A) = fun i=> beam i (mode d A):= by
 let g (i:ℳ d):=PowerSeries.C (raw F d i); let w:=Deck.slots F d
 have he : glow α w g=g:= by
   funext i; change lapse (S:=fps) _ * C (raw F d i)=_; unfold g; rw [← show PowerSeries.C (lapse (S:=ℝ) (Shutters.slots α w i))= lapse (Shutters.slots α w i) by simp [lapse],← map_mul]; exact congr_arg _ (Shutters.intake (G:=G) 3 P (by decide) i)
 let K:= (ins d) g (pulse A.val)
 funext i; simp_rw [← ray_force];
 exact (before α (Deck.slots F d) K 1 i).symm.trans (by unfold K; rw [← posed α w,he,glass_phase]; rfl)

lemma clip_pulse (A:𝒩 k) : clip π' (pulse A.val)=pulse ((ρ h A).val):= by ext i j : 2; simp only [clip,pulse,Physical.diag,(Deck.climb_inj F h).eq_iff]; by_cases h:i=j <;> simp only [h, ↓reduceIte] <;> rfl
lemma pulse_lowers (B:𝒩 k) : lowers π' (pulse B.val):= by
 let H:= no_pass h ((votes _).1 (pinned B.val |>.1 B.property).1).1
 intro i j hj; rw [pulse,show Physical.diag _ (π' i) j=0 from if_neg (fun hu=> hj ⟨i,hu⟩), map_zero, show B.val (π' i) j= _ from H i j hj,map_zero,zero_mul,add_zero]

theorem clip_beam (B:𝒩 k): (fun i=>beam i B) ∘ ascend α π'= fun i=> beam i (ρ h B):= by
 funext i; simp only [Function.comp_apply]; rw [← ray_force,← ray_force,promote α π' _ _ _ (Deck.climb_inj _ h) (pulse_lowers h _), clip_pulse]; rw [show (⇑C ∘ raw F k) ∘ ascend α π'= _ from ((congr_arg (fun b=> (PowerSeries.C (R:=ℝ)) ∘ b) (Plan.fresh_clips (F:=F) h)).symm)] -- may need full RHS
end YM.FormalOPE.RG10.Gazebo
