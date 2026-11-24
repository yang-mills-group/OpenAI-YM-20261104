import YM.Work.A01.Support
import YM.XSpace.Fabric
/-!
# All moments with Gram variables agree for ANY rotation/filtration-candidate
which preserves local-position array and fixes the found quadratic fields

Still in the stabilizer proof, no data except the free scheme.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Sample
open Function Set Filter MeasureTheory MvPolynomial Maxwell Maxwell.Free Maxwell.Wick
open Next.Rank.Normal Traverse Legs
open scoped BigOperators Topology Classical ContDiff

variable {G : Gauge} {d n : ℕ} (R : WickPol G→ WickPol G)
structure Moves (d : ℕ) : Prop where
  fits (p) : p∈shellSector G d → R p ∈ shellSector G d
  quad (p:Flavor 0) : R (team G p p)=team G p p
  arrays (n : ℕ) (x : Points n) (p : Fin n→ WickPol G) : x∈conf n→ (∀ i,p i∈shellSector G d)→moment G x (fun i=> R (p i))= moment G x p

variable {R} (K : Moves R d) {x:Points n} (p : Fin n → poly (Paint G)) (A:E4 → TaylorTower G)
def plot (x:Points n): Finset E4:=Finset.univ.image (fun i=> x i)
lemma occupation (x:Points n): product x p∈Room G (plot x):= Subalgebra.prod_mem _ fun i _=> simple_room (p i) (Finset.mem_image_of_mem _ (Finset.mem_univ _))
lemma growing (z:E4) : plot (Points.cons z x)=insert z (plot x):=by
  ext i; simp only [plot,Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_insert]; constructor
  · rintro ⟨v,hv⟩; refine Fin.cases (fun h=>Or.inl h.symm) (fun i h=> Or.inr ⟨i,h⟩) v hv
  rintro (rfl| ⟨v,hv⟩); exact ⟨0,rfl⟩; exact ⟨v.succ,hv⟩
include K in
lemma Silent_of (q: Fin n→poly (Paint G)) (hpq : ∀ i, R (send (p i))=send (q i)) (hx : x∈conf n)
    (hp : ∀ i,send (p i)∈shellSector G d) (hd : 4≤d): Silent (plot x) (product x q-product x p):=by
  intro k; induction k generalizing n with
  | zero=> refine .stop _ _ ?_; rw [map_sub, delivered x hx,delivered x hx, sub_eq_zero]; simpa only [hpq] using K.arrays _ x (fun i=> send (p i)) hx hp
  | succ k ih=>
    apply Loc.sharp; intro z u hu; let y:=Points.cons z x; let a:=Legs.quad (G:=G) u
    rw [mul_sub, ← growing z (x:=x), ← quad_play, ← product_cons,← product_cons]
    refine ih (p:=Fin.cons a p) (q:=Fin.cons a q) (fun i=>Fin.cases ?_ (fun i=>hpq i) i) (Work.A01.conf_cons hx (fun i h=> hu (h ▸ ?_))) (fun i=>Fin.cases ?_ (fun i=>hp i) i)
    · change R (send a)=send a; rw [show send a=team G u u from quad_team u]; exact K.quad u
    · exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    · change send a∈ _; rw [show send a=team G u u from quad_team u]; exact team_label _ _ hd

lemma profile_rain {S : Finset E4} (e:G.ColorIndex) {P : Pol G} (he : P∈Room G S) (r : ℝ) (n : ℕ) (H : Silent S P):
    Snow.credit r (bill A) n P=0:=by
  let T:= P.vars; let h := T.sup fun i=> i.2.1.1
  have hT : Good S h T := fun i hi=> ⟨mem_supported.mp he hi,Finset.le_sup (f:=fun i:World G=>i.2.1.1) hi⟩
  have hp : P ∈ Lap.scope T:= mem_supported_vars P
  have hy : ∀ k:ℕ, ((Lap.op T (Snow.grams (bill A)))^k) P∈ Rain S T:=by
    intro k; induction k with
    | zero => exact silent_rains e hp he H
    | succ k ih=> rw [pow_succ']; exact rain_fields e (bill_rich A hT) hT ih
  obtain ⟨n,hn⟩:=(Snow.credit_agrees r (bill A) n T hp).exists
  rw [hn,Snow.h_score]; exact Finset.sum_eq_zero fun i _=> by rw [rain_eval e hT (hy i),smul_zero]

variable (C₀:G.ColorIndex) (f:Fin n→ WickPol G) (r : ℝ) (l : ℕ)
include K C₀ in
lemma reading (h : x∈conf n) (hp : ∀ i,f i∈shellSector G d) (hd:4≤d):
    (∫ K: Fabric G,Snow.point r l K • ∏ i, probe (motor (pump K) (A (x i))) (f i))=
    ∫ K: Fabric G,Snow.point r l K • ∏ i, probe (motor (pump K) (A (x i))) (R (f i)):=by
  let p i:= enroll (f i); let q i:= enroll (R (f i))
  have he:= profile_rain A C₀ (he:=Subalgebra.sub_mem (Room G (plot x)) (occupation q x) (occupation p x)) r l
    (Silent_of K p q (by simp [p,q]) h (by simpa [p]) hd)
  rw [map_sub,sub_eq_zero] at he; simp_rw [← read_product]; exact he.symm

include K C₀ in
lemma moment_agreement (X : Fin n → TaylorTower G) (hp : ∀ i,f i∈shellSector G d) (hd:4≤d):
    (∫ K: Fabric G,Snow.point r l K • ∏ i, probe (motor (pump K) (X i)) (f i))=
    ∫ K: Fabric G,Snow.point r l K • ∏ i, probe (motor (pump K) (X i)) (R (f i)) :=by
  let x := points (n:=n) fun i=> (i.val:ℝ) • basis 0
  have h : x ∈ conf n:= by
    intro i j ht; apply Fin.ext; have he : (i.val:ℝ)=(j.val:ℝ):= smul_left_injective ℝ (show basis 0 ≠0 from norm_pos_iff.mp (by simp)) ht
    exact_mod_cast he
  let A:= Function.extend x.ofLp X (fun _=>0)
  rw [show X=(fun i=> A (x i)) from funext fun i=> (Function.Injective.extend_apply (show Injective x.ofLp from h) X _ i).symm]; exact reading K A C₀ f r l h hp hd
end YM.XSpace.Sample
