import YM.Contacts.Junction.Opus
import YM.Contacts.Allium.Ferment
/-!
# finite-period post stencil powers exchange
 Clocks fixed rank losses uniform in setting. No rooted scalar channel bound used. No winding assumptions beyond sewn nonconstant vertices.
 -/
noncomputable section
set_option autoImplicit false
namespace YM.Contacts.Allium
open Function Finset Filter Lattice Wilson RG Pressure
open PhysicalNext.Repeat Pulse Loom Milling House
open ConnectedActivityE6 Blaze Blaze.March PertExtension.Series Radial Next.Scheduling -- Radial namespace
open Ion Junction Junction.Provision Capture Current Meter Resetter
open scoped Topology NNReal BigOperators ContDiff Classical
variable {k n j e i:ℕ}
section sort
variable {α:Type}[Fintype α]
open PowerSeries
-- Jets are nonconstant only; comparisons never require pressure cost of ℓ rank zero.
def rank (F:House α) (k r:ℕ)(x:ℝ× House.Dir α):= ∑ i∈ Finset.range (k-r), x.1^i * grate F i r x.2
lemma collect (F:House α)(k:ℕ)(x:ℝ×House.Dir α): Radar.gap (swell F k) x=∑ r∈ (Finset.range k).erase 0,rank F k r x:= by
    rw [gap_exit]; let P(i r:ℕ):= x.1^i*grate F i r x.2; let S:=Finset.range k; let T:=S.erase 0; let Q(i r:ℕ):=if 0<r ∧ i+r<k then P i r else 0; change (∑ i∈S,_)=∑ r∈T,_;
    have hh i(i':i∈ S): x.1^i * (∑ j∈Finset.range (k-i), if 0<j then grate F i j x.2 else 0)=∑ r∈T,Q i r:= by
        let U:= (Finset.range (k-i)); rw [Finset.mul_sum]; refine Eq.trans ?_ ((sum_subset (f:=fun r=>Q i r) (erase_subset_erase (a:=0) (Finset.range_mono (Nat.sub_le k i))) ?_)) 
        · have hz:= sum_subset (f:=fun r=> Q i r) (Finset.erase_subset 0 U) (s₂:=U) (fun r hr he=> show Q i r=0 from if_neg fun x=> he (mem_erase.mpr ⟨x.1.ne',hr⟩)); rw [hz]; apply sum_congr rfl; intro j hj; unfold Q P; have hv:= mem_range.mp hj; split_ifs <;> first| rfl| omega| simp
        intro r hr h'; apply if_neg; intro H; simp only [T,mem_erase,S,mem_range] at *; omega
    rw [sum_congr rfl hh,sum_comm]; refine sum_congr rfl fun r hr=>?_ ; unfold rank; apply Eq.symm; rw [sum_congr rfl (fun i (hi:i∈Finset.range (k-r))=>?_ )]; exact sum_subset (f:=fun i=> Q i r) (Finset.range_mono (Nat.sub_le ..)) (fun i hi ht=> if_neg (by simp only [Finset.mem_range] at ht; omega))
    exact (if_pos (by simp only [T,mem_erase,S,mem_range] at *; omega) : Q i r=P i r).symm
-- recapture+ ticker film
lemma design_pay (F:House α)(x:House.Dir α)(i e:ℕ) : design (dazzle F i e) x= grate F i e x:= by unfold dazzle grate; split; rfl; exact Forge.parcel_nil x
lemma parcelSum (F:House α)(x:House.Dir α)(u:Resetter.Pow) (hu:Resetter.Uniform u)(i e:ℕ)(k:ℕ)(hi:i<k):
    grate F i e x=∑ j∈Finset.range k, pin (u*(PowerSeries.X*(Resetter.rotate u))^j) i * grate (lowerHouse u F) j e x := by
    rw [← sum_subset (f:=fun j=> pin _ i*grate _ j e x) (Finset.range_mono (Nat.succ_le_of_lt hi)) ?_]; swap; · intro j hj ht; rw [charter u hu,if_neg (by simp only [mem_range] at ht; omega),zero_mul]
    rw [← design_pay F x i e,rehouse u F hu]; simp_rw [← design_pay (lowerHouse u F)]; rw [design_spec]; simp_rw [Finset.sum_apply, Pi.smul_apply,smul_eq_mul, Finset.sum_mul]; rw [sum_comm]; apply sum_congr rfl; intro j _; rw [design_spec, mul_sum]; exact sum_congr rfl (fun i _=>mul_assoc ..)
lemma rankFilm (F: House α)(w:ℝ)(x:House.Dir α)(u:Resetter.Pow)(hu:Resetter.Uniform u)(k e:ℕ):
   rank F k e (w,x)=∑ j∈Finset.range (k-e), ((∑ i∈ Finset.range (k-e), pin (u*(PowerSeries.X*(Resetter.rotate u))^j) i * w^i) * grate (lowerHouse u F) j e x) := by
   unfold rank; rw [sum_congr rfl (fun i hi=>show _=w^i* _ from congr_arg (w^i* ·) (parcelSum F x u hu i e _ (mem_range.mp hi)))]; simp_rw [Finset.mul_sum,sum_mul]; rw [sum_comm]; apply sum_congr rfl; intro j hj; apply sum_congr rfl; intro i _; ring
lemma design_sub (F V:House α)(x:House.Dir α)(i j:ℕ) : grate (F-V) i j x= grate F i j x-grate V i j x:= by
    unfold grate; split; · simp only [design_spec,Pi.sub_apply, sub_mul, Finset.sum_sub_distrib];
    simp
lemma subtract (F V:House α)(x:ℝ×House.Dir α): Radar.gap (swell (F-V) i) x= Radar.gap (swell F i) x - Radar.gap (swell V i) x := by simp_rw [collect,rank,design_sub,mul_sub,Finset.sum_sub_distrib]
end sort

open Flux
variable {N: Meter}{b:Stream}{U:ℕ→Resetter.Pow}
variable {I V γ:ℕ→Type}[∀ i, Fintype (I i)][∀ i, NormedAddCommGroup (V i)][∀ i, NormedSpace ℝ (V i)]
variable {Y:∀ i,House (I i)}{Φ:Shelf V γ (fun i=>House.Dir (I i))}{p:ℝ}{x:Frame γ V}
lemma honor (_h:Y=Y)(r:ℕ)(i j:ℕ)(X:House.Dir (I i)): jet (grate (Y i) j r) r X=grate (Y i) j r X:= (radiant (grate_ana ..) r r (design_scale (Y i) j r) X).trans (if_pos rfl) 
lemma parcel (h:Spectrum N k Y p)(hf: Budget N x n fit Φ)(i j:ℕ)(hp:i+j<k+3)(he:j≠0): Budget N x n (fit*j+p) (fun i' f=>grate (Y i') i j ∘ Φ i' f):= by
    by_cases hh:2≤ i+j; swap
    · exact Arms.cheaper (show (0:Mint V γ)=(fun z f=>grate (Y z) i j ∘ Φ z f) from (by funext _ _ _; exact (if_neg hh).symm)) Budget.zero
    rcases j with _|j; · contradiction
    let j':=j+1; let q i':= grate (Y i') i j'; obtain ⟨Z,hZ,heX⟩:= (h.pays i j' (by omega) (by omega)).cap
    let l i:= (Fintype.card (I i):ℝ)* Z i; have hz: N.Rush p (fun i=> normJ j' (q i) 0):= Current.jetBudget (H:=l) ?_ ?_
    rotate_left;
    · exact heX.mono fun r hr=> ⟨grate_ana .., fun z=> by rw [show jet (q r) j' z= _ from honor (Y:=Y) rfl j' r i z]; unfold grate; rw [if_pos hh]; exact Model.tail_price (Range.cheap _) _ hr.2⟩
    · exact h.card.times hZ (zero_add _)
    refine Arms.cheaper ?_ ((Budget.jetcap hf hz).lo ?_ le_rfl)
    · funext i' f v; exact honor rfl j' i' i _
    · linarith
section collage
open Coat
variable {S T:∀ i, House (I i)}
local notation "H" => (fun i:ℕ=> lowerHouse (U i) (T i))
local notation "Y'" => (gStep ∘ b)
local notation "R" => (groom (gStep ∘ b) (k+3) U)
local notation "tβ" => (appeal b (k+3) U)
local notation "Z" => (gStep ∘ (appeal b (k+3) U))
-- analytic sum over pin.Event uniform.
def put (k:ℕ)(S:∀ i, House (I i))(b:Stream)(X:Shelf V γ (fun i=>House.Dir (I i))): Mint V γ:=fun i n y=> Radar.gap (swell (S i) k) (b i,X i n y)
def putr (k r:ℕ)(S:∀ i, House (I i))(b:Stream)(X:Shelf V γ (fun i=>House.Dir (I i))): Mint V γ:=fun i n y=> rank (S i) k r (b i,X i n y)
abbrev invest (b:Stream)(A:Mint V γ): Mint V γ:= fun i n z=> b i*A i n z
variable (hb:Foil b N) (hv:Live U N (k+3))(hu:∀ᶠ i in atTop, Resetter.Uniform (U i)∧QuietPower (U i))
variable (ht:Budget N x n Capture.fit Φ) (hS: Spectrum N k Y 0)(hY:∀ᶠ i in atTop,Y i=lowerHouse (U i) (T i))
include hb hu hv ht hS hY
lemma collage (he:e<k+3) (hh:e≠0): Budget N x n (Capture.fit*(k+3)) (invest (fun i=>(R i)⁻¹^(2:ℕ)) (putr (k+3) e Y (Z) Φ) - putr (k+3) e T Y' Φ):= by
   let u:=k+3-e; let V:= (tβ); let P:= (PowerSeries.X:Resetter.Pow); let f (j:ℕ)(i:ℕ):Resetter.Pow:= U i*(P* Resetter.rotate (U i))^j; let b₁:Stream:= fun i=> (R i)⁻¹^2;
   let F(i:ℕ):Stream:= b₁*(Z)^i-logit Y' u (f i)
   let S(j:ℕ):Mint _ γ:= invest (F j) (fun i w=> grate (Y i) j e ∘ Φ i w); have hf(j:ℕ):N.Rush (grade u) (F j):= by
       refine ((Flux.warp hb.fare.2 hv (by omega) (hu.mono (fun i hi=>hi.1)) (by omega:0<u) (by omega: u≤k+3) j).price).take ?_; filter_upwards [hb.trans (k:=k+3) (by omega) hv hu] with i hi; unfold F; change b₁ i*((Z) i)^j-_= b₁ i*(Y' i* R i)^j-logit Y' _ _ i; rw [show Z i= _ from hi.2.2.2,mul_comm (Y' i)]; rfl
   refine Arms.confirm (h:=?_) (Budget.rush (Finset.range u) S (fun i hi=>?_))
   · filter_upwards [hu,hY] with i hi hy; funext j y; rw [Finset.sum_apply,Finset.sum_apply,Finset.sum_apply]; let X:=Φ i j y;
     change b₁ i*(∑ j∈Finset.range u,(Z i)^j * grate (Y i) j e X)- rank (T i) (k+3) e (Y' i,X)= ∑ z∈Finset.range u,(b₁ i*(Z i)^z - _) * _
     rw [rankFilm (T i) _ _ (U i) hi.1,← hy,Finset.mul_sum, ←Finset.sum_sub_distrib]; apply sum_congr rfl; intro i _; rw [sub_mul, mul_assoc]; rfl
   have hp:= (parcel hS ht i e (by have he:= mem_range.mp hi; omega) hh).weighted (hf i) rfl; refine hp.lo ?_ le_rfl; unfold Flux.grade; unfold fit u; rw [Nat.cast_sub (show e≤k+3 from he.le)]; push_cast; have h:=(by exact_mod_cast he.le : (e:ℝ) ≤ ((k+3:ℕ):ℝ)); push_cast at h; linarith
-- Index against pre wound stencil startup, projected λ.
lemma full_rank : Budget N x n (1+fit*(k+3)) (invest tβ (put (k+3) Y (Z) Φ)- invest b (put (k+3) T Y' Φ)):= by
   let A(e:ℕ): Mint V γ:= invest (fun i=>(R i)⁻¹^2) (putr (k+3) e Y (Z) Φ)- putr (k+3) e T Y' Φ; let S:=(Finset.range (k+3)).erase 0;
   refine Arms.cheaper ?_ (Arms.weighted (Budget.rush S A (p:=fit*(k+3)) (fun i hi=>collage hb hv hu ht hS hY (mem_range.mp (mem_erase.mp hi).2) (mem_erase.mp hi).1)) hb.fare.1 (add_comm _ _))
   ext z p x; simp only [A, Pi.smul_apply,Finset.sum_apply, Pi.sub_apply, invest,putr,put,smul_eq_mul, collect]; change _= b z* ((R z)⁻¹^2)* _- b z*_; rw [sum_sub_distrib,mul_sub,← mul_sum,← mul_assoc] -- chose sum
lemma ringlet (hp:Spectrum N k (T-S) (fit*(k+3))) : Budget N x n (1+ fit*(k+3)) (invest tβ (put (k+3) Y (Z) Φ) - invest b (put (k+3) S Y' Φ)):= by
   have h:Budget N x n 0 (fun i j z=>(Y' i, Φ i j z)):= Budget.stack (Budget.tally _ (hb.fare.2.mono (by norm_num))) (ht.lo (by norm_num [fit]) le_rfl)
   have hb':Budget N x n (fit*(k+3)) (put (k+3) (T-S) Y' Φ):= gap_shield h hp
   apply Arms.cheaper _ (Arms.sum (full_rank hb hv hu ht hS hY) (hb'.weighted hb.fare.1 (add_comm _ _))); funext i j h; simp only [Pi.add_apply,Pi.sub_apply, Pi.smul_apply,invest,put,smul_eq_mul, subtract]; ring
end collage
end YM.Contacts.Allium
