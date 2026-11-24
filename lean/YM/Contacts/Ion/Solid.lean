import YM.Contacts.Ion.Vertical
namespace YM.Contacts.Lyre
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Kale Garf PertExtension.Series Radial Larch Ion Convoy Lumen Resetter Shuttle.Tide
open Procession Procession.Welcome Procession.Catch Procession.Sun Procession.Lotus Procession.Hinges Procession.Xenon
open Shuttle.Pigment Prairie Harrier Sequent
open scoped Classical Topology BigOperators NNReal Matrix ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}{b c d g:ℝ}{X Y A B ι κ α β: Type}{m:Side}{n k i r l j M D:ℕ}{ζ σ:ℝ≥0}
open UVNext PricedKernels Next.Free Lattice Tree FreeResolvent
open UVNext PricedKernels
open scoped Classical
set_option autoImplicit false
open Tree FreeResolvent
section singular
variable [Fintype ι][Fintype α][Fintype β]
-- fidelity to metric distances to sing-set demanded through pending stepped rooted estimate. We use x→−x as distance only. This particular norm omits costs of diameter between arbitrary singular-neighbors.
structure Posts (Λ:α→ℝ)(F:Field ι α)(b:ℝ) : Prop where
    cash : (∑ x, ‖F x‖)≤ b
    pose (i:ι): (∑ x, Λ (x i)*‖F x‖)≤ b
variable {Λ:α→ℝ}{F P:Field ι α} {a a' v:ℝ}
-- weighted sum estimate composition finitely supported Φ maps at every valence.Jet work
variable (hf: Posts Λ F b)(he:∀ i,0 ≤ Λ i)
include hf
lemma Posts.good : 0 ≤ b:= (Finset.sum_nonneg fun _ _=> norm_nonneg _).trans hf.cash
lemma Posts.smul (t:ℝ): Posts Λ (t • F) (‖t‖*b):= by
   constructor
   · simp_rw [Pi.smul_apply,norm_smul,← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hf.cash (norm_nonneg _)
   intro i; simp only [Pi.smul_apply,norm_smul]; simp_rw [mul_left_comm _ ‖t‖, ← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (hf.pose i) (norm_nonneg _)
lemma Posts.reorder [Fintype κ](e:ι≃κ): Posts Λ (Pulse.reorder e F) b:= by
    let p:= Equiv.arrowCongr e (Equiv.refl α); have he (x:ι→α): Pulse.reorder e F (p x)= F x:= by simp [Pulse.reorder,p,Function.comp_def]
    constructor; · rw [← Equiv.sum_comp p]; simp_rw [he]; exact hf.cash
    intro i; rw [← Equiv.sum_comp p]; simp_rw [he]; exact hf.pose _
omit hf
include he
lemma Posts.sum {F:X→Field ι α}{b:X→ℝ}(s:Finset X) (h:∀ i∈s, Posts Λ (F i) (b i)) : Posts Λ (∑ i∈s,F i) (∑ i∈s,b i):= by
    constructor; · simp_rw [Finset.sum_apply]; apply (Finset.sum_le_sum fun i _=> norm_sum_le ..).trans; rw [sum_comm]; exact Finset.sum_le_sum fun i hi=> (h i hi).cash
    intro i; simp_rw [Finset.sum_apply]; refine (Finset.sum_le_sum fun x _=> mul_le_mul_of_nonneg_left (norm_sum_le ..) (he (x i))).trans (?_); simp_rw [Finset.mul_sum]; rw [sum_comm]; exact Finset.sum_le_sum fun j hj=> (h j hj).pose i
include hf
lemma Posts.print : Posts Λ (printRun F) b:= by
   refine Eq.mp (?_: Posts Λ (Pulse.printRun F) (_:ℝ) = Posts Λ _ b) ((Posts.sum (Λ:=Λ) he (Finset.univ (α:= Equiv.Perm ι)) (fun i _=> hf.reorder i)).smul ( (Fintype.card (Equiv.Perm ι):ℝ)⁻¹)); simp
omit he
-- raw payment for SINGLE transfer, no structural invariance required. n distinct sizes.
variable {p':β→ℝ}{g:α→β→ℝ}(hL:∀x:α,∑ i, ‖g x i‖ ≤ c)(hp:∀ x:α, (∑ i,p' i*‖g x i‖)≤ Λ x*c)(hw:∀ i,0≤p' i)(hc:0≤c)
include hL hp hw hc
lemma step_pure (ξ:ι→α)(i: Option ι) : (∑ x:ι→β,i.elim 1 (p' ∘ x)* ∏ j:ι,‖g (ξ j) (x j)‖) ≤ i.elim 1 (Λ∘ ξ)*c ^ Fintype.card ι:= by
   let d(j:ι)(x:β):= if i=some j then p' x else 1; let e(j:ι)(x:β):= d j x*‖g (ξ j) x‖; let b(j):= if i= some j then Λ (ξ j) else 1; have ht: (∏ j:ι,b j)=i.elim 1 (Λ ∘ ξ):= by cases i with| none=>simp [b]|some i=> simp [b] -- Fintype.prod_ite
   have h(x:ι→β): (∏ j:ι,d j (x j))=i.elim 1 (p'∘ x):= by cases i with| none=>simp [d]|some i=>simp [d]
   simp_rw [← h,← Finset.prod_mul_distrib,← ht]; change (∑ x:ι→β, ∏ j:ι,e j (x j)) ≤_; calc
       _ = ∏ i:ι,∑ t:β,e i t := (Fintype.prod_sum ..).symm
       _ ≤ ∏ j:ι,(b j*c) := by
          have hf(j):0≤ ∑ t:β,e j t:= Finset.sum_nonneg fun i _=> mul_nonneg (by unfold d; split; exact hw _; exact zero_le_one) (norm_nonneg _); refine Finset.prod_le_prod (fun i _=> hf i) (?_); intro j _; by_cases he':i=some j; · simpa only [e,d,b,if_pos he'] using hp (ξ j)
          simpa only [e,d,b,if_neg he',one_mul] using hL (ξ j)
       _ = _:= by rw [Finset.prod_mul_distrib,Finset.prod_const,card_univ]
lemma Posts.affection : Posts p' (Pulse.allAt (fun _=>g) F) (b*c ^ Fintype.card ι):= by
   suffices hv:∀ i:Option ι,(∑ x:ι→β,i.elim 1 (p'∘x)*‖allAt (fun _=>g) F x‖) ≤ b * c ^ Fintype.card ι by exact ⟨(by simpa only [Option.elim_none, one_mul] using hv none),fun i=>hv (some i)⟩
   intro i; let d: (ι→β)→ℝ:= fun v=> i.elim 1 (p'∘v); let L:(ι→α)→ℝ:= fun v=> i.elim 1 (Λ∘v); let t:=c ^ Fintype.card ι; have hu(v):0≤d v:= by cases i with| none=>exact zero_le_one|some i=>exact hw (v i)
   have H : (∑ v:ι→α,‖F v‖* L v)≤b:= by cases i with| none=> simpa only [L,Option.elim_none,mul_one] using hf.cash|some i=> unfold L; rw [show (∑ v:ι→α, ‖F v‖* (some i).elim 1 (Λ∘v))= ∑ v:ι→α,Λ (v i)*‖F v‖ from sum_congr rfl fun v _=> mul_comm ..]; exact hf.pose i
   unfold allAt; simp_rw [tsum_fintype]; refine (Finset.sum_le_sum fun x _=> mul_le_mul_of_nonneg_left (norm_sum_le ..) (hu x)).trans (?_); simp_rw [Finset.mul_sum, norm_mul,norm_prod]; rw [sum_comm]; refine le_trans (b:=(∑ v:ι→α,‖F v‖* L v)*t) (?_) (mul_le_mul_of_nonneg_right H (pow_nonneg hc _)); rw [Finset.sum_mul]; refine Finset.sum_le_sum fun u hu=> ?_; rw [mul_assoc ‖F u‖]; simp_rw [mul_left_comm _ ‖F u‖,← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (step_pure (F:=F) hf hL hp hw hc u i) (norm_nonneg _)
end singular
namespace Soil
variable (e:Parcel G)(s: Parcel.Step)(p:Parcel.Word)(n:Side)
variable (he:2*ζ ≤ e.reach)
abbrev singular (ζ:ℝ≥0)(p: Co m α):=aging ζ p.1
lemma holiday_light :0≤holiday e (e.reach:ℝ):= trFee_nonneg _ _ e.tax_pos.le -- perhaps implicit
include he
-- pay every factor of inherited torus defect (spaces first, then weight) stage
lemma allowances (x:Lines G (n*s.L) 1): let A:= Lyre.output e p s n; (∑ j,singular ζ j*‖A x j‖) ≤ singular ζ x*holiday e (e.reach:ℝ):= by
    intro A; let q:= (e.traveler s n).ratio; let L:ℝ:=s.L.val; let t(y):= gained ((e.reach:ℝ)/L) x.1 (q.embed y); let hp:= treasury e p s n x; refine le_trans (b:= singular ζ x * (∑ j:Lines G n 1, t j.1*‖A x j‖)) (?_) (mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le); rw [Finset.mul_sum]; refine Finset.sum_le_sum (fun i _=> (mul_le_mul_of_nonneg_right (Lyre.split_pre q i.1 x.1 he) (norm_nonneg (A x i))).trans_eq (mul_assoc ..))
omit he in
lemma basic (x: Lines G (n*s.L) 1): (∑ j, ‖Lyre.output e p s n x j‖) ≤ holiday e (e.reach:ℝ):= by have he:2*(0:ℝ≥0) ≤ e.reach:= (by rw [mul_zero]; exact bot_le); let u:= allowances e s p n he x; simp only [singular, aging,gained,NNReal.coe_zero,zero_mul,Real.exp_zero,one_mul] at u; apply u
theorem defense (F:Field (Fin k) (Lines G (n*s.L) 1))(h: Posts (singular ζ) F b): Posts (singular ζ) (Milling.Forge.hoist (Lyre.output e p s n) F) (b*(holiday e (e.reach:ℝ))^k) := by have hT:= @Fintype.card_fin k; rw [show b*(holiday e (e.reach:ℝ))^k = b*(holiday e (e.reach:ℝ))^Fintype.card (Fin k) from (by rw [Fintype.card_fin])]; exact Posts.print (Posts.affection h (basic e s p n) (allowances e s p n he) (fun x=> (Real.exp_pos _).le) (holiday_light e)) (fun x=> (Real.exp_pos _).le) -- fix
end Soil
end
end YM.Contacts.Lyre
