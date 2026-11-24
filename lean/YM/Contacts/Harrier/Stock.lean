import YM.Contacts.Harrier.Charge
namespace YM.Contacts.Harrier
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Kale Garf PertExtension.Series Radial Larch Ion Convoy Lumen Resetter Shuttle.Tide
open Procession Procession.Welcome Procession.Catch Procession.Sun Procession.Lotus Procession.Hinges Procession.Xenon
open Shuttle.Pigment Prairie
open scoped Classical Topology BigOperators NNReal Matrix ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}{b c d g:ℝ}{X Y A B ι κ α β: Type}{m:Side}{n k h i r l j M D:ℕ}{ζ σ:ℝ≥0}
namespace Transfer
open Parcel Prairie Planned.PrimaryIntegral295
variable {e:Parcel G} {p:Word}{s:Parcel.Step}{S:Boom} (T:e.License S ζ)(hp:OK S p)(hs:s∈S)
open Barrage.Reserve.Oasis
variable (x:Dye G) {v:Site s.L}
-- Demand: request i+ℓ+upper bounds on powers from $q$ service and tick calculation
abbrev Demand (S: Boom)(e:Parcel G)(M i:ℕ):= enough (e.floorGoal 3 (M+3*i+5)) S
-- use large i.E(s) attached.H.Bul.A.Frame.Local
variable {K:ℕ}(hT:Demand S e M K)
local notation "Γ" => terrain ζ (Dye G)
local notation "Υ" => terrain (2*ζ) (Dye G)
abbrev bump (e:Parcel G)(p:Word)(s:Parcel.Step)(v:Site s.L)(i r n k:ℕ)(F:Sketch G): Ribbon (Dye G) r:= lum s e p (curb s v) (dart i k) (i-n) n k r F (foot s v)
abbrev lead (e:Parcel G)(p:Word)(s:Parcel.Step)(v:Site s.L)(i r:ℕ)(F:Sketch G): Ribbon (Dye G) r:= bump e p s v i r i r F
variable {V:Sketch G} (hi:i≤K)(he:r≤M+i)
-- omit
lemma lift_formula (e:Parcel G)(p:Word)(s:Parcel.Step)(v:Site s.L)(T:e.License S ζ)(hp:OK S p)(F:Sketch G)(i M r:ℕ): sail (weigh e p s M v F) i r= ∑ n∈ Finset.range (i+1),∑ k∈ Finset.range (M+n+1), bump e p s v i r n k F:= by
   funext x; simp only [Finset.sum_apply]; exact Theater.plow_offset M i r (crafts e p s T hp) .. -- omit automatic variables clash?
omit hp
include T hs hT hi
lemma bumped (r:ℕ)(h':n≤ i)(k':k ≤ M+n): Spent D x ζ M Υ S (fun Q t=> Enroll Γ D x Q n k t) (fun p F=> bump e p s v i r n k F):= beacon T hs hT x n k r (by unfold dart; omega:i-n < dart i k) (by unfold dart; omega) (by unfold Demand at hT; unfold dart; omega) _ (desk_tick ..) _
include he
local notation "Ω-" => Harrier.Before Γ D x
local notation "Ω" => Issued Γ D x
lemma lead_bill : Spent D x ζ M Υ S (fun Q t=> Ω Q i r t) (fun p F=> lead e p s v i r F):= (bumped T hs x hT hi r le_rfl he).restrict (fun _ _ _ _ h=> h.2)
lemma when_less : Spent D x ζ M Υ S (fun Q t=> Ω- Q i r t) (fun p F=> sail (weigh e p s M v F) i r-lead e p s v i r F):= by
    let f i':= Finset.range (M+i'+1); let R:= (f i).erase r; let V(n k:ℕ)(p:Word)(F:Sketch G):= bump e p s v i r n k F; let A':=fun F t=> Harrier.Before Γ D x F i r t
    have hu (n:ℕ)(hn:n∈ Finset.range i): Spent D x ζ M Υ S A' (fun p F=>∑ k∈ f n,V n k p F):= by
       apply Spent.total _ (fun k=>V n k); have hn:= Finset.mem_range.mp hn; intro k hk; exact (bumped T hs x hT hi r hn.le (Nat.le_of_lt_succ (Finset.mem_range.mp hk))).restrict (fun F _ _ _ h=> h n k (Or.inl hn))
    have hh(k:ℕ)(hk:k∈R) : Spent D x ζ M Υ S A' (V i k):= by
       obtain ⟨hl,hk⟩:= Finset.mem_erase.mp hk; have hk:= Nat.le_of_lt_succ (Finset.mem_range.mp hk); by_cases hp:r<k; · exact (bumped T hs x hT hi r le_rfl hk).restrict fun F _ _ _ h=> h i k (Or.inr ⟨rfl,hp⟩)
       refine Spent.zero.cast (fun p F hF heq=>?_ ); obtain ⟨a,b,Q,h'⟩:= permits e p s T heq hs; let Z:=crafts e p s T heq
       funext x; let f:= desk s v x; let H':= F f; obtain ⟨H,W,h⟩:= hF.lineage f; exact Theater.dropping (T:=Z) h' (step_reserved ..) (h.lands i k) (H.incarnate.sym i k) (z:=curb s v) (e:=i-i) (B:=dart i k) (by unfold dart; omega) (by unfold dart; omega) (by omega)
    refine ((Spent.total _ (fun i p F=> ∑ k∈ f i,V i k p F) hu).add (Spent.total R _ hh)).cast ?_; intro p F hF hp; rw [lift_formula e p s v T hp]; change (∑ i'∈Finset.range (i+1),∑ k∈f i', V i' k p F) - V i r p F=_; rw [sum_range_succ,← add_sum_erase (f i) (fun k=> V i k p F) (Finset.mem_range.mpr (Nat.lt_succ_of_le he))]; abel
omit T hs hT hi
omit he in
lemma pass_formula (e:Parcel G)(p:Word)(s:Parcel.Step)(V:Sketch G)(v:Site s.L) (he':r≤M+i):
    let t:=M+4+i-r; let Q:= sink e.x (e.kickoff p s); let Z:=weigh e p s M v V; let P:= Transfer.pass e p s M v V; let U:= fun j φ=> coil (P φ) M j r; sail P i r=sail Z i r-∑ j∈Finset.range t,tickerMark Q (Catch.cap M) j t • U j := by
    intro t Q Z P U; funext φ; have hh: Uniform Q:= sink_mast _; have hf (j:ℕ): U j φ=presageMark Q (Catch.cap M) (coil (Z φ) M) j r:=by unfold U P coil; rw [show (shiftA _ (pass e p s M v V φ))=_ from reclip Q (F:=Z φ) hh]; exact near_houseMark Q _ _ hh -- check
    rw [Pi.sub_apply,Finset.sum_apply,show sail P _ _ _ = U t φ from (Pocket.current_coil _ _ he'|>.symm)]; simp_rw [Pi.smul_apply,hf]; rw [presage_eqMark,Pocket.current_coil _ _ he']
omit he
include T hT hs hi
lemma reset_meter (hn:n ≤ M+4+i) : Backs S (fun p=> tickerMark (sink e.x (e.kickoff p s)) (Catch.cap M) l n):= by
    let F p:= sink e.x (e.kickoff p s); let t:=M+4+i+1; have hh (j:ℕ)(hj:j<t): Backs S (fun p=> pin (F p) j):= by
       unfold F sink pin; simp_rw [PowerSeries.coeff_mk]; by_cases hz:j=0; · simp_rw [if_pos hz]; exact Backs.given 1
       simp only [if_neg hz]; exact e.mintBack T le_rfl _ ((works T (le_refl 3) hT j (by unfold t at hj; omega) 2).ofU s hs) -- ambiguity
    have he (j:ℕ)(hj:j<t): Backs S (fun p=> pin (Resetter.rotate (F p)) j):= Parcel.source_rotate hh j hj
    let A:= Catch.cap M; refine Parcel.source_m (U:=fun p=>Resetter.rotate (F p)^l) (F:=fun p=>rockW (F p) A) ?_ (Parcel.source_pow he l) _ (by unfold t; omega); exact Parcel.source_m hh (Parcel.source_pow (F:=fun p=> Resetter.rotate (F p)* F p) (Parcel.source_m he hh) A) -- remove unnecessary F
omit hi
lemma passport : ∀ i ≤ K,∀ r:ℕ, r ≤ M+i → let Q p F:= sail (Transfer.pass e p s M v F) i r; let U p F:= lead e p s v i r F;
    Spent D x ζ M Υ S (fun F t=> Harrier.Before Γ D x F i r t) (fun p F=>Q p F - U p F) ∧ Spent D x ζ M Υ S (fun F t=>Issued Γ D x F i r t) Q := by
    intro i; induction i using Nat.strongRecOn with|_ i ih=>
    intro hi r hr Q U; let A':= fun F b=> Harrier.Before Γ D x F i r b; suffices h:Spent D x ζ M Υ S A' (fun p F=> Q p F-U p F) from ⟨h, Spent.cast ((Spent.restrict h (H':=fun F t=> Issued Γ D x F i r t) (fun _ _ _ _ h=>h.1)).add (lead_bill (v:=v) T hs x hT hi hr)) (fun p F _ _=> (sub_add_cancel (Q p F) (U p F)).symm)⟩
    let w p:=sink e.x (e.kickoff p s); let t:=M+4+i-r; let y(j:ℕ)(p:Word)(F:Sketch G)(φ:Cards):= coil (pass e p s M v F φ) M j r; let f(j:ℕ)(p:Word)(F:Sketch G):= tickerMark (w p) (Catch.cap M) j t • y j p F;
    have he (j:ℕ)(hj:j<t) : Spent D x ζ M Υ S A' (y j):= by
       unfold y coil dazzle shiftA Catch.cap; split_ifs with hu he
       · let q:= j+r-2-(M+2); have h':q < i:= by unfold q; unfold t at hj; omega
         by_cases hQ:r ≤ M+q; · exact Spent.restrict (show Spent D x ζ M Υ S (fun F t=> Issued Γ D x F q r t) _ from (ih q h' (h'.le.trans hi) r hQ).2) (fun F _ b _ h=> Harrier.Before.earlier (l:=q) h (.inl h')) -- no q arg; inference
         exact Spent.cast Spent.zero (fun p F h hp=> funext fun φ=> ( (received T hp hs (v:=v) h).lineage φ).1.incarnate.thin q r (by omega))
       all_goals exact Spent.zero
    refine ((when_less (v:=v) T hs x hT hi hr).sub (Spent.total (Finset.range t) f (fun i h=> Spent.scale (y:=fun p=> tickerMark (w p) (Catch.cap M) i t) (he i (mem_range.mp h)) (reset_meter T hs hT hi (by unfold t; omega))))).cast fun p F h hp=>?_ ; rw [show Q p F=_ from pass_formula e p s F v hr]; abel -- x implicit not present
include hi
open PowerSeries
abbrev fid (e:Parcel G)(p:Word)(s:Parcel.Step)(h i r:ℕ) (F:Sketch G):= pay s h • ∑ v:Site s.L, lead e p s v i r F
omit T hT hi hs in
lemma sum_sail (U:X→Sketch G)(s:Finset X)(i n:ℕ) : sail (∑ i∈s,U i) i n=∑ j∈s,sail (U j) i n:= by funext φ; simp [sail]
include he
lemma port_health (h:ℕ): Spent D x ζ M Υ S (fun V b=> Issued Γ D x V i r b) (fun p V=> sail (Transfer.mean e p s M h V) i r) := (Spent.smul (Spent.total univ (fun v p F=> sail (Transfer.pass e p s M v F) i r) (fun v _=> (passport T hs x hT i hi r he).2)) (pay s h)).cast fun p F _ _=> by rw [Transfer.mean, show ∀ (b:ℝ)(K:Sketch G), sail (b • K) i r=b • sail K i r from fun _ _=>rfl, sum_sail]
lemma port_less (h:ℕ): Spent D x ζ M Υ S (fun V b=> Ω- V i r b) (fun p V=> sail (Transfer.mean e p s M h V) i r-fid e p s h i r V):= (Spent.smul (Spent.total univ (fun v p F=> sail (Transfer.pass e p s M v F) i r-lead e p s v i r F) (fun v _=> (passport T hs x hT i hi r he).1)) _).cast fun p F _ _=> by rw [fid,Transfer.mean, show ∀ (b:ℝ)(K:Sketch G), sail (b • K) i r=b • sail K i r from fun _ _=>rfl,sum_sail, Finset.sum_sub_distrib,smul_sub]
end Transfer
end
end YM.Contacts.Harrier
