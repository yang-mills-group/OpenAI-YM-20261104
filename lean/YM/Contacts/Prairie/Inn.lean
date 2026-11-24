import YM.Contacts.Prairie.Pear
namespace YM.Contacts.Prairie
open Function Set Finset Filter RG Wilson Lattice Precision Exterior Push.AbsoluteSums Extra.Iteration
open Bloch Milling Milling.Steam Pulse Spine MergeProof Milling.Forge Laurent Stationary Matrix Work.F08
open Milling.Garf Form House PertExtension.Series Tree Larch FreeResolvent PhysicalNext.RankCovariance
open Next.Free Milling.Lumen Barrage.Reserve
open scoped Topology BigOperators Matrix Classical NNReal ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G: Gauge}
namespace Parcel
open Origin Barrage.Slope Ion Resetter
variable (e:Parcel G) (p q u:Word) (s:Step) (n:Side) {i j:ℕ} {ζ:ℝ≥0}{b:ℝ}
variable { S:Boom}{r k:ℕ}
abbrev dust := e.port p - flare G
structure Works {S:Boom}{ζ:ℝ≥0}(e:Parcel G)(k i r:ℕ):Prop where
   ofPort : Fleet S (bath ζ k _) (fun p=> e.port p i r)
   ofU (s:Step)(hs:s∈S): Fleet S (bath ζ k _) (fun p=> e.kickoff p s i r)
def Last (k i r:ℕ):Prop:= ∀ v w,Oasis.Past i r v w → Works (S:=S) (ζ:=ζ) e k v w
lemma flare_q ( S:Boom)(ζ:ℝ≥0)(k i r:ℕ): Fleet S (bath ζ k _) (fun (_ : Word)=> flare G i r):= by exact Fleet.given (expand_fee (s:=ζ+1) (by simp) ((flare_purse ..).shelter i r))
variable {e} (T:e.License S ζ)
include T
lemma housed (h:OK S p) : Oasis.Amount e.x (e.port p) Oasis.normK := by -- add h
   obtain ⟨s,hs,u,hU⟩:= (T.prosper h).price; let W:= (T.prosper h); exact ⟨should W.blazing,W.price,fun i=>by unfold Oasis.normK; split; subst i; exact stark_cash hs (e.floor p 1).starts W.blazing hU (e.whole p) (e.symmetry _) e.x; apply W.honor; omega⟩
lemma stays_nil (h:OK S p): Oasis.Amount e.x (e.dust p) 0:= by simpa only [dust,sub_self,origin] using (housed p T h).minus (housed [] T OK.nil)
lemma kEra (k:ℕ): Fleet S (bath ζ k _) (fun p=> kin G (e.column p).metric 2):= by
   refine T.pa (X:=Dye G) k ⟨?_,?_⟩
   · let C p:= (kin_desc (G:=G) 1 (e.column p).metric (e.whole _) (e.K_funds p) e.K_pos T.warm 2).ground; exact ⟨_,(C []).cash,fun p _=> C p⟩
   refine ⟨_,mul_nonneg (mul_nonneg (by exact norm_nonneg ((2:ℝ)⁻¹)) (Nat.cast_nonneg (Fintype.card (Breed 1 (Dye G))))) e.gift_pos,fun p q u _ _ h=>?_⟩; let A(x:Word):=e.column (u++x); let μ:=e.shop*mileage u; have h': 0 ≤ μ:=mul_nonneg e.gift_pos (mileage_pos _).le; have hD : 2*( (2*ζ:ℝ≥0):ℝ) ≤ e.decade:= by push_cast; have ht:=NNReal.coe_le_coe.mpr T.lane; push_cast at ht; linarith only [ht]
   convert Oasis.kin_diff (G:=G) (t:=2*ζ) (F:=A p) (U:=A q) (e.Q_strip p q u _ T.ok h) h' hD using 1; ring
variable {p}
lemma old (h:OK S p): e.port p 0 2 = kin G (e.column p).metric 2:= by obtain ⟨s,-,M,hM⟩:= (T.prosper h).price; exact east (T.prosper h).blazing (hM.shelter 0 2) (e.whole _)
lemma old_fee (k:ℕ)(h:OK S p): Rooted (bath ζ k _) (e.port p 0 2) (share e.T G e.J k):= by
   rw [old T h]; refine ((sheet e.T G e.J k).choose_spec.2 _ (e.toll p)).weaken (fun t=> monoTerrace le_rfl ?_ t) le_rfl; have ht:=NNReal.coe_le_coe.mpr T.lane; apply NNReal.coe_le_coe.mp; push_cast at *; unfold decade at ht; linarith only [ht, NNReal.coe_nonneg ζ] -- arg
lemma roots (k:ℕ): Works (S:=S) (ζ:=ζ) e k 0 2:= ⟨Holds.eq (kEra T k) fun _ h=> (old T h).symm,fun s hs=> Holds.eq (Fleet.next (kEra T k) s hs) fun _ _=>rfl⟩
lemma finished (h:i=0 ∧ r≠2 ∨ r<2 ∨ i+2<r) : Works (S:=S) (ζ:=ζ) e k i r:= by
    by_cases hr:r<2; swap
    · refine ⟨Holds.eq Fleet.fzero ?_,fun s hs=> Holds.eq Fleet.fzero ?_⟩; exact fun p hp=> ((T.prosper hp).blazing.frame.thin _ _ (.inr (by omega))).symm; intro p hp; obtain ⟨_,-,he⟩:= T.signal hp hs; exact (he.frame.thin _ _ (.inr (by omega))).symm
    interval_cases r; exact ⟨Fleet.empty,fun s _=> Fleet.empty⟩; refine ⟨Holds.eq Fleet.fzero ?_,fun s hs=> Holds.eq Fleet.fzero ?_⟩; intro p hp; obtain ⟨a,Sha,U⟩:= T.banks hp; exact (rank_one e.simple (should a.blazing) U i).symm; intro p hp; obtain ⟨a,h,Q⟩:= T.signal hp hs; exact (rank_one e.simple (should Q) h i).symm
end Parcel
end
end YM.Contacts.Prairie
