import YM.RG05Readout.Flatten.Local
/-! Amass from one-per-root at b, pay Berry. Zero roots outside fit;
 geometry requires b paying some fixed costs independent of mesh n.Close
 support applies to actual test of signed family, including counter
 loaded at PIE precision even in T.UK. Normalizations explicit.Center
 measure per root with units restoration reserved for Cluster.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Flatten
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Cells Overlay
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons
open Records Basket Shadow
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}{I J V:Type}[DecidableEq V][Fintype V]
    {j b k D:ℕ}
set_option quotPrecheck false
local notation "t!"=> (1,false)
local notation "A"=> C.S.a
local notation "Λ"=> C.S.toDepth
local notation "X!"=> C.side N p
local notation "Y!"=> C.side b p
local notation "s!"=> n+1
local notation "P"=> C.side (n+1) p
local notation "ρ₀"=>C.S.radius p
open GridApprox
abbrev Silent (d:ℕ){Z:Side}(F:Bin G Z) := ∀ f:Body, Cap (d+2) f 0 → F f=0 -- implicit
lemma precinct_null (v:Palette C d): Silent d (precinct C p N d v):= fun _ h=>unlit _ _ _ _ _ h
lemma stay (ht:m≤ N)(F:Bin G (C.side N p))(hF:Silent d F)(hy:i≤ m) : Silent d (crops C m p N d ht F i hy) :=by
   intro f h; rw [awaken]; let r:=(Λ hy p); apply Finset.sum_eq_zero; intro t _; have htP : Cap (d+2) (feeR r t f) 0:= cap_aff _ (by positivity) (inv_le_one_of_one_le₀ (by exact_mod_cast r.count.property)) (mapsR r (C.S.toDepth_odd hy p) t) h
   have hw:= hF _ htP; rw [hw]; let y:=(Λ ht p).embed (r.assemble (0,t)); change ratioX r d • stepUp t! y 0=_; rw [show stepUp t! y (0: Goods G _)=0 from rfl,smul_zero]
lemma quiet {M:ℝ} (T:PulseC)(hT:Priced d T M)(hm:n+1 ≤ N)(v:Palette C d)(f:Goods G (C.side N p)): Silent d (rebirth C d n p N hm T v f):=by
    intro s hs; unfold rebirth; rw [stay (le_refl N) (precinct C p N d v) (precinct_null v) hm _ hs, show T s=0 from norm_le_zero_iff.mp (by have h:= hT s 0 hs; simpa using h),sub_zero,zero_smul] -- edit
variable (hr:j ≤ b) (hm:m ≤ N) {Z:ℕ} {M R:ℝ}
variable (X:Bin G (C.side N p))(hX:Silent d X) (f:Body) (hf: ∀ x∈tsupport f.val, ‖x‖≤R)
-- here ordering calibrated.T
noncomputable def gathered (C:Family G)(m N p d:ℕ)(hm:m≤N)(X:Bin G (C.side N p))(b:ℕ)(f:Body): Goods G (C.side N p):= ∑ z:Site (C.side b p), uniform C m p N d hm X b z (1,false) (restricted C b p z f)
include hX hf
lemma mass (he:b ≤ m) (hR : R+A b*3 < ρ₀): gathered C m N p d hm X b f= ∑ y:Site (C.side m p), ratioX (Λ he p) d • stepUp t! ((Λ hm p).embed y) (X (restricted C m p y f)):=by
   let r:= Λ he p
   unfold gathered; simp_rw [lift_pol hm X he]
   rw [← Equiv.sum_comp r.splitSites.symm,Fintype.sum_prod_type]; refine sum_congr rfl fun z _=> sum_congr rfl fun i _=> ?_; let y:=r.assemble (z,i); obtain h|⟨a,b'⟩:=linkR he f hf hR y (d+2)
   · rw [show r.parent y=z from r.assemble_parent _,show r.residue y=i from r.assemble_res _] at h
     change ratioX r d • stepUp t! _ (X (feeR r i (restricted C b p z f)))=ratioX r d • stepUp t! _ (X (restricted C m p y f)); rw [h]; rfl
   rw [show r.parent y=z from r.assemble_parent _,show r.residue y=i from r.assemble_res _] at a
   change ratioX r d • stepUp t! _ (X (feeR r i (restricted C b p z f)))=ratioX r d • stepUp t! _ (X (restricted C m p y f)); rw [hX _ a,hX _ b']; rfl
omit hX hf
local notation "α"=> Λ hr p
abbrev XHosts (h:j ≤ b):Finset (Site Y!):=Finset.univ.filter (fun z=>separation z 0≤ (C.S.toDepth h p).count.val/4)
include hX hf
local notation "W!"=> XHosts (C:=C) (p:=p) hr
lemma outside (hp:R+A b≤ A j/4)(z:Site (C.side b p))(hz:z∉ XHosts (C:=C) (p:=p) hr)(he:b ≤ m): uniform C m p N d hm X b z t! (restricted C b p z f)=0:=by
    unfold uniform; rw [dif_pos he, stay hm _ hX _ _ (remote hr f hf hp z (fun h' => hz (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h'⟩)) _)]; rfl
lemma remove (hp:R+A b ≤ A j / 4)(he:b ≤ m): gathered C m N p d hm X b f= ∑ z∈ W!, uniform C m p N d hm X b z t! (restricted C b p z f) := (sum_subset (subset_univ _) fun z _ hv => outside hr hm X hX f hf hp z hv he).symm
omit hX hf
lemma root_count : (W!).card ≤ (C.S.toDepth hr p).count.val^4:=by
    let r:=(Λ hr p); have ht(z)(hz:z∈(W!)): r.parent z=0:=by
       refine owner r z 0 ?_; have hh:separation z 0 ≤ r.count.val/4:=(Finset.mem_filter.mp hz).2; rw [show r.embed 0=0 from r.root.map_zero]
       have hg:0<r.count.val:=r.count.property; omega
    have hx (z)(hz:z∈(W!)): (α).assemble (0,(α).residue z)=z:=by rw [←show r.parent z=0 from ht z hz]; exact r.unpack_at z
    have h: Set.InjOn (r.residue) W!:= fun i hi a ha he=> (hx i hi).symm.trans ((congr_arg (fun i=>r.assemble (0,i)) he).trans (hx a ha)); rw [← site_card (α).count]; exact (card_image_of_injOn (f:=r.residue) (s:=W!) h).ge.trans (Finset.card_le_univ _)
include hX hf
lemma valueSum (hp:R+A b ≤ A j / 4)(he:b ≤ m)(h:C.Makes)(hM:0≤ M)
   (hw:∀ z∈W!, let T:=tilesAt C.S p ((hr.trans he).trans hm); let V' := uniform C m p N d hm X b z t! (restricted C b p z f); Interior (T.chamber 0) V' ∧ T.rootTest (C.beta N p) V' ≤M):
   let T:=tilesAt C.S p ((hr.trans he).trans hm);
   Interior (T.chamber 0) (gathered C m N p d hm X b f)∧ T.rootTest (C.beta N p) (gathered C m N p d hm X b f) ≤ ((A j)/(A b))^4 * M:=by
     intro T; let Y z:= uniform C m p N d hm X b z t! (restricted C b p z f); let u:=C.beta N p
     rw [remove hr hm X hX f hf hp he]; obtain ⟨hP,hC⟩:= Next.Extract.rooted T u (seamless h ..) (W!) Y (fun _=>1) (fun i hi=> (hw i hi).1); simp only [one_smul,norm_one,one_mul] at hP hC; refine ⟨hP,hC.trans ((sum_le_sum (g:=fun _=>M) (fun i hi=> (hw i hi).2)).trans ?_)⟩
     rw [sum_const,nsmul_eq_mul]; apply mul_le_mul_of_nonneg_right _ hM; have hp:(A j)/(A b)=(α).count.val:=(div_eq_iff (C.S.a_pos _).ne').mpr ((C.S.embeds_scale _).symm.trans (mul_comm ..)); rw [hp]; exact_mod_cast root_count (C:=C) (p:=p) hr
end YM.RG05Readout.Flatten
