import YM.FormalBulk08.Avenue.Creek
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Avenue
open Filter Set Metric MeasureTheory Function Lattice Laurent Bloch Exterior Precision RG Next.Free
open Stationary
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix
variable {n:Side}
open MSbar.Tree.Resolvent
variable {j:ℕ}{k:ℝ}
open Flat UVExtension.Free
variable {G:Gauge}
open Reef Mesa Gorge

variable {D l:ℕ}
open Kemp Pose Dawn Spigot Orb Wick Series Jets MeasureTheory Lotus Shore Lava Rift
variable {F:Anthem D G} -- auto D declaration
private lemma pasture (s v:Link G n)(h: Reef.force G n *ᵥ s= Reef.force G n*ᵥ v)(x:Face (Per n)):
    Work.F03.faceCurl x (Stationary.arm _ _ _ s)= Work.F03.faceCurl x (Stationary.arm _ _ _ v):= by ext a; rw [current,current,h]
private lemma bloom {l:List (Spigot.Path D G)}{η C:ℝ}{t:Loc G 1}{j u E:ℕ}{q:Herald}(p:Studio D)(h:∀ a∈ l,Merit q t a j u E η C)(hs:0<η)(s v:Link G n)(hx: Reef.force G n*ᵥ s=Reef.force G n*ᵥ v): traceP s (PowerSeries.coeff 0 (terms l p n))=traceP v (PowerSeries.coeff 0 (terms l p n)):= by
   induction l with
   | nil=> simp [terms,traceP]
   | cons a l ih=>
       let M:=a.cabin
       have he:= h a (List.mem_cons_self ..); have hp:=he.income
       have hL:PowerSeries.coeff 0 (terms (a::l) p n)=PowerSeries.coeff 0 (cradle a.grade M p n)+PowerSeries.coeff 0 (terms l p n):= map_add ..
       have hA : traceP s (PowerSeries.coeff 0 (cradle a.grade M p n))=traceP v (PowerSeries.coeff 0 (cradle a.grade M p n)):= by
           by_cases hv:a.grade=0; swap
           · simp only [cradle, PowerSeries.coeff_X_pow_mul',show ¬a.grade≤0 from (by omega), ↓reduceIte]; simp [traceP]
           rw [hv,cradle,pow_zero,one_mul,after_one,Nat.add_zero,← (canon_gain hp hs p s a.rank).tsum_eq,←(canon_gain hp hs p v a.rank).tsum_eq]; apply tsum_congr; intro i; simp_rw [springPin,pasture s v hx]
       have ht:= ih (fun i hi=>h i (List.mem_cons_of_mem _ hi));rw [hL]; unfold traceP; rw [map_add,map_add]; exact (show _+_= _+_ from congr_arg₂ (·+·) hA ht) -- traceP reduce
private lemma lull (F:Anthem D G){o:Loc G 1}(h:Wade o F l):∃ η C:ℝ,0<η ∧ Woodsy o η C 0 F:= by
   let I:=Fin (l+1); choose v C hv hC H using fun i:I=>h.2.2 0 i.val
   obtain ⟨p,m,hp⟩:= Finset.exists_min_image Finset.univ v Finset.univ_nonempty; refine ⟨v p,∑ i:I,C i,hv p,Finset.sum_nonneg fun i _=> hC i,fun e he r x=>?_⟩
   rw [show e=0 by omega]; by_cases hx:r<l+1
   · let i:I:=⟨r,hx⟩; exact (penn_shrink (H i x) (hp i (Finset.mem_univ i))).mono (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun i _=> hC i) (Finset.mem_univ i)) (norm_nonneg _))
   rw [show F x 0 r=0 from Classical.byContradiction (fun hh=>by have hv:=h.1 x 0 r hh; unfold Yield at hv; omega)]; exact (Knox_zeros _).mono (mul_nonneg (Finset.sum_nonneg fun i _=> hC i) (norm_nonneg _))

def Matters (p:Pce (wire G n)) :Prop:= ∀ x y : Link G n,Reef.force G n*ᵥ x= Reef.force G n*ᵥ y → traceP x p=traceP y p
lemma Glyph.matters (o:Loc G 1)(p:Studio D)(h:Glyph o F l 0): Matters (PowerSeries.coeff 0 (Kemp.banner l (F p) n)):= by
   obtain ⟨η,C,hη,H⟩:=lull F h.summary; obtain ⟨ξ,K,hx,hk,I⟩:= ignited herald o l 0 0 D hη; obtain ⟨M,hm⟩:= I F _ H h; rw [← lit_sum hm hx p n 0 (Nat.zero_le _)]; exact bloom p hm.origin hx
section forwards
lemma through_curl (z:Site n)(x: Link G n)(a:Lines G n 2) : (Reef.force G n*ᵥ (x ∘ Lotus.tint z)) a=(Reef.force G n*ᵥ x) (Lotus.tint z a):= by
    obtain ⟨y,d,i⟩:= a; obtain ⟨d,rfl⟩:=plaqEquiv.surjective d; change (Reef.force G n *ᵥ (x ∘ Lotus.tint z)) (y, plaquette d, i)=(Reef.force _ _ *ᵥ _) (y+z, plaquette d,i);rw [show ∀ b, (Reef.force G n*ᵥ b) (y,plaquette d,i)=_ from fun b=>(current b (y,d) i).symm]; rw [←show Work.F03.faceCurl (y+z,d) _ i=(Reef.force _ _ *ᵥ x) _ from current ..]
    let f:= x∘ Lotus.tint z; change Work.F03.faceCurl (y,d) (Stationary.arm _ _ _ f) i= Work.F03.faceCurl (y+z,d) (Stationary.arm _ _ _ x) i
    rw [Work.F03.faceCurl, Work.F03.faceCurl,←Exterior.fundamental,←Exterior.fundamental, YM.AnalyticBridge.VerifiedReset.Square.cochain_square,YM.AnalyticBridge.VerifiedReset.Square.cochain_square]; unfold Exterior.collect; simp [Stationary.arm_apply,f,Lotus.tint,add_right_comm]
lemma materia (o:Loc G 1)(z:Cover)(p:Studio D)(h:Glyph o F l 0): Matters (PowerSeries.coeff 0 (Kemp.banner l (work z (F p)) n)):= by
   rw [seated z (F p) l n (h.summary.1 p) (h.summary.2.1 p),resite,PowerSeries.coeff_map]; intro a b he; unfold traceP; simp_rw [AlgHom.toRingHom_eq_coe,RingHom.coe_coe,MvPolynomial.aeval_rename]; apply Glyph.matters o p h; funext i; rw [through_curl,through_curl,he]
lemma crest_real (v:Train j)(hk:0<k): (bandR G v k n).IsSymm:= by change _ᵀ= _; unfold bandR; rw [← patron_star,cargo_sym _ _ hk]
lemma imprints {p:Pce (wire G n)}(hk:0<k)(v:Train j)(hj:4≤j)(h: Matters p) :∃ q:Pce (Lines G n 2), p=mixRows (Reef.force G n) q:= by
   let S:=kernelP G k v n; let M:=bandR G v k n; let D:=Reef.force G n
   have he:D*(M*S)=D:= by
       have ht:= congr_arg Matrix.transpose (invite v (n:=n) (G:=G) hk hj); rwa [Matrix.transpose_mul,Matrix.transpose_mul,Matrix.transpose_transpose, show (bandR G v k n)ᵀ=M from crest_real v hk, kernel_color _ hk hj] at ht
   let W:=patron G ((pink k v).acts n);have hv:S=Dᵀ*W*D:= by unfold S W D; rw [kernelP,Precision.K,patron_mul,patron_mul,patron_star];rfl
   refine ⟨mixRows (M*(Dᵀ*W)) p,?_⟩; rw [mix_budget,Matrix.mul_assoc,←hv]; apply orbit_ext; intro x; rw [mix_eats]; refine h _ _ ?_; rw [Matrix.mulVec_mulVec,show Reef.force G n=D from rfl,he]
end forwards
end YM.FormalBulk08.Avenue
