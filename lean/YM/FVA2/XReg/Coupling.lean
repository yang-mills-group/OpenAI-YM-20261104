import YM.FVA2.Dframe.Bare
import YM.XSpace.Tamarack
/-!
# Realm algebra includes coupling registration at all arities, points & smearing

 Need exact pre-composition in the honest formal series before discarding divergences.
 Use MS public `substitute`: coupling `q` used in old coupling argument (new basis variable).
 Here following mechanism of Talking's `said` to identify as full FPS action.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Reg.Point
open Function Filter Set MeasureTheory Maxwell Maxwell.Free
open MS MS.Local.Physical MS.Menus MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival Dframe
open MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical Matrix
variable {n d k:ℕ}{G:Gauge}{B:Deck G}
local notation "Π"=> Press.portDeck G
local notation "ℒ"=> Normalize.Change G d
local notation "𝒮"=> XSpace.Structure1.Point G d n
local notation "μ"=> (PowerSeries.mk (R:=ℂ))
local notation "W"=> Fin n
variable (q:Cn)(S U:Guard G d)(V:ℕ→XSpace.Structure1.Point G d n)(v:Tags G d n)
-- at fixed test too.
abbrev story (V:ℕ→XSpace.Structure1.Point G d n)(v:Tags G d n):= μ (fun i=> V i v)
private lemma build (P:𝒮) (v:Tags G d n): P v=∑ i:W→Dime G d, (∏ j, (dime G d).repr (v j) (i j)) * P (fun j=> dime G d (i j)):= by
    have he:= P.map_sum (fun i (j:Dime G d)=> (dime G d).repr (v i) j • dime G d j); simpa only [Module.Basis.sum_repr, P.map_smul_univ,smul_eq_mul] using he -- may pattern
lemma estate : story (status S V) v= ∑ j:W→ Dime G d,( ∏ i,tax S (v i) (j i)) * story V (fun i=> dime G d (j i)):= PowerSeries.ext fun i=> by
    simp only [story,map_sum, Constants.admits, coeff_mk ]; rw [seen]; rw [Finset.sum_comm]; -- RHS only nested.s
    apply Finset.sum_congr rfl; intro j _; rw [build ( V (j none) ) (pulseU j S v)]; simp only [tax, coeff_mk]
lemma eternal : status U (status S V) = status (S*U) V:= by
    have he (v:Tags G d n) : story (status U (status S V)) v=story (status (S*U) V) v:= by
        rw [ estate, estate ]; -- issue Lean reduces?
        simp_rw [ estate,taxes, Fintype.prod_sum,Finset.mul_sum, Finset.sum_mul ]; -- taxes factor
        rw [Finset.sum_comm]; refine Finset.sum_congr rfl (fun i _=> Finset.sum_congr rfl (fun j _=>?_ )); rw [Finset.prod_mul_distrib]; -- ring
        ring
    ext1 i; ext1 p; simpa only [story, coeff_mk] using congr_arg (coeff i) (he p)
lemma home_v : status (1:Guard G d) V= V:= by
    -- directly tally uniquely f none=i and all packets some sites literal zero at positive.
    have he(j:Dime G d)(p:Sec G d): tax (1:Guard G d) p j=C ((dime G d).repr p j):= by
        refine PowerSeries.ext fun i=>?_; simp only [tax, coeff_mk,coeff_one, coeff_C]; split_ifs with hv; · subst i; rfl
        simp
    funext i; ext1 p; have h:= congr_arg (coeff i) (estate 1 V p); simp only [he, map_sum, ← map_prod, coeff_C_mul, story, coeff_mk ] at h; exact h.trans ( build _ p|>.symm )
-- subst as closed power series
lemma mk'_sub {q:Cn}(h:Rooted q)(p:Change.Ser) : μ (substitute q p) = (μ p).subst q:= by have he:= Constants.actual_subst (μ p) q h; simp_rw [coeff_mk] at he; exact he
lemma circle (f g:Cn) (hf:Rooted f)(hg:Rooted g): Rooted (f.subst g):= by unfold Rooted; rw [ ← Constants.actual_subst _ _ hg, coeff_mk,pay0 ]; exact hf
lemma moves {q:Cn}(h:Rooted q) : story (substitute q V) v= (story V v).subst q:= by unfold story; simp_rw [translate]; exact mk'_sub h _
lemma cycles (f g:Cn)(hf:Rooted f)(hg:Rooted g) : substitute g (substitute f V)=substitute (f.subst g) V:= by
    ext1 i; ext1 v; have h' (f:Cn)(hf:Rooted f): HasSubst (S:=ℂ) f:= HasSubst.of_constantCoeff_zero' (show constantCoeff f=0 from (coeff_zero_eq_constantCoeff_apply f).symm.trans hf)
    have he:story (substitute g (substitute f V)) v=(story V v).subst (f.subst g):= by rw [moves _ _ hg, moves _ _ hf]; exact PowerSeries.subst_comp_subst_apply (h' f hf) (h' g hg) _
    rw [ ← moves V v ( circle f g hf hg ) ] at he; simpa only [story, coeff_mk] using congr_arg (coeff i) he

-- integrate.Reports.L
lemma restT (R: Reports G d)(p: Test n): status S (fun i=> R i n p) k=realm S R k n p:= by ext1 u; rw [really,seen]
lemma seenT (R:Reports G d)(p:Test n) (t:Cn): substitute t (fun i=> R i n p) k= substitute t R k n p:= by rw [rules,rules]; simp only [ Finset.sum_apply, LinearMap.sum_apply, Pi.smul_apply, LinearMap.smul_apply ]
def stepV (q:Cn)(S:Guard G d): Guard G d:= PowerSeries.mk (substitute q (fun i=> coeff i S))
lemma horizon (p:Sec G d)(j:Dime G d)(h:Rooted q): tax (stepV q S) p j= (tax S p j).subst q:= by
    rw [← Constants.actual_subst _ _ h]; apply PowerSeries.ext; intro i; simp only [tax,stepV, coeff_mk,rules,LinearMap.sum_apply, LinearMap.smul_apply,map_sum,Finsupp.finsetSum_apply,map_smul,Finsupp.smul_apply]
-- covariance of realm under actual coupling formula
lemma resetP (h:Rooted q) : status (stepV q S) (substitute q V)= substitute q (status S V):= by
    have hs : HasSubst (S:=ℂ) q:= HasSubst.of_constantCoeff_zero' (a:=q) ((coeff_zero_eq_constantCoeff_apply _).symm.trans h)
    ext1 i; ext1 v; have he : story (status ( stepV q S ) (substitute q V)) v=story (substitute q (status S V)) v:= by
        rw [estate,moves _ _ h,estate]; simp_rw [moves _ _ h,horizon q S _ _ h, ← PowerSeries.coe_substAlgHom hs ]; rw [map_sum]; refine Finset.sum_congr rfl (fun j _=>?_); rw [map_mul,map_prod]
    obtain ht:= congr_arg (coeff i) he; simpa only [story,coeff_mk] using ht
lemma resetR (R:Reports G d) (h:Rooted q): realm (stepV q S) (substitute q R)=substitute q (realm S R):= by
    ext1 i; ext1 n; ext1 t; let P:ℕ→Point G d n:= fun i=> R i n t; rw [← restT, show (fun i':ℕ=> substitute q R i' n t)= substitute q P from funext (fun i'=> (seenT (k:=i') R t q).symm), ← seenT, resetP (V:= _) q (S:= S) h, show (fun i=> realm S R i n t)= status S P from funext (fun i=> (restT (k:=i) S R t).symm) ];
end YM.FVA2.Reg.Point
