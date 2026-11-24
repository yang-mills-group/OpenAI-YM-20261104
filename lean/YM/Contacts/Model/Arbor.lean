import YM.Contacts.Model.Oak
/-! Recover small-f price on the aggregate jets, despite lack of budget on simultaneous values at different periods. Symbols before flags. -/
noncomputable section
namespace YM.Contacts.Model
open Function Lattice Finset Filter Set PhysicalNext.Repeat Pressure Wilson MeasureTheory RG
open Slide (Stars)
open Trio (froth Mirrors Offer)
open AnalyticBridge VerifiedReset Push.AbsoluteSums Animals YM.Stationary Milling PertExtension.Series Exterior Precision Ion
open Pulse Spine Garf Steam Bloch Radial House Lumen Metric Push.Uniform Kale
open scoped Topology NNReal InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{n m c:Side}{k w r z ℓ i j:ℕ}
namespace Arbor
-- analytic near true gauges. Link s volume substitution via path budget only, no dimension prices creeping to β powers through powers of tapes.
open Lintel.Plata ConnectedActivityE6 Push.SectorMeasure
variable {Υ C A Λ H t R D I O Z:ℝ}{S:ℝ≥0}{X:G.ColorIndex}{P:Bed}
variable {E : Type}[NormedAddCommGroup E][NormedSpace ℝ E]{U:E → Config G m}{u:E}
lemma acorn (a:Site m)(hk:m.val≤k): (Kale.walk a).length≤4*k:= by
   rw [Kale.walk, Stationary.route_length,sub_zero]; refine (sum_le_sum (g:=fun i=>k) (s:=univ) (fun i _=>?_)).trans ?_
   · have hx:= lift_centers a i; omega
   simp [Axis]
private abbrev myLog (G:Gauge)(k:ℕ)(a:ℝ):= ∀ u:G.El,G.chord u≤ Kale.charHeight G → Allows k G.plog (G.mat u) a
lemma logwrap (G:Gauge)(k:ℕ): ∃ a:ℝ,0≤a ∧ myLog G k a:= by
   let s:= {x:G.El| G.chord x≤ Kale.charHeight G}; have hx:IsCompact s := (isClosed_le G.continuous_chord continuous_const).isCompact; have hp:= Kale.guardChar G; obtain ⟨p,hp,H⟩:= exists_allows (f:=G.plog) (hx.image G.continuous_mat) (fun _ hu=> (by obtain ⟨u,hu,rfl⟩:= hu; exact hp.patch _ (le_trans (show G.chord u≤_ from hu) (le_mul_of_one_le_left hp.down.le (by norm_num))))) k; exact ⟨p,hp,fun i h=> H _ ⟨i,h,rfl⟩⟩
def Logprice (G: Gauge)(k:ℕ) := (logwrap G k).choose
def arborPrice (G:Gauge)(a:ℕ)(k:ℕ)(B:ℝ) :=
   let v:= travelCost G k (4*a) B
   2^k*(2^k*v*B)*v
lemma allowance (h:∀ i,Allows k (fun x=>G.mat (U x i)) u Z) (w:ℕ)(hq:m.val≤w)(x: Bond m): Allows k (fun x'=>G.mat (alive (U x') x)) u (arborPrice G w k Z):= by
    have hh (x:Site m): Allows k (fun x'=> G.mat (bring (U x') x)) u (travelCost G k (4*w) Z):= travel_jets h 0 (acorn x hq)
    exact (((hh x.1).times (h x)).times ((hh _).inverse)) -- unif may timeout.M.M
omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma inn (h:∀ i,G.chord (U u i) ≤ Z) (w:ℕ)(hq:m.val≤w)(x: Bond m): G.chord (alive (U u) x) ≤(2*(4*(w:ℝ))+1)*Z:= by
    have he (v:Site m) : G.chord (bring (U u) v)≤4*(w:ℝ)*Z:= by
       refine (Next.Fluctuations.travel_chord _ (Kale.walk v) 0 _ h).trans ?_; gcongr; · exact (G.chord_nonneg _).trans (h x)
       exact_mod_cast acorn v hq
    let g:=Kale.bring (U u); let v:=g x.1; let s:= x.1+step x.2; apply (G.chord_triangle _ (g s)⁻¹).trans; rw [G.chord_inv]; apply ((add_le_add (add_le_add (he x.1) (h x)|>.trans' (G.chord_triangle ..)) (he s))).trans; exact le_of_eq (by ring)
lemma revive (h:∀ i,Allows k (fun x => G.mat (U x i)) u Z) (he : ∀ i,G.chord (U u i)< Kale.charHeight G) : Allows k (bevel m ∘ U) u (composeCost k (Logprice G k) Z):= by
    let C:=Logprice G k; let v:=composeCost k C Z; have hh (i:Bond m): Allows k (fun y=>cutLog Chi.canonical (Kale.charHeight G) (U y i)) u v:= by
       have hp : ContinuousAt (fun y=>U y i) u:= (G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.continuousAt_iff.mpr (h i).analytic.continuousAt
       have hh := ((G.continuous_chord.continuousAt.comp hp).eventually (gt_mem_nhds (he i))); refine (((logwrap G k).choose_spec.2 _ (he i).le).comp (f:=fun z=> G.mat (U z i)) (h i)).germ (hh.mono fun i h=> ((Kale.guardChar G).kept _ _ h.le).symm)
    have hp:0≤ v:=(hh (Classical.arbitrary _)).nonneg
    apply allows_pi hp; intro i; rcases i with ⟨x,y,t⟩; let e: Bond m:= (x,axisEquiv.symm y); let L:= PiLp.proj (𝕜:=ℝ) 2 (fun _:G.ColorIndex=>ℝ) t
    refine ((hh e).linear L ?_).mono (show (1:ℝ)*v ≤ v from (one_mul _).le); apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro s; rw [one_mul]; 
    simpa only [L, PiLp.proj_apply,Real.norm_eq_abs,EuclideanSpace.basisFun_inner, OrthonormalBasis.norm_eq_one, one_mul] using (abs_real_inner_le_norm (EuclideanSpace.basisFun G.ColorIndex ℝ t) s)
lemma guards {α:Type}[Fintype α]{r:ℕ}{F:Field (Fin (r+1)) α}{l:Pulse.Range α}{f:E→ House.Dir α}(h:Allows k f u Z)(hr:Rooted l F C): Allows k (design F ∘ f) u (((Fintype.card α:ℝ)^(r+1))* C*(1+ |2^k * Z|)^(r+1)):= by
   letI : DecidableEq (Fin (r+1)):= fun _ _=> Classical.propDecidable _; have he (i:α): Allows k (fun x=> f x i) u Z:= ((h.linear (ContinuousLinearMap.proj i) (ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x=> by rw [one_mul]; exact norm_le_pi_norm x i)))).mono ((one_mul Z).le) -- lemma
   let g(s:ℕ):ℝ:=(1+|2^k * Z|)^s; have hx (p:Fin (r+1)→α)(s:Finset (Fin (r+1))): Allows k (fun x=>∏ i∈s,f x (p i)) u (g s.card):= by
      induction s using Finset.induction with | empty=> simp only [Finset.prod_empty,Finset.card_empty,g,pow_zero]; exact allows_const _ norm_one.le | insert i s hi ih=>
      simp_rw [Finset.prod_insert hi,card_insert_of_notMem hi]; refine (Allows.bilinear (ContinuousLinearMap.mul ℝ ℝ) (he _) ih (ContinuousLinearMap.opNorm_mul_le ℝ ℝ)).mono ?_; rw [mul_one]; unfold g; rw [pow_succ,mul_comm _ (1+|2^k * Z|)]; apply mul_le_mul_of_nonneg_right (le_trans (le_abs_self _) (le_add_of_nonneg_left zero_le_one)) (by positivity)
   have ht p:=hx p univ
   have hr (p:Fin (r+1)→α): Allows k (fun x=> F p*∏ i,f x (p i)) u (C*g (r+1)):= ((ht p).smul (F p)).mono (by rw [card_univ,Fintype.card_fin]; exact mul_le_mul_of_nonneg_right (hr.bound p 0) (by unfold g; positivity))
   unfold Function.comp; simp_rw [design_spec]; refine (allows_sum (s:=univ) (fun i _=> hr i)).mono ?_; rw [sum_const,nsmul_eq_mul,card_univ]; simp [g,mul_assoc]
private def viz (G:Gauge) (v:ℕ)(k a w:ℕ)(r:ℝ) := ((v:ℝ)^4*(Fintype.card (Loc G 1):ℝ))^w * (1+|2^k*composeCost k (Logprice G k) (arborPrice G a k r)|)^w
-- pad rank zero. cost syntax
-- assumption h∈ smooth not needed.def of compact `artP`
def arcPrice (G:Gauge) (v:ℕ)(k w:ℕ)(r t:ℝ):= t*∑ j∈Finset.range w,viz G v k v j r
variable {v:ℕ}
lemma vizPrice (W:bore G)(h:Aegis X W P)(hG:G.Simple)(hp:Tills (z+3) S C W)(hv:m.val≤v)(he: i< z+3)
    (hy:∀ e,Allows k (fun x => G.mat (U x e)) u Z)(hz:∀ e,G.chord (U u e) ≤ t) (hs:(2* (4*(v:ℝ))+1)*t < Kale.charHeight G) : Allows k (Kale.fire (wind (hair W m) (z+3) i) ∘ U) u (arcPrice G v k (z+3) Z C):= by
   let a:=fun z=>alive (U z); let b:=fun z=>bevel m (a z); let β:= composeCost k (Logprice G k) (arborPrice G v k Z); have hβ: Allows k b u β:= revive (U:=a) (allowance hy v hv) (fun i=> lt_of_le_of_lt (inn hz v hv i) hs); let A r:= viz G v k v r Z; have hx r:0≤C*A r:=mul_nonneg hp.nonneg (by unfold A viz; positivity); unfold Kale.fire wind Function.comp arcPrice
   erw [mul_sum]; refine (allows_sum (s:=Finset.range (z+3-i)) (f:=fun j x=>grate (hair W m) i j (b x)) (C:=fun j=> C*A j) (fun j hj=>?_)).mono (sum_le_sum_of_subset_of_nonneg (range_mono (Nat.sub_le _ _)) (fun i _ _=> hx _));
   unfold grate; split; swap; · exact allows_const _ ((norm_zero (E:=ℝ)).trans_le (hx j))
   rename_i hh; have hf:= mem_range.mp hj; cases j with
   | zero=> rw [Lintel.Plata.hair_quiet h m hG _ 0 (by omega)]; simp_rw [Forge.parcel_nil]; exact allows_const _ ((norm_zero (E:=ℝ)).trans_le (hx 0))
   | succ r=>
    let x:= W (i+(r+1)-2) (r+1); let y:= z; have he k: Mirrored (backpack k) x:= (should h.blazing).my.here k _ _
    have hg:= (guards (α:=Co m (Loc G 1)) hβ (l:=Pulse.Range.cheap _) (Shadow.cost (printFeeds (heritage he m)) (hp.cap (i+(r+1)-2) (r+1) (by omega) (by omega)) ?_ (lower_onto m)))
    rotate_left; -- ? tactic order
    · exact fun u=> show (Pulse.Range.cheap _).bill _ ≤ _ from (by simp [Range.cheap,Range.bill,Range.height]) -- fix
    refine hg.mono ?_; unfold A viz; rw [mul_left_comm C,←mul_assoc (_^(r+1))]; -- multiplier reordered? 
    have hQ: (Fintype.card (Co m (Loc G 1)):ℝ) ≤ (v:ℝ)^4*Fintype.card (Loc G 1):= by simp [Co,Lattice.Site,Lattice.Per,Four,Axis]; gcongr
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hQ _) hp.nonneg) (by positivity)
end Arbor
end YM.Contacts.Model
